#!/usr/bin/env python3
"""
proof_engine.py: explore the space of Lean 4 proofs.

Architecture
  Proposer  : suggests next tactics (fixed tactic list, an LLM, or both)
  Verifier  : the Lean REPL. It is the only judge of correctness.
  Search    : best-first over proof states, deduplicated by goal text
  Blueprint : a tree of target theorems. When a target resists, an LLM
              proposes intermediate lemmas, which become new targets.
              Proved lemmas are added to the environment for later targets.
  Log       : every attempted step is appended to explore.jsonl

Nothing is accepted unless the final, assembled proof re-checks in Lean
with no errors and no `sorry`.
"""
from __future__ import annotations

import argparse
import heapq
import itertools
import json
import os
import queue
import re
import subprocess
import threading
import time
from dataclasses import dataclass, field
from pathlib import Path

BANNED = re.compile(r"\b(sorry|admit|native_decide)\b|^\s*axiom\b", re.M)


# --------------------------------------------------------------------------
# Lean REPL driver (https://github.com/leanprover-community/repl)
# --------------------------------------------------------------------------

class LeanTimeout(Exception):
    pass


class ReplRestarted(Exception):
    pass


class LeanRepl:
    """Talks JSON to the Lean REPL. Each request and response ends with a blank line."""

    def __init__(self, cmd: list[str], cwd: str, timeout: float = 60.0):
        self.cmd, self.cwd, self.timeout = cmd, cwd, timeout
        self.generation = 0  # bumped on restart: all env / proofState ids become invalid
        self._start()

    def _start(self):
        self.proc = subprocess.Popen(
            self.cmd, cwd=self.cwd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
            stderr=subprocess.DEVNULL, text=True, bufsize=1)
        self.q: queue.Queue = queue.Queue()
        threading.Thread(target=self._reader, args=(self.proc, self.q), daemon=True).start()

    @staticmethod
    def _reader(proc, q):
        for line in proc.stdout:
            q.put(line)
        q.put(None)

    def restart(self):
        try:
            self.proc.kill()
        except Exception:
            pass
        self._start()
        self.generation += 1

    def send(self, obj: dict, timeout: float | None = None) -> dict:
        timeout = timeout or self.timeout
        self.proc.stdin.write(json.dumps(obj) + "\n\n")
        self.proc.stdin.flush()
        buf: list[str] = []
        deadline = time.time() + timeout
        while True:
            remaining = deadline - time.time()
            if remaining <= 0:
                self.restart()
                raise LeanTimeout(str(obj)[:200])
            try:
                line = self.q.get(timeout=remaining)
            except queue.Empty:
                continue
            if line is None:
                self.restart()
                raise ReplRestarted("Lean REPL exited")
            if line.strip():
                buf.append(line)
            elif buf:
                try:
                    return json.loads("".join(buf))
                except json.JSONDecodeError:
                    continue


def lean_errors(resp: dict) -> list[str]:
    errs = [m.get("data", "") for m in resp.get("messages", []) if m.get("severity") == "error"]
    if "message" in resp and "proofState" not in resp and "env" not in resp:
        errs.append(resp["message"])
    return errs


def try_this(resp: dict) -> str | None:
    """Turn `exact?` / `apply?` / `aesop?` output into the concrete tactic it found."""
    for m in resp.get("messages", []):
        d = m.get("data", "")
        if d.startswith("Try this:"):
            return d[len("Try this:"):].strip()
    return None


# --------------------------------------------------------------------------
# Proposers
# --------------------------------------------------------------------------

STATIC_TACTICS = [
    "rfl", "trivial", "decide", "grind", "simp_arith", "norm_num", "simp", "simp_all", "ring", "ring_nf",
    "noncomm_ring", "group", "abel", "linarith", "nlinarith [sq_nonneg (0 : ℝ)]",
    "positivity", "omega", "aesop", "tauto", "field_simp", "push_cast",
    "intro h", "intros", "constructor", "funext x", "ext", "gcongr",
    "exact?", "apply?",
]


@dataclass
class Context:
    statement: str
    goals: list[str]
    path: tuple[str, ...]
    failures: list[tuple[str, str]] = field(default_factory=list)
    lemmas: list[str] = field(default_factory=list)


class StaticProposer:
    def __init__(self, tactics=None):
        self.tactics = tactics or STATIC_TACTICS

    def propose(self, ctx: Context, k: int) -> list[str]:
        return list(self.tactics)


class LLMProposer:
    """Uses Claude to propose tactics, whole proofs, and intermediate lemmas."""

    def __init__(self, model: str | None = None):
        import anthropic  # pip install anthropic
        self.client = anthropic.Anthropic()
        self.model = model or os.environ.get("PROOF_ENGINE_MODEL", "claude-opus-5-5")

    def _ask(self, prompt: str, max_tokens: int = 2000) -> str:
        r = self.client.messages.create(
            model=self.model, max_tokens=max_tokens,
            system="You are an expert in Lean 4 and Mathlib. Reply with JSON only.",
            messages=[{"role": "user", "content": prompt}])
        return "".join(b.text for b in r.content if getattr(b, "type", "") == "text")

    @staticmethod
    def _json(text: str):
        m = re.search(r"(\[.*\]|\{.*\})", text, re.S)
        return json.loads(m.group(1)) if m else None

    def propose(self, ctx: Context, k: int) -> list[str]:
        fails = "\n".join(f"- `{t}` failed: {e[:200]}" for t, e in ctx.failures[-8:])
        prompt = f"""Theorem:
{ctx.statement}

Tactics applied so far:
{chr(10).join(ctx.path) or "(none)"}

Current goals:
{chr(10).join(ctx.goals)}

Proven lemmas you may use: {", ".join(ctx.lemmas) or "(none)"}
Recent failures:
{fails or "(none)"}

Propose {k} distinct, diverse next tactics (single Lean 4 tactic each, may use `<;>`).
Return a JSON array of strings."""
        try:
            out = self._json(self._ask(prompt))
            return [t for t in out if isinstance(t, str)][:k] if isinstance(out, list) else []
        except Exception as e:  # network / parse failure: fall back silently
            print(f"  [llm] propose failed: {e}")
            return []

    def whole_proofs(self, statement: str, lemmas: list[str], n: int) -> list[str]:
        prompt = f"""Give {n} different complete Lean 4 tactic proofs of:
{statement}
Available proven lemmas: {", ".join(lemmas) or "(none)"}
Each proof is the tactic block that goes after `:= by`, newline separated.
Return a JSON array of strings."""
        try:
            out = self._json(self._ask(prompt, 4000))
            return [p for p in out if isinstance(p, str)] if isinstance(out, list) else []
        except Exception as e:
            print(f"  [llm] whole-proof failed: {e}")
            return []

    def decompose(self, statement: str, preamble_names: str, attempts: str, n: int) -> list[dict]:
        prompt = f"""This Lean 4 theorem resisted automated proof:
{statement}

What was tried and where it got stuck:
{attempts}

Propose up to {n} intermediate lemmas that, once proved, should make it easy.
Each must be a TRUE, self-contained Lean 4 statement in Mathlib, of the form
`theorem <unique_snake_name> <binders> : <prop>` with no proof.
Prefer lemmas strictly easier than the original. Context: {preamble_names}
Return JSON: {{"lemmas": [{{"name": "...", "statement": "theorem ..."}}], "plan": "one sentence"}}"""
        try:
            out = self._json(self._ask(prompt, 3000))
            return out.get("lemmas", []) if isinstance(out, dict) else []
        except Exception as e:
            print(f"  [llm] decompose failed: {e}")
            return []


class HybridProposer:
    def __init__(self, llm: LLMProposer, static: StaticProposer):
        self.llm, self.static = llm, static

    def propose(self, ctx, k):
        seen, out = set(), []
        for t in self.llm.propose(ctx, k) + self.static.propose(ctx, k):
            if t not in seen:
                seen.add(t)
                out.append(t)
        return out


# --------------------------------------------------------------------------
# Search
# --------------------------------------------------------------------------

@dataclass(order=True)
class Node:
    score: float
    tie: int
    path: tuple = field(compare=False)
    goals: list = field(compare=False)


def indent(tac: str) -> str:
    return "\n".join("  " + ln for ln in tac.splitlines())


def assemble(statement: str, path) -> str:
    return statement + " := by\n" + "\n".join(indent(t) for t in path)


def score(goals: list[str], depth: int) -> float:
    return 10 * len(goals) + sum(len(g) for g in goals) / 200 + 0.5 * depth


class Engine:
    def __init__(self, repl: LeanRepl, proposer, preamble: str, log_path: Path,
                 tactic_timeout: float = 30.0, width: int = 8):
        self.repl, self.proposer, self.preamble = repl, proposer, preamble
        self.log_path, self.tactic_timeout, self.width = log_path, tactic_timeout, width
        self.lemmas: list[str] = []        # full source of proven lemmas
        self.lemma_names: list[str] = []
        self._env = None
        self._gen = -1
        self._cache: dict = {}

    # -- environment -------------------------------------------------------
    def env(self) -> int:
        if self._env is None or self._gen != self.repl.generation:
            src = self.preamble + "\n\n" + "\n\n".join(self.lemmas)
            r = self.repl.send({"cmd": src}, timeout=600)
            errs = lean_errors(r)
            if errs:
                raise RuntimeError("Preamble / lemmas failed to compile:\n" + "\n".join(errs))
            self._env, self._gen, self._cache = r["env"], self.repl.generation, {}
        return self._env

    def add_lemma(self, name: str, proof_src: str):
        """Extend the loaded environment in place. Reloading the preamble (e.g. all of
        Mathlib) for every new lemma exhausts memory inside one REPL process."""
        self.lemmas.append(proof_src)
        self.lemma_names.append(name)
        if self._env is not None and self._gen == self.repl.generation:
            try:
                r = self.repl.send({"cmd": proof_src, "env": self._env}, timeout=300)
                if not lean_errors(r):
                    self._env, self._cache = r["env"], {}
                    return
            except (LeanTimeout, ReplRestarted):
                pass
        self._env = None  # fall back to a full rebuild on next use

    def recycle(self):
        """Restart Lean to free memory held by old proof states; the environment
        (preamble + proven lemmas) is rebuilt once on next use."""
        self.repl.restart()
        self._env, self._cache = None, {}

    def log(self, **rec):
        rec["t"] = time.time()
        with open(self.log_path, "a") as f:
            f.write(json.dumps(rec) + "\n")

    # -- proof states ------------------------------------------------------
    def check_statement(self, statement: str) -> tuple[int | None, list[str], str]:
        r = self.repl.send({"cmd": statement + " := by\n  sorry", "env": self.env()})
        errs = lean_errors(r)
        if errs or not r.get("sorries"):
            return None, [], "; ".join(errs) or "no goal produced"
        s = r["sorries"][0]
        return s["proofState"], [s["goal"]], ""

    def state_of(self, statement: str, path: tuple) -> int:
        key = (self.repl.generation, path)
        if key in self._cache:
            return self._cache[key]
        if not path:
            ps, _, err = self.check_statement(statement)
            if ps is None:
                raise RuntimeError(err)
        else:
            parent = self.state_of(statement, path[:-1])
            r = self.repl.send({"tactic": path[-1], "proofState": parent}, self.tactic_timeout)
            ps = r["proofState"]
        self._cache[(self.repl.generation, path)] = ps
        return ps

    def verify(self, src: str) -> bool:
        try:
            r = self.repl.send({"cmd": src, "env": self.env()}, timeout=300)
        except (LeanTimeout, ReplRestarted):
            return False
        if lean_errors(r):
            return False
        return not any("sorry" in m.get("data", "") for m in r.get("messages", []))

    # -- strategies --------------------------------------------------------
    def try_whole_proofs(self, statement: str, n: int) -> str | None:
        llm = getattr(self.proposer, "llm", None) or (
            self.proposer if isinstance(self.proposer, LLMProposer) else None)
        if not llm:
            return None
        for body in llm.whole_proofs(statement, self.lemma_names, n):
            if BANNED.search(body):
                continue
            src = statement + " := by\n" + indent(body)
            ok = self.verify(src)
            self.log(kind="whole", statement=statement, proof=body, ok=ok)
            if ok:
                return src
        return None

    def search(self, statement: str, budget: int) -> tuple[str | None, list]:
        ps, goals, err = self.check_statement(statement)
        if ps is None:
            raise ValueError(f"Statement does not elaborate: {err}")
        self._cache[(self.repl.generation, ())] = ps
        counter = itertools.count()
        frontier = [Node(score(goals, 0), next(counter), (), goals)]
        seen = {tuple(goals)}
        failures: list[tuple[str, str]] = []
        best_stuck = goals
        expansions = 0
        while frontier and expansions < budget:
            node = heapq.heappop(frontier)
            expansions += 1
            ctx = Context(statement, node.goals, node.path, failures, self.lemma_names)
            for tac in self.proposer.propose(ctx, self.width):
                if BANNED.search(tac):
                    continue
                try:
                    parent = self.state_of(statement, node.path)
                    r = self.repl.send({"tactic": tac, "proofState": parent}, self.tactic_timeout)
                except (LeanTimeout, ReplRestarted) as e:
                    failures.append((tac, f"timeout/restart: {e}"))
                    continue
                errs = lean_errors(r)
                if errs or "proofState" not in r:
                    failures.append((tac, (errs or ["?"])[0]))
                    self.log(kind="step", statement=statement, path=node.path, tactic=tac, ok=False)
                    continue
                tac = try_this(r) or tac
                child = node.path + (tac,)
                self._cache[(self.repl.generation, child)] = r["proofState"]
                new_goals = r.get("goals", [])
                self.log(kind="step", statement=statement, path=node.path, tactic=tac,
                         ok=True, goals=len(new_goals))
                if not new_goals:
                    src = assemble(statement, child)
                    if self.verify(src):
                        return src, []
                    continue
                key = tuple(new_goals)
                if key in seen:
                    continue
                seen.add(key)
                if score(new_goals, 0) < score(best_stuck, 0):
                    best_stuck = new_goals
                heapq.heappush(frontier, Node(score(new_goals, len(child)), next(counter),
                                              child, new_goals))
        return None, best_stuck

    def prove(self, statement: str, budget: int, whole: int) -> tuple[str | None, list]:
        src = self.try_whole_proofs(statement, whole) if whole else None
        if src:
            return src, []
        return self.search(statement, budget)


# --------------------------------------------------------------------------
# Blueprint loop
# --------------------------------------------------------------------------

def load_bp(p: Path) -> dict:
    return json.loads(p.read_text())


def save_bp(p: Path, bp: dict):
    tmp = p.with_suffix(".tmp")
    tmp.write_text(json.dumps(bp, indent=2, ensure_ascii=False))
    tmp.replace(p)


def run(bp_path: Path, engine: Engine, rounds: int, budget: int, whole: int,
        decompose: bool, max_depth: int, n_lemmas: int, pathways: set | None = None,
        recycle_every: int = 4):
    bp = load_bp(bp_path)
    targets = bp["targets"]
    # load already-proved lemmas into the environment, in order
    for t in targets:
        if t.get("status") == "proved" and t.get("proof"):
            engine.add_lemma(t["name"], t["proof"])

    for rnd in range(1, rounds + 1):
        open_ = [t for t in targets if t.get("status", "open") == "open"
                 and (pathways is None or t.get("pathway") in pathways)]
        if not open_:
            print("No open targets in scope.")
            break
        print(f"\n=== round {rnd}: {len(open_)} open targets ===")
        # leaves first: deeper lemmas feed their parents
        for k, t in enumerate(sorted(open_, key=lambda t: -t.get("depth", 0))):
            if recycle_every and k and k % recycle_every == 0:
                engine.recycle()
            print(f"\n> {t['name']}  (depth {t.get('depth', 0)}, attempt {t.get('attempts', 0) + 1})")
            try:
                src, stuck = engine.prove(t["statement"], budget, whole)
            except ValueError as e:
                print(f"  bad statement: {e}")
                t["status"] = "invalid"
                save_bp(bp_path, bp)
                continue
            except (LeanTimeout, ReplRestarted) as e:
                print(f"  Lean restarted ({e}); skipping this target for this round")
                engine.recycle()
                continue
            t["attempts"] = t.get("attempts", 0) + 1
            if src:
                print("  PROVED")
                t["status"], t["proof"] = "proved", src
                engine.add_lemma(t["name"], src)
                save_bp(bp_path, bp)
                continue
            print(f"  not yet. stuck at: {stuck[0][:160] if stuck else '?'}")
            t["stuck_goal"] = stuck[0] if stuck else None
            llm = getattr(engine.proposer, "llm", None) or (
                engine.proposer if isinstance(engine.proposer, LLMProposer) else None)
            if decompose and llm and t.get("depth", 0) < max_depth and not t.get("children"):
                names = ", ".join(x["name"] for x in targets)
                lemmas = llm.decompose(t["statement"], names, "\n".join(stuck), n_lemmas)
                kids = []
                for lem in lemmas:
                    name, stmt = lem.get("name"), lem.get("statement", "")
                    if not name or any(x["name"] == name for x in targets) or BANNED.search(stmt):
                        continue
                    ps, _, err = engine.check_statement(stmt)
                    if ps is None:
                        print(f"  rejected lemma {name}: {err[:120]}")
                        continue
                    targets.append({"name": name, "statement": stmt, "status": "open",
                                    "depth": t.get("depth", 0) + 1, "parent": t["name"],
                                    "pathway": t.get("pathway"),
                                    "origin": "llm-decomposition"})
                    kids.append(name)
                t["children"] = kids
                print(f"  decomposed into: {kids}")
            save_bp(bp_path, bp)

    proved = sum(t.get("status") == "proved" for t in targets)
    print(f"\nSummary: {proved}/{len(targets)} proved. Blueprint saved to {bp_path}")


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--project", required=True, help="Lean project with Mathlib (lake new X math)")
    ap.add_argument("--repl", required=True, help="path to the built REPL binary (repl/.lake/build/bin/repl)")
    ap.add_argument("--blueprint", default="blueprint.json")
    ap.add_argument("--proposer", choices=["static", "llm", "hybrid"], default="hybrid")
    ap.add_argument("--budget", type=int, default=60, help="node expansions per target per round")
    ap.add_argument("--width", type=int, default=8, help="LLM tactics per node")
    ap.add_argument("--whole", type=int, default=4, help="whole-proof LLM samples per target (0 = off)")
    ap.add_argument("--rounds", type=int, default=3)
    ap.add_argument("--decompose", action="store_true", help="let the LLM split stuck targets into lemmas")
    ap.add_argument("--max-depth", type=int, default=3)
    ap.add_argument("--lemmas", type=int, default=4)
    ap.add_argument("--log", default="explore.jsonl")
    ap.add_argument("--recycle", type=int, default=4,
                    help="restart Lean every N targets to free memory (0 = never)")
    ap.add_argument("--pathway", type=int, action="append",
                    help="only run targets tagged with this pathway number (repeatable)")
    a = ap.parse_args()

    bp_path = Path(a.blueprint).resolve()
    bp0 = load_bp(bp_path)
    preamble = bp0["preamble"]
    static = StaticProposer(STATIC_TACTICS + bp0.get("extra_tactics", []))
    if a.proposer == "static":
        prop = static
    elif a.proposer == "llm":
        prop = LLMProposer()
    else:
        prop = HybridProposer(LLMProposer(), static)
    whole = 0 if a.proposer == "static" else a.whole
    repl = LeanRepl(["lake", "env", str(Path(a.repl).resolve())], cwd=a.project)
    eng = Engine(repl, prop, preamble, Path(a.log).resolve(), width=a.width)
    run(bp_path, eng, a.rounds, a.budget, whole, a.decompose, a.max_depth, a.lemmas,
        set(a.pathway) if a.pathway else None, a.recycle)


if __name__ == "__main__":
    main()
