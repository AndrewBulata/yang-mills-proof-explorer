#!/usr/bin/env python3
"""
conjecture.py: let the engine invent statements, then refute, recognise, or prove them.

Loop (one round):
  1. GENERATE candidate statements
       mutate   : perturb proved theorems (constants ±1, strict/non-strict, drop a hypothesis)
       families : parameter sweeps defined in families.py (e.g. n-site lattice gaps, n = 2..5)
       llm      : Claude proposes new conjectures from the proved library (needs ANTHROPIC_API_KEY)
  2. FILTER    : discard statements Lean cannot elaborate, and duplicates
  3. REFUTE    : try to prove the negation, searching small integer counterexamples
  4. RECOGNISE : one `exact?` call; if it closes the goal, the result is already in Mathlib
  5. PROVE     : best-first search, as in proof_engine.py
  6. FEEDBACK  : proved statements join the library and seed the next round's mutations

Every verdict (proved, refuted, known) is a Lean-checked proof. Output goes to
conjectures.json and a readable report, conjectures.md.
"""
from __future__ import annotations

import argparse
import itertools
import json
import re
from pathlib import Path

import proof_engine as pe

# Fast tactics for conjecture mode (no exact?/apply?: those are reserved for step 4).
FAST_TACTICS = [
    "rfl", "decide", "norm_num", "simp", "simp_all", "ring", "ring_nf", "noncomm_ring",
    "group", "abel", "linarith", "nlinarith [sq_nonneg (0 : ℝ)]", "positivity", "omega",
    "grind", "intro h", "intros", "constructor", "aesop", "field_simp",
]

# ---------------------------------------------------------------------------
# statement surgery
# ---------------------------------------------------------------------------

def split_statement(stmt: str) -> tuple[str, str, str] | None:
    """'theorem name binders : prop' -> (name, binders, prop). None if unparseable."""
    m = re.match(r"\s*(?:theorem|lemma)\s+(\S+)\s*(.*)$", stmt, re.S)
    if not m:
        return None
    name, rest = m.group(1), m.group(2)
    depth = 0
    for i, ch in enumerate(rest):
        if ch in "([{⦃⟨":
            depth += 1
        elif ch in ")]}⦄⟩":
            depth -= 1
        elif ch == ":" and depth == 0 and rest[i + 1: i + 2] != "=":
            return name, rest[:i].strip(), rest[i + 1:].strip()
    return None


def rename(stmt: str, new: str) -> str:
    return re.sub(r"^(\s*(?:theorem|lemma)\s+)\S+", lambda m: m.group(1) + new, stmt, count=1)


def negation(stmt: str) -> str | None:
    parts = split_statement(stmt)
    if not parts:
        return None
    name, binders, prop = parts
    body = f"∀ {binders}, {prop}" if binders else prop
    return f"theorem {name}_refuted : ¬ ({body})"


def binder_count(binders: str) -> int:
    """Number of explicit variables (hypotheses included), used to size witness tuples."""
    n = 0
    for grp in re.findall(r"\(([^()]*?)\s:\s", binders):
        n += len(grp.split())
    return n


def witness_tactics(stmt: str) -> list[str]:
    """Counterexample search: after pushing ¬ inward, try small explicit witnesses."""
    parts = split_statement(stmt)
    if not parts:
        return []
    _, binders, _ = parts
    vars_ = [v for grp in re.findall(r"\(([^()]*?)\s:\s*ℝ\)", binders) for v in grp.split()]
    k = len(vars_)
    if k == 0 or k > 4:
        return []
    # small integer grid; coarser as the number of variables grows
    values = {1: ("1", "-1", "0", "2", "-2", "3"), 2: ("1", "-1", "0", "2", "-2", "3"),
              3: ("1", "-1", "0", "2", "-2"), 4: ("3", "1", "-1", "-3", "0")}[k]
    tacs = []
    for combo in itertools.product(values, repeat=k):
        # one line: the REPL reads only the first line of a multi-line tactic
        tacs.append("(push Not; refine ⟨" + ", ".join(f"({c} : ℝ)" for c in combo) + ", ?_⟩ <;> norm_num)")
    return tacs


# ---------------------------------------------------------------------------
# generators
# ---------------------------------------------------------------------------

REL_SWAPS = [("≥", ">"), ("≤", "<"), (">", "≥"), ("<", "≤")]


def mutate(name: str, stmt: str) -> list[tuple[str, str, str]]:
    """Return (new_name, new_statement, description) variants of a proved statement."""
    parts = split_statement(stmt)
    if not parts:
        return []
    _, binders, prop = parts
    out = []
    # integer constants ±1 (only in the conclusion)
    for k, m in enumerate(re.finditer(r"(?<![\w.₀-₉⁰-⁹])(\d+)(?![\w.])", prop)):
        if prop[:m.start()].rstrip().endswith("^"):
            continue  # leave exponents alone
        val = int(m.group(1))
        for new, tag in ((val + 1, "up"), (val - 1, "down")):
            if new < 0 or (val in (0, 1) and tag == "down"):
                continue
            p2 = prop[:m.start()] + str(new) + prop[m.end():]
            out.append((f"{name}__c{k}{tag}", f"theorem {name}__c{k}{tag} {binders} : {p2}",
                        f"constant {val} → {new}"))
    # relation swaps (first occurrence)
    for a, b in REL_SWAPS:
        if a in prop:
            p2 = prop.replace(a, b, 1)
            tag = {"≥": "gt", "≤": "lt", ">": "ge", "<": "le"}[a]
            out.append((f"{name}__{tag}", f"theorem {name}__{tag} {binders} : {p2}", f"{a} → {b}"))
    # drop one hypothesis binder (h... : ...)
    for m in re.finditer(r"\((h\w*)\s*:\s*[^()]*(?:\([^()]*\)[^()]*)*\)", binders):
        b2 = (binders[:m.start()] + binders[m.end():]).strip()
        b2 = re.sub(r"\s+", " ", b2)
        out.append((f"{name}__no_{m.group(1)}", f"theorem {name}__no_{m.group(1)} {b2} : {prop}",
                    f"hypothesis {m.group(1)} dropped"))
    return out


def family_conjectures() -> list[tuple[str, str, str]]:
    try:
        import families
    except ImportError:
        return []
    out = []
    for fam in families.FAMILIES:
        for name, stmt, about in fam():
            out.append((name, stmt, about))
    return out


# ---------------------------------------------------------------------------
# the loop
# ---------------------------------------------------------------------------

def classify(engine: pe.Engine, name: str, stmt: str, budget: int, fast: list[str]) -> dict:
    rec = {"name": name, "statement": stmt}
    ps, _, err = engine.check_statement(stmt)
    if ps is None:
        rec["verdict"] = "ill-typed"
        rec["detail"] = err[:300]
        return rec

    # 3. refute
    neg = negation(stmt)
    if neg:
        engine.proposer = pe.StaticProposer(witness_tactics(stmt) + ["(push Not; norm_num)", "simp", "norm_num"])
        try:
            src, _ = engine.search(neg, budget=1)
        except (ValueError, pe.LeanTimeout, pe.ReplRestarted):
            src = None
        if src:
            rec.update(verdict="refuted", proof=src)
            return rec

    # 4. recognise
    engine.proposer = pe.StaticProposer(["exact?"])
    try:
        src, _ = engine.search(stmt, budget=1)
    except (ValueError, pe.LeanTimeout, pe.ReplRestarted):
        src = None
    if src:
        rec.update(verdict="known", proof=src)
        return rec

    # 5. prove
    engine.proposer = pe.StaticProposer(fast)
    try:
        src, stuck = engine.search(stmt, budget=budget)
    except (ValueError, pe.LeanTimeout, pe.ReplRestarted) as e:
        src, stuck = None, [str(e)]
    if src:
        rec.update(verdict="proved", proof=src)
    else:
        rec.update(verdict="open", stuck_goal=(stuck or [""])[0][:400])
    return rec


def sharpness_notes(records: list[dict]) -> list[str]:
    notes = []
    for r in records:
        if r["origin"] == "family" and r["verdict"] == "refuted":
            notes.append(f"`{r['name']}` is false ({r['about']} fails), refuted by an explicit counterexample.")
    for r in records:
        m = re.match(r"(.+)__c(\d+)up$", r["name"])
        if m and r["verdict"] == "refuted":
            old, new = re.findall(r"-?\d+", r.get("about", "0 → 0"))[:2]
            notes.append(f"`{m.group(1)}`: the constant {old} is sharp among integers "
                         f"({new} is refuted by an explicit counterexample).")
        m = re.match(r"(.+)__no_(h\w*)$", r["name"])
        if m and r["verdict"] == "refuted":
            notes.append(f"`{m.group(1)}`: hypothesis `{m.group(2)}` is necessary (dropping it is refuted).")
        if m and r["verdict"] in ("proved", "known"):
            notes.append(f"`{m.group(1)}`: hypothesis `{m.group(2)}` is unnecessary; the stronger statement holds.")
    return notes


def write_report(path: Path, records: list[dict], rounds: int):
    counts = {}
    for r in records:
        counts[r["verdict"]] = counts.get(r["verdict"], 0) + 1
    lines = ["# Conjecture run", "",
             f"{len(records)} candidate statements over {rounds} round(s): "
             + ", ".join(f"{v} {k}" for k, v in sorted(counts.items())) + ".", ""]
    notes = sharpness_notes(records)
    if notes:
        lines += ["## Findings", ""] + [f"- {n}" for n in notes] + [""]
    for verdict in ("proved", "known", "refuted", "open"):
        rs = [r for r in records if r["verdict"] == verdict]
        if not rs:
            continue
        lines += [f"## {verdict.capitalize()} ({len(rs)})", ""]
        for r in rs:
            lines += [f"**{r['name']}** ({r.get('origin', '')})", "", "```lean", r["statement"], "```", ""]
            if r.get("proof"):
                lines += ["<details><summary>Lean proof</summary>", "", "```lean", r["proof"], "```",
                          "", "</details>", ""]
    path.write_text("\n".join(lines))


def run(engine: pe.Engine, bp: dict, rounds: int, budget: int, sources: set[str], out_dir: Path,
        llm=None, max_per_round: int = 60, only: set[str] | None = None):
    out_dir.mkdir(parents=True, exist_ok=True)
    library = {t["name"]: t["statement"] for t in bp["targets"] if t.get("status") == "proved"}
    for t in bp["targets"]:
        if t.get("status") == "proved" and t.get("proof"):
            engine.add_lemma(t["name"], t["proof"])
    fast = FAST_TACTICS + bp.get("extra_tactics", [])
    seen = set(library.values())
    records: list[dict] = []
    # statements whose mutations we have not explored yet
    frontier = {n: st for n, st in library.items() if only is None or n in only}

    for rnd in range(1, rounds + 1):
        cands: list[tuple[str, str, str, str]] = []
        if "mutate" in sources:
            for n, s in frontier.items():
                cands += [(a, b, c, "mutation") for a, b, c in mutate(n, s)]
        if "families" in sources and rnd == 1:
            cands += [(a, b, c, "family") for a, b, c in family_conjectures()]
        if "llm" in sources and llm is not None:
            for a, b in llm.conjecture(list(library.items()), bp["preamble"], 10):
                cands.append((a, b, "LLM conjecture", "llm"))
        frontier = {}
        fresh = []
        for c in cands:
            key = " ".join(split_statement(c[1])[2].split()) if split_statement(c[1]) else c[1]
            if c[1] in seen or key in seen:
                continue
            seen.add(c[1]); seen.add(key)
            fresh.append(c)
        fresh = fresh[:max_per_round]
        print(f"\n=== round {rnd}: {len(fresh)} new candidates ===")
        for k, (name, stmt, about, origin) in enumerate(fresh):
            if k and k % 6 == 0:
                engine.recycle()
            rec = classify(engine, name, stmt, budget, fast)
            rec["about"], rec["origin"], rec["round"] = about, origin, rnd
            print(f"  {rec['verdict']:9s} {name}   [{about}]")
            records.append(rec)
            if rec["verdict"] in ("proved", "known"):
                engine.add_lemma(name, rec["proof"])
                library[name] = stmt
                frontier[name] = stmt
            (out_dir / "conjectures.json").write_text(json.dumps(records, indent=2, ensure_ascii=False))
        if not frontier and "llm" not in sources:
            break
    write_report(out_dir / "conjectures.md", records, rnd)
    return records


class LLMConjecturer(pe.LLMProposer):
    def conjecture(self, library: list[tuple[str, str]], preamble: str, n: int) -> list[tuple[str, str]]:
        lib = "\n".join(s for _, s in library[-40:])
        prompt = f"""Definitions in scope:
{preamble[-3000:]}

Proved library:
{lib}

Propose {n} NEW Lean 4 statements that would be interesting, plausibly true, and not
already in the library or in Mathlib: generalisations (fixed n → all n), sharper constants,
converses, or new results about these definitions. Each is `theorem <unique_name> <binders> : <prop>`
with no proof. Return a JSON array of objects {{"name": ..., "statement": ...}}."""
        try:
            out = self._json(self._ask(prompt, 3000))
            return [(o["name"], o["statement"]) for o in out if isinstance(o, dict)]
        except Exception as e:
            print(f"  [llm] conjecture failed: {e}")
            return []


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--project", required=True)
    ap.add_argument("--repl", required=True)
    ap.add_argument("--blueprint", default="blueprint.json", help="proved targets seed the library")
    ap.add_argument("--sources", default="mutate,families", help="comma list: mutate,families,llm")
    ap.add_argument("--rounds", type=int, default=2)
    ap.add_argument("--budget", type=int, default=6)
    ap.add_argument("--only", default="", help="comma list of library theorem names to mutate")
    ap.add_argument("--out", default="conjecture-run")
    a = ap.parse_args()
    bp = json.loads(Path(a.blueprint).read_text())
    only = set(a.only.split(",")) if a.only else None
    sources = set(a.sources.split(","))
    repl = pe.LeanRepl(["lake", "env", str(Path(a.repl).resolve())], cwd=a.project)
    eng = pe.Engine(repl, pe.StaticProposer(FAST_TACTICS), bp["preamble"], Path(a.out) / "explore.jsonl")
    llm = LLMConjecturer() if "llm" in sources else None
    run(eng, bp, a.rounds, a.budget, sources, Path(a.out), llm, only=only)


if __name__ == "__main__":
    main()
