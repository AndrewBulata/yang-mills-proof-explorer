"""Tests the search and blueprint logic against a fake Lean (no Lean install needed).

Toy logic: goal `reach n`. Tactic `dec` turns n into n-1, `half` halves an even n,
`split` turns `reach n` (n >= 4) into two goals, `done` closes `reach 0`.
"""
import json
import re
import tempfile
from pathlib import Path

import proof_engine as pe


def step(goals, tac):
    if not goals:
        return None
    n, rest = goals[0], goals[1:]
    if tac == "dec" and n > 0:
        return [n - 1] + rest
    if tac == "half" and n % 2 == 0 and n > 0:
        return [n // 2] + rest
    if tac == "split" and n >= 4:
        return [n // 2, n - n // 2] + rest
    if tac == "done" and n == 0:
        return rest
    return None


class MockRepl:
    generation = 0

    def restart(self):
        self.generation += 1

    def __init__(self):
        self.states, self.calls = {}, 0

    def _new(self, goals):
        i = len(self.states)
        self.states[i] = goals
        return i

    def send(self, obj, timeout=None):
        self.calls += 1
        if "tactic" in obj:
            g = step(self.states[obj["proofState"]], obj["tactic"].strip())
            if g is None:
                return {"messages": [{"severity": "error", "data": "tactic failed"}], "proofState": -1}
            return {"proofState": self._new(g), "goals": [f"⊢ reach {x}" for x in g]}
        cmd = obj["cmd"]
        m = re.search(r"reach (\d+)", cmd)
        if not m:
            return {"env": 0}
        if "sorry" in cmd:
            return {"env": 1, "sorries": [{"proofState": self._new([int(m.group(1))]),
                                           "goal": f"⊢ reach {m.group(1)}"}]}
        goals = [int(m.group(1))]
        for line in cmd.split(":= by", 1)[1].splitlines():
            if line.strip():
                goals = step(goals, line.strip())
                if goals is None:
                    return {"env": 2, "messages": [{"severity": "error", "data": "bad"}]}
        return {"env": 2} if goals == [] else {"env": 2, "messages": [{"severity": "error", "data": "unsolved"}]}


def test_search_finds_proof():
    tmp = Path(tempfile.mkdtemp())
    eng = pe.Engine(MockRepl(), pe.StaticProposer(["dec", "half", "split", "done", "sorry"]),
                    "import Mathlib", tmp / "log.jsonl")
    src, _ = eng.search("theorem t : reach 12", budget=200)
    assert src is not None, "no proof found"
    assert "sorry" not in src
    assert eng.verify(src)
    print("found:\n" + src)


def test_budget_exhaustion_reports_stuck():
    tmp = Path(tempfile.mkdtemp())
    eng = pe.Engine(MockRepl(), pe.StaticProposer(["dec"]), "import Mathlib", tmp / "log.jsonl")
    src, stuck = eng.search("theorem t : reach 50", budget=5)
    assert src is None and stuck, "should be stuck with a frontier goal"
    print("stuck at:", stuck)


def test_blueprint_loop():
    tmp = Path(tempfile.mkdtemp())
    bp = {"preamble": "import Mathlib", "targets": [
        {"name": "a", "statement": "theorem a : reach 6", "status": "open"},
        {"name": "b", "statement": "theorem b : reach 9", "status": "open"},
    ]}
    p = tmp / "bp.json"
    p.write_text(json.dumps(bp))
    eng = pe.Engine(MockRepl(), pe.StaticProposer(["dec", "half", "done"]), "import Mathlib",
                    tmp / "log.jsonl")
    pe.run(p, eng, rounds=2, budget=100, whole=0, decompose=False, max_depth=2, n_lemmas=2)
    out = json.loads(p.read_text())
    assert all(t["status"] == "proved" for t in out["targets"])
    assert len((tmp / "log.jsonl").read_text().splitlines()) > 0


def test_pathway_filter():
    tmp = Path(tempfile.mkdtemp())
    bp = {"preamble": "import Mathlib", "targets": [
        {"name": "a", "statement": "theorem a : reach 6", "status": "open", "pathway": 4},
        {"name": "b", "statement": "theorem b : reach 9", "status": "open", "pathway": 5},
    ]}
    p = tmp / "bp.json"
    p.write_text(json.dumps(bp))
    eng = pe.Engine(MockRepl(), pe.StaticProposer(["dec", "half", "done"]), "import Mathlib",
                    tmp / "log.jsonl")
    pe.run(p, eng, rounds=1, budget=100, whole=0, decompose=False, max_depth=2, n_lemmas=2,
           pathways={4})
    out = {t["name"]: t["status"] for t in json.loads(p.read_text())["targets"]}
    assert out == {"a": "proved", "b": "open"}, out


def test_conjecture_surgery():
    import conjecture as cj
    st = "theorem two_site_gap (v₀ v₁ : ℝ) (h : v₀ + v₁ = 0) : (v₀ - v₁) ^ 2 ≥ 2 * (v₀ ^ 2 + v₁ ^ 2)"
    name, binders, prop = cj.split_statement(st)
    assert name == "two_site_gap" and binders.endswith("= 0)") and prop.startswith("(v₀ - v₁)")
    assert cj.negation(st).startswith("theorem two_site_gap_refuted : ¬ (∀ (v₀ v₁ : ℝ)")
    muts = {d for _, _, d in cj.mutate("two_site_gap", st)}
    assert "constant 2 → 3" in muts and "hypothesis h dropped" in muts and "≥ → >" in muts
    assert all("^ 3" not in s2 for _, s2, _ in cj.mutate("two_site_gap", st)), "exponents must not mutate"
    assert len(cj.witness_tactics(st)) == 36
    assert all("\n" not in t for t in cj.witness_tactics(st)), "REPL tactics must be one line"


if __name__ == "__main__":
    test_conjecture_surgery()
    test_pathway_filter()
    test_search_finds_proof()
    test_budget_exhaustion_reports_stuck()
    test_blueprint_loop()
    print("\nall tests passed")
