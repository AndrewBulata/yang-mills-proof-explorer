# Yang–Mills proof explorer

An engine that explores Lean 4 proofs around the Yang–Mills mass gap problem.
A proposer (a fixed tactic list, Claude, or both) suggests proof steps. Lean checks
every step. A best-first search keeps the most promising proof states, and stuck
targets can be split into smaller lemmas that become new targets.

Nothing counts as proved unless the assembled proof re-checks in Lean with no
errors and no `sorry`.

**This project does not prove the mass gap.** It builds verified infrastructure
along the known routes of attack and records exactly where each route gets stuck.

## Results so far

First run, 25 November 2026: tactic list only (no AI), 10 search nodes per target,
3,592 proof steps explored. 6 of 16 targets proved and re-checked by Lean.

| Target | Pathway | What it says | Status | Proof found |
| --- | --- | --- | --- | --- |
| `jacobi_ring` | foundations | Jacobi identity for commutators (algebra behind the Bianchi identity) | proved | `grind` |
| `holonomy_gauge` | foundations | Lattice Wilson loops transform by conjugation under gauge transformations | proved | `unfold holonomy gaugeTransform; group` |
| `two_site_gap` | foundations | Two-site lattice: energy gap 2 above the vacuum | proved | `nlinarith` |
| `three_site_gap` | foundations | Three-site lattice: energy gap 3 | proved | `nlinarith` |
| `massive_uniform_gap` | foundations | Massive lattice free field: gap ≥ m², uniform in lattice size | proved | `norm_num; positivity` |
| `z2_link_square` | finite groups | Z₂ link variables square to one | proved | `norm_num` |
| `gaps_can_close` | foundations | Positive gaps at every size do not give a uniform gap | open | |
| `massless_gap_closes` | foundations | Massless lattice field: the gap closes as size grows | open | |
| `gap_criterion_discrete` | formal route | One common decay rate forces a spectral gap | open | |
| `contraction_decay` | formal route | Transfer-matrix contraction gives geometric decay | open | |
| `gap_from_contraction` | formal route | Contraction q < 1 gives gap −log(q)/τ > 0 | open | |
| `pow_eq_exp_log` | formal route | qⁿ = exp(n log q) | open | |
| `scale_split_uniform_gap` | RG + strong coupling | Uniform bound past one scale plus finitely many scales gives a uniform gap | open | |
| `polymer_series_bound` | cluster expansion | Toy polymer series converges with explicit bound | open | |
| `poincare_variance_decay` | stochastic quantization | Poincaré-type contraction gives exponential variance decay | open | |
| `holonomy_gauge_abelian` | finite groups | Abelian Wilson loops are exactly gauge invariant | open | |

The open targets need induction, case analysis or a short lemma chain, which the
tactic list cannot plan. They are the job of the AI proposer (`--proposer hybrid`).
Full output: [`results/2026-11-25-static/`](results/2026-11-25-static/).

## How it works

```
blueprint.json ──► Engine ──► Lean REPL (the only judge)
   targets          │  best-first search over proof states
   preamble         │  proposer: tactic list / Claude / both
                    │  decomposition: stuck target → smaller lemmas
                    ▼
   proofs + stuck goals written back · every step logged to explore.jsonl
```

## Setup

```bash
./setup.sh                  # Lean, the REPL, and the ~2,000 Mathlib modules needed (~25 min on 2 cores)
FULL_MATHLIB=1 ./setup.sh   # or all of Mathlib via its download cache
python3 test_engine.py      # engine logic tests (no Lean needed)
```

The script falls back to GitHub release downloads when Lean's own servers are
unreachable.

## Run

```bash
W=lean-workspace
# tactic list only: free
python3 proof_engine.py --project $W/ymproj --repl $W/repl/.lake/build/bin/repl --proposer static

# with Claude proposing tactics, whole proofs and intermediate lemmas
pip install anthropic && export ANTHROPIC_API_KEY=...
python3 proof_engine.py --project $W/ymproj --repl $W/repl/.lake/build/bin/repl \
    --proposer hybrid --decompose --rounds 3 --budget 20

# one route at a time
python3 proof_engine.py ... --pathway 5 --pathway 6
```

Pathway numbers: 0 foundations · 1 formal route via the existence proof ·
2 multiscale RG · 3 RG then strong coupling · 4 cluster expansion ·
5 stochastic quantization · 6 finite gauge groups · 7 large N · 8 confinement.

Other flags: `--budget` (search nodes per target), `--width` (AI tactics per node),
`--whole` (whole-proof samples), `--max-depth` (decomposition depth),
`--recycle` (restart Lean every N targets to free memory). Re-running resumes
from the blueprint.

## Adding targets

Append to `targets` in `blueprint.json`. The statement is everything before `:= by`.
Shared definitions go in `preamble`; extra tactics for the tactic list go in
`extra_tactics`.

```json
{"name": "my_lemma", "pathway": 0, "statement": "theorem my_lemma (x : ℝ) : x ^ 2 ≥ 0", "status": "open", "depth": 0}
```

## Context

In November 2026 a working group chaired by David Gross validated OpenAI's Lean
formalization of the *existence* of 4D Yang–Mills theory (repository
`yang-mills-group/OpenAI-YM-20261028`). The mass gap remains open. Its definitions
make it possible to state the gap in Lean; see `_phase3_example` in
`blueprint.json` for how to point this engine at it.

`lean/YangMillsToy.lean` contains standalone proofs of the lattice gauge-invariance
results. All of it compiles against Mathlib except `trace_sq_gauge_invariant`, which
needs `Mathlib.LinearAlgebra.Matrix.Trace` and has not been checked yet.

## Limits

* Search finds proofs of lemmas, not new ideas. The mass gap needs an estimate
  nobody knows how to prove.
* AI-proposed lemmas can be false; a false lemma just stays unproved.
* Hybrid runs call the Claude API on every search node. Start small and watch spend.

## License

MIT. See [LICENSE](LICENSE).
