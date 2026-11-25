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

**All 22 targets are proved and checked by Lean 4 against Mathlib.** Every proof
depends only on Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). The full proof library is [`lean/Verified.lean`](lean/Verified.lean).

| Run | Proposer | Proved | Output |
| --- | --- | --- | --- |
| 1 | Tactic list, engine search (3,592 steps) | 6 of 16 | [`results/2026-11-25-static/`](results/2026-11-25-static/) |
| 2 | Claude as proposer, every proof verified by Lean | remaining 10, plus 6 new | [`results/2026-11-25-claude-proposer/`](results/2026-11-25-claude-proposer/) |

The tactic list proved none of the 6 new results on its own. They need multi-step
plans (reindexing a sum over a group, hyperbolic identities, a product of sums),
which is what an AI proposer adds.

### New in run 2: exact confinement in 2D Z₂ gauge theory

In two dimensions, Z₂ lattice gauge theory can be solved exactly. After the standard
2D gauge fixing, the plaquettes inside a Wilson loop become independent Z₂ variables.
Run 2 proves the consequences in Lean:

| Theorem | Statement |
| --- | --- |
| `z2_plaquette_expectation` | One plaquette with weight exp(βu) has ⟨u⟩ = tanh β |
| `z2_wilson_loop_area_law` | A loop enclosing A independent plaquettes has ⟨W⟩ = (tanh β)^A |
| `z2_string_tension_pos` | The string tension σ = −log tanh β is positive for every β > 0 |
| `z2_area_law_exponential` | ⟨W⟩ = exp(−σA): an area law, so confinement at all couplings |
| `elitzur_mechanism` | An observable that flips sign under a symmetry of the weight has zero expectation |
| `haar_left_invariant` | The counting (Haar) measure on a finite gauge group is translation invariant |

These are textbook results, going back to Wegner (1971) and Balian, Drouffe and Itzykson (1975), formalized here. The gauge-fixing
step, from link variables to independent plaquettes, is taken as given and is the
natural next target. In four dimensions the analogous statement for SU(N) is the open
confinement problem.

### All targets

| Target | Pathway | What it says | Found by |
| --- | --- | --- | --- |
| `jacobi_ring` | foundations | Jacobi identity for commutators (algebra behind the Bianchi identity) | engine |
| `holonomy_gauge` | foundations | Lattice Wilson loops transform by conjugation under gauge transformations | engine |
| `two_site_gap` | foundations | Two-site lattice: energy gap 2 above the vacuum | engine |
| `three_site_gap` | foundations | Three-site lattice: energy gap 3 | engine |
| `massive_uniform_gap` | foundations | Massive lattice free field: gap ≥ m², uniform in lattice size | engine |
| `z2_link_square` | finite groups | Z₂ link variables square to one | engine |
| `gaps_can_close` | foundations | Positive gaps at every size do not give a uniform gap | Claude |
| `massless_gap_closes` | foundations | Massless lattice field: a step profile has gradient energy 2/(M+1), so the gap closes | Claude |
| `gap_criterion_discrete` | formal route | One common decay rate forces a spectral gap | Claude |
| `contraction_decay` | formal route | Transfer-matrix contraction gives geometric decay | Claude |
| `gap_from_contraction` | formal route | Contraction q < 1 gives gap −log(q)/τ > 0 | Claude |
| `pow_eq_exp_log` | formal route | qⁿ = exp(n log q) | Claude |
| `scale_split_uniform_gap` | RG + strong coupling | Uniform bound past one scale plus finitely many scales gives a uniform gap | Claude |
| `polymer_series_bound` | cluster expansion | Toy polymer series converges with explicit bound | Claude |
| `poincare_variance_decay` | stochastic quantization | Poincaré-type contraction gives exponential variance decay | Claude |
| `holonomy_gauge_abelian` | finite groups | Abelian Wilson loops are exactly gauge invariant | Claude |
| `haar_left_invariant` | finite groups | Haar measure on a finite group is translation invariant | Claude |
| `elitzur_mechanism` | confinement | Sign-flipping observables have zero expectation | Claude |
| `z2_plaquette_expectation` | confinement | ⟨u⟩ = tanh β for one Z₂ plaquette | Claude |
| `z2_wilson_loop_area_law` | confinement | ⟨W⟩ = (tanh β)^A in 2D Z₂ gauge theory | Claude |
| `z2_string_tension_pos` | confinement | σ = −log tanh β > 0 for all β > 0 | Claude |
| `z2_area_law_exponential` | confinement | ⟨W⟩ = exp(−σA) | Claude |

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

`lean/Verified.lean` holds every proof above in one file. `lean/YangMillsToy.lean`
contains the original standalone lattice gauge-invariance results. All of it compiles
against Mathlib except `trace_sq_gauge_invariant`, which needs
`Mathlib.LinearAlgebra.Matrix.Trace` and has not been checked yet.

## Limits

* Search finds proofs of lemmas, not new ideas. The mass gap needs an estimate
  nobody knows how to prove.
* AI-proposed lemmas can be false; a false lemma just stays unproved.
* Hybrid runs call the Claude API on every search node. Start small and watch spend.

## License

MIT. See [LICENSE](LICENSE).
