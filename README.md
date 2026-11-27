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

**All 29 engine targets are proved and checked by Lean 4 against Mathlib, plus a strong-coupling library for any dimension (Parts E to G of `lean/Verified.lean`).** Every proof
depends only on Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). The full proof library is [`lean/Verified.lean`](lean/Verified.lean).

| Run | Proposer | Proved | Output |
| --- | --- | --- | --- |
| 1 | Tactic list, engine search (3,592 steps) | 6 of 16 | [`results/2026-11-25-static/`](results/2026-11-25-static/) |
| 2 | AI-assisted proposer, every proof verified by Lean | remaining 10, plus 13 new | [`results/2026-11-25-ai-assisted/`](results/2026-11-25-ai-assisted/) |
| 3 | Conjecture mode: engine invents and tests its own statements | 45 explored: 16 proved, 18 refuted, 11 open | [`results/2026-11-25-conjecture-run/`](results/2026-11-25-conjecture-run/) |
| 4 | Engine search on Part G's basic lemmas, given only the definitions | 6 of 7 | [`results/2026-11-25-engine-part-g/`](results/2026-11-25-engine-part-g/) |
| 5 | Engine search on Part I's lemmas, given only the definitions | 3 of 10 | [`results/2026-11-27-engine-pieces/`](results/2026-11-27-engine-pieces/) |

Parts B to I were developed with an AI-assisted proposer and checked by Lean outside the
search loop; run 4 put the engine back on Part G's basic lemmas, where it found its own
proofs for 6 of 7. The tactic list proved none of the 6 new results of run 2 on its own. They need multi-step
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

These are textbook results, going back to Wegner (1971) and Balian, Drouffe, and Itzykson (1975), formalized here. The gauge-fixing
step, from link variables to independent plaquettes, is taken as given and is the
natural next target. In four dimensions the analogous statement for SU(N) is the open
confinement problem.

### Mass gap of 2D Z₂ gauge theory, from the transfer matrix

The Yang–Mills question asks for a spectral gap of the transfer matrix above the vacuum.
For 2D Z₂ lattice gauge theory this can be answered exactly, and Lean now verifies it.
The transfer matrix `(T f)(s) = Σ_{s'} exp(β s s') f(s')` acts on one Z₂ variable:

| Theorem | Statement |
| --- | --- |
| `z2_transfer_vacuum` | The vacuum has eigenvalue 2 cosh β |
| `z2_transfer_excited` | Every state orthogonal to the vacuum has eigenvalue 2 sinh β |
| `z2_transfer_spectrum` | The spectrum is exactly {2 cosh β, 2 sinh β} |
| `z2_transfer_iterate` | n Euclidean time steps multiply an excited state by (2 sinh β)ⁿ |
| `z2_transfer_gap` | For β > 0: 0 < 2 sinh β < 2 cosh β, ratio tanh β |
| `z2_mass_gap` | **There is m > 0 with excited states decaying as exp(−m n) relative to the vacuum, at every coupling; m = −log tanh β** |

As with the area law, the reduction of the 2D theory to this single-variable transfer
matrix (axial gauge) is taken as given.

### Strong-coupling expansion in any dimension, including 4D

The first layer of the Osterwalder–Seiler strong-coupling analysis, proved for Z₂ lattice
gauge theory on **any finite lattice in any dimension** (Part E of `lean/Verified.lean`).
A lattice is a finite set of links, a finite set of plaquettes, and each plaquette's
boundary; the periodic d-dimensional hypercubic lattice is defined as an instance.

| Theorem | Statement |
| --- | --- |
| `HTE.exp_pm` | e^{βu} = cosh β (1 + u tanh β) for u = ±1 |
| `HTE.orthogonality` | Summing over all link configurations kills every odd power of a link spin |
| `HTE.numer_expand` | Σ_U W_C e^{βΣu_p} = cosh(β)^{\|P\|} 2^{\|L\|} Σ_{S: ∂S = C} tanh(β)^{\|S\|} |
| `HTE.Z_expand` | The partition function is a sum over closed plaquette surfaces |
| `HTE.wilson_ratio` | ⟨W_C⟩ = (surfaces bounded by C) / (closed surfaces) |
| `HTE.wilson_nonneg` | ⟨W_C⟩ ≥ 0 for β ≥ 0 (a Griffiths-type inequality) |
| `HTE.wilson_le_surf` | ⟨W_C⟩ ≤ Σ_{S: ∂S = C} tanh(β)^{\|S\|} |
| `HTE.area_bound` | If every surface bounded by C has at least A plaquettes, ⟨W_C⟩ ≤ 2^{\|P\|} tanh(β)^A |
| `Hypercubic.area_bound_4d`, `wilson_nonneg_4d` | The same, on the 4D hypercubic lattice |

**Polymer cancellation and a volume-uniform area law** (Part F). Split each surface
bounded by C into the piece attached to C and a closed remainder; the closed remainders
cancel against the partition function. Then a count of attached surfaces gives an area
law that does not depend on the volume:

| Theorem | Statement |
| --- | --- |
| `HTE.polymer_cancellation` | Σ_{∂S=C} t^{\|S\|} ≤ (Σ_{attached T} t^{\|T\|}) · Σ_{∂R=∅} t^{\|R\|} |
| `HTE.wilson_le_polymer` | ⟨W_C⟩ ≤ Σ over attached surfaces only |
| `HTE.area_law_uniform` | ≤ c^k attached surfaces of size k, each ≥ A plaquettes ⇒ sum ≤ (ct)^A / (1 − ct) |
| `HTE.strong_coupling_area_law` | ⟨W_C⟩ ≤ (c tanh β)^A / (1 − c tanh β), uniform in volume, whenever c tanh β < 1 |
| `HTE.string_tension_exponential` | String tension σ = −log(c tanh β) > 0, and ⟨W_C⟩ ≤ e^{−σA} / (1 − c tanh β) |
| `Hypercubic.strong_coupling_area_law_4d` | The same on the 4D hypercubic lattice |

**The splitting map, constructed** (Part G). The part of a surface attached to the loop is
built explicitly for any lattice: the plaquettes reachable from one touching C through
plaquettes that share links. Lean verifies that the remainder is closed, that the attached
part has boundary C, and that it is connected and touches C. This removes the splitting
hypothesis entirely:

| Theorem | Statement |
| --- | --- |
| `HTE.rest_closed` | The remainder S \ comp S is a closed surface |
| `HTE.comp_boundary` | The attached part comp S has the same boundary C |
| `HTE.comp_attached` | comp S is connected and attached to C in its own right |
| `HTE.strong_coupling_area_law_connected` | Volume-uniform area law from two inputs only |
| `Hypercubic.strong_coupling_area_law_4d_connected` | The same on the 4D lattice |

**Lattice animals** (Part H). A general counting theorem for any finite graph where
every vertex has at most Δ neighbours:

| Theorem | Statement |
| --- | --- |
| `Animals.growth` | A connected set can be grown from one vertex by adding one neighbour at a time |
| `Animals.exists_cover` | Every connected set of size k + 1 is the vertex set of a walk with 2k steps |
| `Animals.card_walksFrom` | There are at most Δ^m walks with m steps from a vertex |
| `Animals.animal_count` | **At most Δ^(2k) connected sets of size k + 1 contain a given vertex** |

**Several pieces along the loop, and the perimeter-corrected area law** (Part I). The part
of a surface attached to the loop can have several connected pieces, each touching the loop
somewhere else. Induction on the plaquettes touching the loop handles this: peel off the
piece reachable from one of them, show the rest is still attached to the others, and
multiply. Each piece is then counted by the lattice-animal bound.

| Theorem | Statement |
| --- | --- |
| `Animals.rest_attached` | Removing one seed's piece leaves a set attached to the other seeds |
| `Animals.Gsum_le_prod` | Attached sets, weighted by τ^size, sum to at most ∏ over seeds of (1 + rooted sum) |
| `Animals.Rsum_le` | Each rooted sum is at most τ / (1 − Δ²τ), by the lattice-animal bound |
| `HTE.strong_coupling_area_law_perimeter` | **⟨W_C⟩ ≤ (tanh β / τ)^A · (1 + τ/(1 − Δ²τ))^m, uniform in the volume** |

Here m is the number of plaquettes touching C, so the second factor is a perimeter
correction e^{μ|C|}, and (tanh β / τ)^A is the area law. This is the standard form of the
strong-coupling result, proved for any lattice in any dimension.

**What remains for a complete 4D strong-coupling confinement theorem** is now two facts about
the hypercubic lattice, both stated as hypotheses:

1. **Degree bound**: each plaquette shares a link with at most Δ plaquettes (Δ = 21 in 4D,
   itself included).
2. **Minimal area**: every surface bounded by an R×T planar loop has at least R·T plaquettes.

### Conjecture mode: the engine proposes its own statements

`conjecture.py` turns the engine from a prover into an explorer. Each round it
generates candidate statements, then for each one tries to:

1. **refute** it, by proving its negation with a search over small integer counterexamples;
2. **recognise** it, with one `exact?` call that detects results already in Mathlib;
3. **prove** it, with the usual best-first search.

Proved statements join the library and seed the next round. Candidates come from
mutations of proved theorems (constants ±1, strict vs non-strict, dropped hypotheses),
parameter families in `families.py`, and, with an API key, conjectures proposed by Claude.
Every verdict is a Lean-checked proof, including every refutation.

What the first run found on its own (full report:
[`conjectures.md`](results/2026-11-25-conjecture-run/conjectures.md)):

- **The massless gap closes.** "An n-site chain has gap ≥ 1" is proved for n = 2 and
  refuted for n = 4, with the counterexample (3, 1, −1, −3): energy 12, norm 20. The true
  gap 2 − 2cos(π/n) falls below 1 at n = 4.
- **Sharp constants.** The gap constants in `two_site_gap`, `three_site_gap`,
  `complete_gap_3` and `complete_gap_4` are optimal: raising each by one is refuted.
- **Necessary hypotheses.** Dropping the mean-zero condition, `0 < q` in
  `gap_from_contraction`, or `0 < β` in `z2_string_tension_pos` is refuted in each case.
- **A pattern to generalise.** The complete-graph gap is n for n = 3, 4, and 5. It was then
  proved for every n (`complete_graph_gap_all`), the step an AI proposer adds to the loop.

```bash
python3 conjecture.py --project $W/ymproj --repl $W/repl/.lake/build/bin/repl \
    --blueprint results/2026-11-25-ai-assisted/blueprint.json \
    --sources mutate,families --rounds 2 --only two_site_gap,three_site_gap
# add llm to --sources (with ANTHROPIC_API_KEY set) for Claude-generated conjectures
```

### All targets

| Target | Pathway | What it says | Found by |
| --- | --- | --- | --- |
| `jacobi_ring` | foundations | Jacobi identity for commutators (algebra behind the Bianchi identity) | engine search |
| `holonomy_gauge` | foundations | Lattice Wilson loops transform by conjugation under gauge transformations | engine search |
| `two_site_gap` | foundations | Two-site lattice: energy gap 2 above the vacuum | engine search |
| `three_site_gap` | foundations | Three-site lattice: energy gap 3 | engine search |
| `massive_uniform_gap` | foundations | Massive lattice free field: gap ≥ m², uniform in lattice size | engine search |
| `z2_link_square` | finite groups | Z₂ link variables square to one | engine search |
| `gaps_can_close` | foundations | Positive gaps at every size do not give a uniform gap | AI-assisted |
| `massless_gap_closes` | foundations | Massless lattice field: a step profile has gradient energy 2/(M+1), so the gap closes | AI-assisted |
| `gap_criterion_discrete` | formal route | One common decay rate forces a spectral gap | AI-assisted |
| `contraction_decay` | formal route | Transfer-matrix contraction gives geometric decay | AI-assisted |
| `gap_from_contraction` | formal route | Contraction q < 1 gives gap −log(q)/τ > 0 | AI-assisted |
| `pow_eq_exp_log` | formal route | qⁿ = exp(n log q) | AI-assisted |
| `scale_split_uniform_gap` | RG + strong coupling | Uniform bound past one scale plus finitely many scales gives a uniform gap | AI-assisted |
| `polymer_series_bound` | cluster expansion | Toy polymer series converges with explicit bound | AI-assisted |
| `poincare_variance_decay` | stochastic quantization | Poincaré-type contraction gives exponential variance decay | AI-assisted |
| `holonomy_gauge_abelian` | finite groups | Abelian Wilson loops are exactly gauge invariant | AI-assisted |
| `haar_left_invariant` | finite groups | Haar measure on a finite group is translation invariant | AI-assisted |
| `elitzur_mechanism` | confinement | Sign-flipping observables have zero expectation | AI-assisted |
| `z2_plaquette_expectation` | confinement | ⟨u⟩ = tanh β for one Z₂ plaquette | AI-assisted |
| `z2_wilson_loop_area_law` | confinement | ⟨W⟩ = (tanh β)^A in 2D Z₂ gauge theory | AI-assisted |
| `z2_string_tension_pos` | confinement | σ = −log tanh β > 0 for all β > 0 | AI-assisted |
| `z2_area_law_exponential` | confinement | ⟨W⟩ = exp(−σA) | AI-assisted |
| `z2_transfer_vacuum` | confinement | Vacuum eigenvalue 2 cosh β | AI-assisted |
| `z2_transfer_excited` | confinement | Excited eigenvalue 2 sinh β | AI-assisted |
| `z2_transfer_spectrum` | confinement | Spectrum is exactly {2 cosh β, 2 sinh β} | AI-assisted |
| `z2_transfer_iterate` | confinement | (2 sinh β)ⁿ decay of excited states | AI-assisted |
| `z2_transfer_gap` | confinement | 0 < 2 sinh β < 2 cosh β for β > 0 | AI-assisted |
| `z2_mass_gap` | confinement | Mass gap m = −log tanh β > 0 at every coupling | AI-assisted |
| `complete_graph_gap_all` | foundations | Complete-graph gap is n for every n | AI-assisted (from conjecture mode) |

## Authorship

Designed and directed by **Andrew Bulata**: the research programme, the choice of
pathways and targets, the engine's architecture, and the decisions about what to prove
next. Proofs were developed with AI assistance (Claude) and every one is checked by Lean,
which is the only judge of correctness in this repository.

## Related work

**[mrdouglasny/lgt](https://github.com/mrdouglasny/lgt)** (Michael R. Douglas and Fred
Rajasekaran) formalizes in Lean 4 a strong-coupling **mass gap** for U(n) Wilson lattice
gauge theory on (ℤ/Nℤ)^d, d ≥ 2, by the Dobrushin uniqueness method: exponential decay of
plaquette correlations for β < 1/(32n(d−1)), with only Lean's standard axioms. That result
predates the strong-coupling work here and covers more gauge groups.

This repository takes a complementary route: the high-temperature (surface) expansion,
polymer cancellation, and lattice animals, aimed at **confinement** (the Wilson-loop area
law) rather than the mass gap. Where results overlap, theirs came first.

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

# with Claude proposing tactics, whole proofs, and intermediate lemmas
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
