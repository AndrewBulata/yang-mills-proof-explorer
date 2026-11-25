/-
  Verified.lean: every proof in this file is checked by Lean 4 against Mathlib.
  Part A closes the 10 targets the first engine run left open.
  Part B: Haar invariance, the Elitzur mechanism, and the exact area law of 2D Z₂ gauge theory.
  Part C: transfer-matrix spectrum and mass gap of 2D Z₂ gauge theory at every coupling.
  Part D: the complete-graph gap for every n, generalised from conjecture-mode results.
  Part E: high-temperature (strong-coupling) expansion of Z₂ lattice gauge theory on any
          finite lattice in any dimension, Wilson-loop positivity, and a finite-volume
          area bound, specialised to the 4D hypercubic lattice.
  Part F: polymer cancellation and a volume-uniform strong-coupling area law, any dimension,
          given two combinatorial inputs (surface splitting and a c^k count).
  Part G: the splitting map constructed explicitly for any lattice (the part of a surface
          connected to the loop), so the area law needs only minimal area and a count of
          connected attached surfaces.
  Part H: lattice animals in any bounded-degree graph: at most Δ^(2k) connected sets of
          size k + 1 contain a given vertex.
  Axioms used: only propext, Classical.choice, Quot.sound (Lean's standard three).
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Group
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Int.Order.Units
import Mathlib.Tactic.GCongr
open BigOperators

namespace YM

def gaugeTransform {G X : Type*} [Group G] (g : X → G) (U : X → X → G) : X → X → G :=
  fun x y => g x * U x y * (g y)⁻¹

structure Plaquette (X : Type*) where
  a : X
  b : X
  c : X
  d : X

def holonomy {G X : Type*} [Group G] (U : X → X → G) (p : Plaquette X) : G :=
  U p.a p.b * U p.b p.c * U p.c p.d * U p.d p.a

end YM
open YM
/-! ## Part A: the ten targets left open by the first run -/

theorem holonomy_gauge {G X : Type*} [Group G] (g : X → G) (U : X → X → G) (p : Plaquette X) :
    holonomy (gaugeTransform g U) p = g p.a * holonomy U p * (g p.a)⁻¹ := by
  unfold holonomy gaugeTransform
  group

theorem gaps_can_close : ∃ Δ : ℕ → ℝ, (∀ L, 0 < Δ L) ∧ ¬ ∃ m > 0, ∀ L, m ≤ Δ L := by
  refine ⟨fun L => 1 / ((L : ℝ) + 1), fun L => by positivity, ?_⟩
  rintro ⟨m, hm, h⟩
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hm
  have hN' : m ≤ 1 / ((N : ℝ) + 1) := h N
  linarith

theorem contraction_decay (v : ℕ → ℝ) (q : ℝ) (hq : 0 ≤ q) (h : ∀ n, v (n + 1) ≤ q * v n) :
    ∀ n, v n ≤ q ^ n * v 0 := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
    calc v (k + 1) ≤ q * v k := h k
      _ ≤ q * (q ^ k * v 0) := mul_le_mul_of_nonneg_left ih hq
      _ = q ^ (k + 1) * v 0 := by ring

theorem gap_from_contraction (q τ : ℝ) (hq : 0 < q) (hq1 : q < 1) (hτ : 0 < τ) :
    0 < -Real.log q / τ :=
  div_pos (neg_pos.mpr (Real.log_neg hq hq1)) hτ

theorem pow_eq_exp_log (q : ℝ) (hq : 0 < q) (n : ℕ) : q ^ n = Real.exp ((n : ℝ) * Real.log q) := by
  rw [← Real.log_pow, Real.exp_log (pow_pos hq n)]

theorem scale_split_uniform_gap (Δ : ℕ → ℝ) (hpos : ∀ L, 0 < Δ L) (m : ℝ) (hm : 0 < m) (L₀ : ℕ)
    (h : ∀ L ≥ L₀, m ≤ Δ L) : ∃ m' > 0, ∀ L, m' ≤ Δ L := by
  have aux : ∀ K : ℕ, ∃ m0 > 0, ∀ L < K, m0 ≤ Δ L := by
    intro K
    induction K with
    | zero => exact ⟨1, one_pos, fun L hL => absurd hL (Nat.not_lt_zero _)⟩
    | succ k ih =>
      obtain ⟨m0, hm0, hk⟩ := ih
      refine ⟨min m0 (Δ k), lt_min hm0 (hpos k), fun L hL => ?_⟩
      rcases (by omega : L < k ∨ L = k) with hL | hL
      · exact (min_le_left _ _).trans (hk L hL)
      · subst hL; exact min_le_right _ _
  obtain ⟨m0, hm0, hk⟩ := aux L₀
  refine ⟨min m0 m, lt_min hm0 hm, fun L => ?_⟩
  by_cases hL : L < L₀
  · exact (min_le_left _ _).trans (hk L hL)
  · exact (min_le_right _ _).trans (h L (not_lt.mp hL))

theorem polymer_series_bound (z : ℝ) (hz : |z| < 1) (N : ℕ) :
    ∑ n ∈ Finset.range N, |z| ^ n ≤ 1 / (1 - |z|) := by
  have h0 : 0 ≤ |z| := abs_nonneg z
  have h1 : 0 < 1 - |z| := by linarith
  have key : ∀ K : ℕ, (∑ n ∈ Finset.range K, |z| ^ n) * (1 - |z|) = 1 - |z| ^ K := by
    intro K
    induction K with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ, add_mul, ih]; ring
  rw [le_div_iff₀ h1, key N]
  have : 0 ≤ |z| ^ N := pow_nonneg h0 N
  linarith

theorem poincare_variance_decay (V : ℕ → ℝ) (lam : ℝ) (_hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (h : ∀ n, V (n + 1) ≤ (1 - lam) * V n) : ∀ n, V n ≤ (1 - lam) ^ n * V 0 :=
  contraction_decay V (1 - lam) (by linarith) h

theorem holonomy_gauge_abelian {G X : Type*} [CommGroup G] (g : X → G) (U : X → X → G)
    (p : Plaquette X) : holonomy (gaugeTransform g U) p = holonomy U p := by
  rw [holonomy_gauge, mul_comm (g p.a), mul_assoc, mul_inv_cancel, mul_one]

theorem gap_criterion_discrete (lam w : ℕ → ℝ) (n : ℕ) (hw : ∀ i, 0 ≤ w i) (C m : ℝ)
    (h : ∀ t : ℝ, 1 ≤ t → ∑ i ∈ Finset.range n, w i * Real.exp (-t * lam i) ≤ C * Real.exp (-m * t)) :
    ∀ i < n, 0 < w i → m ≤ lam i := by
  intro i hi hwi
  by_contra hlt
  push Not at hlt
  have hd : 0 < m - lam i := by linarith
  have hwd : 0 < w i * (m - lam i) := mul_pos hwi hd
  let t : ℝ := max 1 (C / (w i * (m - lam i)) + 1)
  have ht1 : 1 ≤ t := le_max_left _ _
  have hbig : C / (w i * (m - lam i)) + 1 ≤ t := le_max_right _ _
  have hsingle : w i * Real.exp (-t * lam i) ≤ ∑ j ∈ Finset.range n, w j * Real.exp (-t * lam j) :=
    Finset.single_le_sum (f := fun j => w j * Real.exp (-t * lam j))
      (fun j _ => mul_nonneg (hw j) (Real.exp_pos _).le) (Finset.mem_range.mpr hi)
  have key := hsingle.trans (h t ht1)
  have e1 : Real.exp (-t * lam i) = Real.exp (-m * t) * Real.exp (t * (m - lam i)) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [e1] at key
  have hexp : 0 < Real.exp (-m * t) := Real.exp_pos _
  have key2 : w i * Real.exp (t * (m - lam i)) ≤ C := by
    have h3 : Real.exp (-m * t) * (w i * Real.exp (t * (m - lam i))) ≤ Real.exp (-m * t) * C := by
      linarith [key]
    exact le_of_mul_le_mul_left h3 hexp
  have hlin : t * (m - lam i) + 1 ≤ Real.exp (t * (m - lam i)) := Real.add_one_le_exp _
  have hC : C < w i * (m - lam i) * t := by
    have h1 : C / (w i * (m - lam i)) < t := by linarith
    have := (div_lt_iff₀ hwd).mp h1
    linarith
  have h4 : w i * (t * (m - lam i) + 1) ≤ w i * Real.exp (t * (m - lam i)) :=
    mul_le_mul_of_nonneg_left hlin hwi.le
  nlinarith

/-- Massless lattice field: a step profile (+c on the left half, -c on the right) has
mean zero, unit norm, and gradient energy 2/(M+1), which can be made arbitrarily small. -/
theorem massless_gap_closes : ∀ ε > 0, ∃ N : ℕ, ∃ v : ℕ → ℝ,
    (∑ i ∈ Finset.range N, v i = 0) ∧ (∑ i ∈ Finset.range N, v i ^ 2 = 1) ∧
    ∑ i ∈ Finset.range (N - 1), (v (i + 1) - v i) ^ 2 < ε := by
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_one_div_lt (half_pos hε)
  set K : ℕ := M + 1 with hK
  have hKpos : (0 : ℝ) < K := by positivity
  set c : ℝ := Real.sqrt (1 / (2 * K)) with hc
  have hc2 : c ^ 2 = 1 / (2 * K) := by
    rw [hc, Real.sq_sqrt]; positivity
  let v : ℕ → ℝ := fun i => if i < K then c else -c
  refine ⟨K + K, v, ?_, ?_, ?_⟩
  · rw [Finset.sum_range_add]
    have h1 : ∑ i ∈ Finset.range K, v i = ∑ i ∈ Finset.range K, c :=
      Finset.sum_congr rfl (fun i hi => by simp [v, Finset.mem_range.mp hi])
    have h2 : ∑ i ∈ Finset.range K, v (K + i) = ∑ i ∈ Finset.range K, -c :=
      Finset.sum_congr rfl (fun i _ => by simp [v])
    rw [h1, h2]; simp
  · rw [Finset.sum_range_add]
    have h1 : ∑ i ∈ Finset.range K, v i ^ 2 = ∑ i ∈ Finset.range K, c ^ 2 :=
      Finset.sum_congr rfl (fun i hi => by simp [v, Finset.mem_range.mp hi])
    have h2 : ∑ i ∈ Finset.range K, v (K + i) ^ 2 = ∑ i ∈ Finset.range K, c ^ 2 :=
      Finset.sum_congr rfl (fun i _ => by simp [v])
    rw [h1, h2, hc2]; simp; field_simp; ring
  · have hN : K + K - 1 = M + (M + 1) := by omega
    rw [hN, Finset.sum_range_add, Finset.sum_range_succ']
    have h1 : ∑ i ∈ Finset.range M, (v (i + 1) - v i) ^ 2 = 0 :=
      Finset.sum_eq_zero (fun i hi => by
        have := Finset.mem_range.mp hi
        simp [v, show i + 1 < K by omega, show i < K by omega])
    have h2 : ∑ i ∈ Finset.range M, (v (M + (i + 1) + 1) - v (M + (i + 1))) ^ 2 = 0 :=
      Finset.sum_eq_zero (fun i _ => by
        simp [v, show ¬ (M + (i + 1) + 1 < K) by omega, show ¬ (M + (i + 1) < K) by omega])
    have h3 : (v (M + 0 + 1) - v (M + 0)) ^ 2 = 4 * c ^ 2 := by
      simp [v, show ¬ (M + 1 < K) by omega, show M < K by omega]; ring
    rw [h1, h2, h3, hc2]
    have : (1 : ℝ) / ((M : ℝ) + 1) < ε / 2 := hM
    have hK' : (K : ℝ) = M + 1 := by simp [hK]
    rw [hK']
    have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
    calc (0 : ℝ) + (0 + 4 * (1 / (2 * ((M : ℝ) + 1)))) = 2 * (1 / ((M : ℝ) + 1)) := by
          field_simp; ring
      _ < 2 * (ε / 2) := by linarith
      _ = ε := by ring

/-! ## Part B: new results -/

/-- Invariance of the counting (Haar) measure on a finite gauge group under left translation. -/
theorem haar_left_invariant {G : Type*} [Group G] [Fintype G] (f : G → ℝ) (z : G) :
    ∑ x, f (z * x) = ∑ x, f x :=
  Fintype.sum_equiv (Equiv.mulLeft z) _ _ (fun _ => rfl)

/-- The mechanism behind Elitzur's theorem: if the weight is invariant under a symmetry
`x ↦ z x` and the observable flips sign under it, its (unnormalised) expectation vanishes. -/
theorem elitzur_mechanism {G : Type*} [Group G] [Fintype G] (w O : G → ℝ) (z : G)
    (hw : ∀ x, w (z * x) = w x) (hO : ∀ x, O (z * x) = -O x) : ∑ x, w x * O x = 0 := by
  have hS : ∑ x, w (z * x) * O (z * x) = ∑ x, w x * O x :=
    Fintype.sum_equiv (Equiv.mulLeft z) _ _ (fun _ => rfl)
  have h2 : ∑ x, w (z * x) * O (z * x) = -∑ x, w x * O x := by
    simp only [hw, hO, mul_neg, Finset.sum_neg_distrib]
  linarith

/-- Z₂ spin: true ↦ +1, false ↦ -1. -/
def spin (b : Bool) : ℝ := if b then 1 else -1

/-- One Z₂ plaquette with Boltzmann weight exp(β u): ⟨u⟩ = tanh β. -/
theorem z2_plaquette_expectation (β : ℝ) :
    (∑ b : Bool, spin b * Real.exp (β * spin b)) / (∑ b : Bool, Real.exp (β * spin b)) =
      Real.tanh β := by
  simp only [Fintype.sum_bool, spin, ite_true, ite_false, Bool.false_eq_true]
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq, Real.cosh_eq]
  have : 0 < Real.exp β + Real.exp (-β) := by positivity
  field_simp
  ring_nf

/-- **Exact area law for 2D Z₂ lattice gauge theory.** After the standard 2D gauge fixing,
the A plaquettes inside a Wilson loop are independent Z₂ variables, and the loop is their
product. The expectation factorises: ⟨W⟩ = (tanh β)^A. -/
theorem z2_wilson_loop_area_law (β : ℝ) (A : ℕ) :
    (∑ s : Fin A → Bool, ∏ i, (spin (s i) * Real.exp (β * spin (s i)))) /
      (∑ s : Fin A → Bool, ∏ i, Real.exp (β * spin (s i))) = Real.tanh β ^ A := by
  rw [← Fintype.prod_sum (fun (_ : Fin A) (b : Bool) => spin b * Real.exp (β * spin b)),
    ← Fintype.prod_sum (fun (_ : Fin A) (b : Bool) => Real.exp (β * spin b))]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← div_pow, z2_plaquette_expectation]

/-- The string tension σ = -log tanh β of 2D Z₂ gauge theory is strictly positive at every
coupling β > 0: confinement holds at all couplings in two dimensions. -/
theorem z2_string_tension_pos (β : ℝ) (hβ : 0 < β) : 0 < -Real.log (Real.tanh β) := by
  have h0 : 0 < Real.tanh β := by
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq]
    have : Real.exp (-β) < Real.exp β := Real.exp_lt_exp.mpr (by linarith)
    exact div_pos (by linarith) (Real.cosh_pos β)
  exact neg_pos.mpr (Real.log_neg h0 (Real.tanh_lt_one β))

/-- Area law in exponential form: ⟨W⟩ = exp(-σ A) with σ = -log tanh β. -/
theorem z2_area_law_exponential (β : ℝ) (hβ : 0 < β) (A : ℕ) :
    Real.tanh β ^ A = Real.exp (-(-Real.log (Real.tanh β)) * A) := by
  have h0 : 0 < Real.tanh β := by
    have := z2_string_tension_pos β hβ
    rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq]
    have : Real.exp (-β) < Real.exp β := Real.exp_lt_exp.mpr (by linarith)
    exact div_pos (by linarith) (Real.cosh_pos β)
  rw [neg_neg, mul_comm, ← Real.log_pow, Real.exp_log (pow_pos h0 A)]


/-! ## Part C: transfer-matrix mass gap for 2D Z₂ gauge theory

In axial gauge, 2D Z₂ lattice gauge theory on a strip reduces to a chain of independent
plaquette spins, and its transfer matrix acts on functions of one Z₂ variable as
`(T f)(s) = Σ_{s'} exp(β s s') f(s')`. This section computes its full spectrum and proves
the gap above the vacuum: the Yang–Mills mass-gap question, answered exactly in a model
where it can be. -/

/-- The Z₂ transfer matrix kernel. -/
noncomputable def transferZ2 (β : ℝ) (s s' : Bool) : ℝ := Real.exp (β * spin s * spin s')

/-- The transfer matrix acting on wavefunctions `f : Bool → ℝ`. -/
noncomputable def applyT (β : ℝ) (f : Bool → ℝ) : Bool → ℝ := fun s => ∑ s', transferZ2 β s s' * f s'

/-- The vacuum (constant wavefunction) has eigenvalue 2 cosh β. -/
theorem z2_transfer_vacuum (β : ℝ) : applyT β (fun _ => 1) = fun _ => 2 * Real.cosh β := by
  funext s
  cases s <;> simp [applyT, transferZ2, spin, Real.cosh_eq] <;> ring

/-- Every state orthogonal to the vacuum is an eigenvector with eigenvalue 2 sinh β. -/
theorem z2_transfer_excited (β : ℝ) (f : Bool → ℝ) (hf : f true + f false = 0) :
    applyT β f = fun s => 2 * Real.sinh β * f s := by
  have hff : f false = -f true := by linarith
  funext s
  cases s <;> simp [applyT, transferZ2, spin, Real.sinh_eq, hff] <;> ring

/-- Full spectral decomposition: T acts as 2 cosh β on the vacuum component and as
2 sinh β on the orthogonal component. The spectrum is exactly {2 cosh β, 2 sinh β}. -/
theorem z2_transfer_spectrum (β : ℝ) (f : Bool → ℝ) :
    applyT β f = fun s => 2 * Real.cosh β * ((f true + f false) / 2) +
      2 * Real.sinh β * ((f true - f false) / 2) * spin s := by
  funext s
  cases s <;> simp [applyT, transferZ2, spin, Real.sinh_eq, Real.cosh_eq] <;> ring

/-- Iterating: n time steps multiply an excited state by (2 sinh β)ⁿ. -/
theorem z2_transfer_iterate (β : ℝ) (f : Bool → ℝ) (hf : f true + f false = 0) (n : ℕ) :
    (applyT β)^[n] f = fun s => (2 * Real.sinh β) ^ n * f s := by
  induction n with
  | zero => funext s; simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    rw [z2_transfer_excited β _ (by rw [← mul_add, hf, mul_zero])]
    funext s
    ring

/-- The gap: for β > 0 the excited eigenvalue is positive and strictly below the vacuum's,
with ratio tanh β. -/
theorem z2_transfer_gap (β : ℝ) (hβ : 0 < β) :
    0 < 2 * Real.sinh β ∧ 2 * Real.sinh β < 2 * Real.cosh β ∧
      2 * Real.sinh β / (2 * Real.cosh β) = Real.tanh β := by
  have he : Real.exp (-β) < Real.exp β := Real.exp_lt_exp.mpr (by linarith)
  have hp : 0 < Real.exp (-β) := Real.exp_pos _
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.sinh_eq]; linarith
  · rw [Real.sinh_eq, Real.cosh_eq]; linarith
  · rw [Real.tanh_eq_sinh_div_cosh]
    have hc : 0 < Real.cosh β := Real.cosh_pos β
    field_simp

/-- **Mass gap of 2D Z₂ lattice gauge theory at every coupling.** There is m > 0 such that
every state orthogonal to the vacuum decays, relative to the vacuum, as exp(-m n) after
n steps of Euclidean time. Explicitly m = -log tanh β. -/
theorem z2_mass_gap (β : ℝ) (hβ : 0 < β) :
    ∃ m > 0, ∀ n : ℕ, ∀ f : Bool → ℝ, f true + f false = 0 → ∀ s,
      (applyT β)^[n] f s = (2 * Real.cosh β) ^ n * Real.exp (-m * n) * f s := by
  refine ⟨-Real.log (Real.tanh β), z2_string_tension_pos β hβ, fun n f hf s => ?_⟩
  rw [z2_transfer_iterate β f hf n, ← z2_area_law_exponential β hβ n,
    Real.tanh_eq_sinh_div_cosh, ← mul_pow]
  have hc : 0 < Real.cosh β := Real.cosh_pos β
  have e : 2 * Real.cosh β * (Real.sinh β / Real.cosh β) = 2 * Real.sinh β := by
    field_simp
  rw [e]


/-! ## Part D: generalisation suggested by conjecture mode

Conjecture mode proved `complete_gap_n` for n = 3, 4, and 5, and refuted the constant n + 1.
This is the statement for every n: on the complete graph with n sites, every mean-zero
state has energy exactly n times its norm, so the gap is n (each ordered pair counted twice). -/

theorem complete_graph_gap_all (n : ℕ) (v : Fin n → ℝ) (h : ∑ i, v i = 0) :
    ∑ i, ∑ j, (v i - v j) ^ 2 = 2 * n * ∑ i, v i ^ 2 := by
  have e : ∀ i j, (v i - v j) ^ 2 = v i ^ 2 + v j ^ 2 - 2 * v i * v j := fun i j => by ring
  simp only [e, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have h1 : ∑ i : Fin n, ∑ j : Fin n, 2 * v i * v j = 0 := by
    simp only [← Finset.mul_sum, h, mul_zero, Finset.sum_const_zero]
  rw [h1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
  ring


/-! ## Part E: high-temperature expansion of Z₂ lattice gauge theory, any dimension

A lattice is abstract here: a finite set of links `L`, a finite set of plaquettes `P`, and
for each plaquette its boundary `bd p : Finset L`. The hypercubic lattice in d dimensions
(defined at the end, d = 4 included) is one instance.

Main result (`numer_expand`): for every Wilson loop C,

  Σ_U W_C(U) e^{β Σ_p u_p(U)} = cosh(β)^|P| · 2^|L| · Σ_{S ⊆ P, ∂S = C} tanh(β)^|S|

so ⟨W_C⟩ is a ratio of sums over plaquette surfaces S with boundary C, weighted by
tanh(β)^|S|. This is the starting point of the Osterwalder–Seiler strong-coupling analysis. -/

namespace HTE

set_option linter.unusedSectionVars false

variable {L P : Type} [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]

/-- Plaquette variable: product of the Z₂ link spins around its boundary. -/
def plaq (bd : P → Finset L) (U : L → Bool) (p : P) : ℝ := ∏ l ∈ bd p, spin (U l)

/-- Wilson-action Boltzmann weight. -/
noncomputable def weight (bd : P → Finset L) (β : ℝ) (U : L → Bool) : ℝ :=
  ∏ p, Real.exp (β * plaq bd U p)

/-- Partition function. -/
noncomputable def Z (bd : P → Finset L) (β : ℝ) : ℝ := ∑ U : L → Bool, weight bd β U

/-- Wilson loop along a set of links C. -/
def wilson (C : Finset L) (U : L → Bool) : ℝ := ∏ l ∈ C, spin (U l)

/-- Unnormalised Wilson-loop expectation. ⟨W_C⟩ = numer / Z. -/
noncomputable def numer (bd : P → Finset L) (β : ℝ) (C : Finset L) : ℝ :=
  ∑ U : L → Bool, wilson C U * weight bd β U

/-- How many times link l occurs in C together with the boundaries of the plaquettes in S. -/
def mult (bd : P → Finset L) (C : Finset L) (S : Finset P) (l : L) : ℕ :=
  (if l ∈ C then 1 else 0) + (S.filter (fun p => l ∈ bd p)).card

/-- S has boundary C (mod 2): every link occurs an even number of times in C and ∂S. -/
abbrev HasBoundary (bd : P → Finset L) (S : Finset P) (C : Finset L) : Prop :=
  ∀ l, Even (mult bd C S l)

lemma spin_pm (b : Bool) : spin b = 1 ∨ spin b = -1 := by cases b <;> simp [spin]

lemma sum_spin_pow (k : ℕ) : ∑ b : Bool, spin b ^ k = if Even k then 2 else 0 := by
  rw [Fintype.sum_bool]
  rcases Nat.even_or_odd k with h | h
  · simp [spin, h.neg_one_pow, h]; norm_num
  · simp [spin, h.neg_one_pow, Nat.not_even_iff_odd.mpr h]

/-- Character orthogonality on Z₂^L: the link sum kills every odd power. -/
lemma orthogonality (m : L → ℕ) :
    ∑ U : L → Bool, ∏ l, spin (U l) ^ m l = if ∀ l, Even (m l) then 2 ^ Fintype.card L else 0 := by
  rw [← Fintype.prod_sum (fun (l : L) (b : Bool) => spin b ^ m l)]
  simp only [sum_spin_pow]
  split_ifs with h
  · rw [Finset.prod_congr rfl (fun l _ => if_pos (h l)), Finset.prod_const, Finset.card_univ]
  · push Not at h
    obtain ⟨l, hl⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ l) (if_neg (Nat.not_even_iff_odd.mpr hl))

/-- The integrand of the expansion as a single product of link spins. -/
lemma integrand (bd : P → Finset L) (C : Finset L) (S : Finset P) (U : L → Bool) :
    wilson C U * ∏ p ∈ S, plaq bd U p = ∏ l, spin (U l) ^ mult bd C S l := by
  have hw : wilson C U = ∏ l, spin (U l) ^ (if l ∈ C then 1 else 0) := by
    unfold wilson
    rw [← Fintype.prod_ite_mem]
    refine Finset.prod_congr rfl (fun l _ => ?_)
    split_ifs <;> simp
  have hp : ∏ p ∈ S, plaq bd U p = ∏ l, spin (U l) ^ (S.filter (fun p => l ∈ bd p)).card := by
    unfold plaq
    simp only [← Fintype.prod_ite_mem (bd _)]
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl (fun l _ => ?_)
    rw [← Finset.prod_const, Finset.prod_filter]
  rw [hw, hp, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun l _ => ?_)
  rw [← pow_add]
  rfl

lemma plaq_pm (bd : P → Finset L) (U : L → Bool) (p : P) :
    plaq bd U p = 1 ∨ plaq bd U p = -1 := by
  unfold plaq
  refine Finset.prod_induction _ (fun x => x = 1 ∨ x = -1) ?_ (Or.inl rfl)
    (fun l _ => spin_pm (U l))
  rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num

/-- e^{βx} = cosh β (1 + x tanh β) for x = ±1: the key identity of the expansion. -/
lemma exp_pm (β x : ℝ) (hx : x = 1 ∨ x = -1) :
    Real.exp (β * x) = Real.cosh β * (1 + Real.tanh β * x) := by
  have hc : Real.cosh β ≠ 0 := (Real.cosh_pos β).ne'
  have key : Real.cosh β * (1 + Real.tanh β * x) = Real.cosh β + Real.sinh β * x := by
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp
  rw [key]
  rcases hx with rfl | rfl
  · rw [mul_one, mul_one, Real.cosh_add_sinh]
  · rw [show β * (-1) = -β by ring, mul_neg_one, ← sub_eq_add_neg, Real.cosh_sub_sinh]

/-- The Boltzmann weight expanded over plaquette subsets. -/
lemma weight_expand (bd : P → Finset L) (β : ℝ) (U : L → Bool) :
    weight bd β U = Real.cosh β ^ Fintype.card P *
      ∑ S ∈ (Finset.univ : Finset P).powerset, Real.tanh β ^ S.card * ∏ p ∈ S, plaq bd U p := by
  unfold weight
  rw [Finset.prod_congr rfl (fun p _ => exp_pm β _ (plaq_pm bd U p)), Finset.prod_mul_distrib,
    Finset.prod_const, Finset.card_univ, Finset.prod_one_add]
  congr 1
  refine Finset.sum_congr rfl (fun S _ => ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const]

/-- **High-temperature (strong-coupling) expansion of Wilson loops, any lattice.** -/
theorem numer_expand (bd : P → Finset L) (β : ℝ) (C : Finset L) :
    numer bd β C = Real.cosh β ^ Fintype.card P * 2 ^ Fintype.card L *
      ∑ S ∈ (Finset.univ : Finset P).powerset.filter (fun S => HasBoundary bd S C),
        Real.tanh β ^ S.card := by
  unfold numer
  simp only [weight_expand]
  set c := Real.cosh β ^ Fintype.card P
  set t := Real.tanh β
  calc ∑ U : L → Bool, wilson C U * (c * ∑ S ∈ (Finset.univ : Finset P).powerset,
          t ^ S.card * ∏ p ∈ S, plaq bd U p)
      = ∑ U : L → Bool, ∑ S ∈ (Finset.univ : Finset P).powerset,
          c * t ^ S.card * (wilson C U * ∏ p ∈ S, plaq bd U p) := by
        refine Finset.sum_congr rfl (fun U _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun S _ => ?_)
        ring
    _ = ∑ S ∈ (Finset.univ : Finset P).powerset, ∑ U : L → Bool,
          c * t ^ S.card * (wilson C U * ∏ p ∈ S, plaq bd U p) := Finset.sum_comm
    _ = ∑ S ∈ (Finset.univ : Finset P).powerset,
          c * t ^ S.card * (if HasBoundary bd S C then 2 ^ Fintype.card L else 0) := by
        refine Finset.sum_congr rfl (fun S _ => ?_)
        rw [← Finset.mul_sum]
        simp only [integrand]
        rw [orthogonality]
    _ = c * 2 ^ Fintype.card L * ∑ S ∈ (Finset.univ : Finset P).powerset.filter
          (fun S => HasBoundary bd S C), t ^ S.card := by
        rw [Finset.sum_filter, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun S _ => ?_)
        split_ifs <;> ring

/-- The partition function: a sum over closed plaquette surfaces. -/
theorem Z_expand (bd : P → Finset L) (β : ℝ) :
    Z bd β = Real.cosh β ^ Fintype.card P * 2 ^ Fintype.card L *
      ∑ S ∈ (Finset.univ : Finset P).powerset.filter (fun S => HasBoundary bd S ∅),
        Real.tanh β ^ S.card := by
  rw [← numer_expand]
  unfold Z numer
  simp [wilson]

/-- Surface sums. -/
noncomputable def surf (bd : P → Finset L) (β : ℝ) (C : Finset L) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset P).powerset.filter (fun S => HasBoundary bd S C), Real.tanh β ^ S.card

/-- ⟨W_C⟩ as a ratio of surface sums: open surfaces bounded by C over closed surfaces. -/
theorem wilson_ratio (bd : P → Finset L) (β : ℝ) (C : Finset L) :
    numer bd β C / Z bd β = surf bd β C / surf bd β ∅ := by
  rw [numer_expand, Z_expand]
  have h1 : Real.cosh β ^ Fintype.card P * 2 ^ Fintype.card L ≠ 0 := by
    have := Real.cosh_pos β; positivity
  unfold surf
  rw [mul_div_mul_left _ _ h1]

lemma tanh_nonneg' (β : ℝ) (hβ : 0 ≤ β) : 0 ≤ Real.tanh β := by
  rw [Real.tanh_eq_sinh_div_cosh, Real.sinh_eq]
  have : Real.exp (-β) ≤ Real.exp β := Real.exp_le_exp.mpr (by linarith)
  exact div_nonneg (by linarith) (Real.cosh_pos β).le

lemma surf_nonneg (bd : P → Finset L) (β : ℝ) (hβ : 0 ≤ β) (C : Finset L) : 0 ≤ surf bd β C :=
  Finset.sum_nonneg (fun S _ => pow_nonneg (tanh_nonneg' β hβ) _)

/-- The empty surface is closed, so the closed-surface sum is at least 1. -/
lemma surf_closed_ge_one (bd : P → Finset L) (β : ℝ) (hβ : 0 ≤ β) : 1 ≤ surf bd β ∅ := by
  unfold surf
  have hmem : (∅ : Finset P) ∈ (Finset.univ : Finset P).powerset.filter
      (fun S => HasBoundary bd S ∅) := by
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.empty_subset, true_and]
    intro l
    simp [mult]
  have := Finset.single_le_sum (f := fun S : Finset P => Real.tanh β ^ S.card)
    (fun S _ => pow_nonneg (tanh_nonneg' β hβ) _) hmem
  simpa using this

/-- **Positivity of Wilson loops** for β ≥ 0 (a Griffiths-type inequality), any lattice. -/
theorem wilson_nonneg (bd : P → Finset L) (β : ℝ) (hβ : 0 ≤ β) (C : Finset L) :
    0 ≤ numer bd β C / Z bd β := by
  rw [wilson_ratio]
  exact div_nonneg (surf_nonneg bd β hβ C) (surf_nonneg bd β hβ ∅)

/-- ⟨W_C⟩ is bounded by the sum over surfaces with boundary C. -/
theorem wilson_le_surf (bd : P → Finset L) (β : ℝ) (hβ : 0 ≤ β) (C : Finset L) :
    numer bd β C / Z bd β ≤ surf bd β C := by
  rw [wilson_ratio]
  exact div_le_self (surf_nonneg bd β hβ C) (surf_closed_ge_one bd β hβ)

/-- **Finite-volume area law at strong coupling, any dimension.** If every surface bounded by
C has at least A plaquettes, then ⟨W_C⟩ ≤ 2^|P| · tanh(β)^A. The factor 2^|P| depends on the
volume; removing it needs the polymer (cluster) expansion, the next milestone. -/
theorem area_bound (bd : P → Finset L) (β : ℝ) (hβ : 0 ≤ β) (C : Finset L) (A : ℕ)
    (hA : ∀ S : Finset P, HasBoundary bd S C → A ≤ S.card) :
    numer bd β C / Z bd β ≤ 2 ^ Fintype.card P * Real.tanh β ^ A := by
  refine (wilson_le_surf bd β hβ C).trans ?_
  have ht0 := tanh_nonneg' β hβ
  have ht1 : Real.tanh β ≤ 1 := (Real.tanh_lt_one β).le
  unfold surf
  calc ∑ S ∈ (Finset.univ : Finset P).powerset.filter (fun S => HasBoundary bd S C),
        Real.tanh β ^ S.card
      ≤ ∑ S ∈ (Finset.univ : Finset P).powerset.filter (fun S => HasBoundary bd S C),
          Real.tanh β ^ A := by
        refine Finset.sum_le_sum (fun S hS => ?_)
        exact pow_le_pow_of_le_one ht0 ht1 (hA S (Finset.mem_filter.mp hS).2)
    _ ≤ ∑ S ∈ (Finset.univ : Finset P).powerset, Real.tanh β ^ A :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => pow_nonneg ht0 _)
    _ = 2 ^ Fintype.card P * Real.tanh β ^ A := by
        rw [Finset.sum_const, Finset.card_powerset, Finset.card_univ, nsmul_eq_mul]
        push_cast; ring

end HTE

/-! ### The hypercubic lattice in d dimensions (periodic, side N) -/

namespace Hypercubic

variable (d N : ℕ) [NeZero N]

abbrev Site := Fin d → ZMod N
abbrev Link := Site d N × Fin d
abbrev Plaq := Site d N × {q : Fin d × Fin d // q.1 < q.2}

/-- Unit vector in direction μ. -/
def e {d N : ℕ} (μ : Fin d) : Fin d → ZMod N := Pi.single μ 1

/-- The four boundary links of the plaquette at x in the (μ, ν) plane. -/
def bd {d N : ℕ} [NeZero N] (q : Plaq d N) : Finset (Link d N) :=
  {(q.1, q.2.1.1), (q.1 + e q.2.1.1, q.2.1.2), (q.1 + e q.2.1.2, q.2.1.1), (q.1, q.2.1.2)}

/-- The strong-coupling area bound, specialised to the 4D hypercubic lattice. -/
theorem area_bound_4d (β : ℝ) (hβ : 0 ≤ β) (C : Finset (Link 4 N)) (A : ℕ)
    (hA : ∀ S : Finset (Plaq 4 N), HTE.HasBoundary (@bd 4 N _) S C → A ≤ S.card) :
    HTE.numer (@bd 4 N _) β C / HTE.Z (@bd 4 N _) β ≤ 2 ^ Fintype.card (Plaq 4 N) * Real.tanh β ^ A :=
  HTE.area_bound (@bd 4 N _) β hβ C A hA

/-- Wilson loops are nonnegative in 4D lattice Z₂ gauge theory at any β ≥ 0. -/
theorem wilson_nonneg_4d (β : ℝ) (hβ : 0 ≤ β) (C : Finset (Link 4 N)) :
    0 ≤ HTE.numer (@bd 4 N _) β C / HTE.Z (@bd 4 N _) β :=
  HTE.wilson_nonneg (@bd 4 N _) β hβ C

end Hypercubic


/-! ## Part F: polymer cancellation and a volume-uniform area law

Part E bounds ⟨W_C⟩ by a sum over *all* surfaces bounded by C, which grows with the volume.
The polymer argument fixes this. Split every surface S with ∂S = C into the piece `comp S`
attached to C and a closed remainder S \ comp S. The closed remainders cancel against the
partition function, leaving a sum over attached surfaces only. If there are at most c^k
attached surfaces of size k, the result is an area law that does not depend on the volume.

The splitting map and the c^k count are hypotheses here: they are pure lattice combinatorics
(connected components and lattice-animal counting), the next milestone. -/

namespace HTE

set_option linter.unusedSectionVars false

variable {L P : Type} [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]

/-- **Polymer cancellation.** The closed parts of surfaces bounded by C factor out as the
partition function's surface sum. -/
theorem polymer_cancellation (bd : P → Finset L) (β : ℝ) (hβ : 0 ≤ β) (C : Finset L)
    (𝒯 : Finset (Finset P)) (comp : Finset P → Finset P)
    (h_sub : ∀ S, comp S ⊆ S)
    (h_mem : ∀ S, HasBoundary bd S C → comp S ∈ 𝒯)
    (h_closed : ∀ S, HasBoundary bd S C → HasBoundary bd (S \ comp S) ∅) :
    surf bd β C ≤ (∑ T ∈ 𝒯, Real.tanh β ^ T.card) * surf bd β ∅ := by
  have ht := tanh_nonneg' β hβ
  unfold surf
  set FC := (Finset.univ : Finset P).powerset.filter (fun S => HasBoundary bd S C)
  set F0 := (Finset.univ : Finset P).powerset.filter (fun S => HasBoundary bd S ∅)
  let φ : Finset P → Finset P × Finset P := fun S => (comp S, S \ comp S)
  let g : Finset P × Finset P → ℝ := fun x => Real.tanh β ^ x.1.card * Real.tanh β ^ x.2.card
  have hinj : Set.InjOn φ FC := by
    intro S₁ _ S₂ _ h
    have h1 : comp S₁ = comp S₂ := congrArg Prod.fst h
    have h2 : S₁ \ comp S₁ = S₂ \ comp S₂ := congrArg Prod.snd h
    calc S₁ = comp S₁ ∪ S₁ \ comp S₁ := (Finset.union_sdiff_of_subset (h_sub S₁)).symm
      _ = comp S₂ ∪ S₂ \ comp S₂ := by rw [h2, h1]
      _ = S₂ := Finset.union_sdiff_of_subset (h_sub S₂)
  have hsplit : ∀ S ∈ FC, Real.tanh β ^ S.card = g (φ S) := by
    intro S _
    simp only [g, φ]
    rw [← pow_add, add_comm, Finset.card_sdiff_add_card_eq_card (h_sub S)]
  have himg : FC.image φ ⊆ 𝒯 ×ˢ F0 := by
    intro x hx
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hx
    have hb : HasBoundary bd S C := (Finset.mem_filter.mp hS).2
    refine Finset.mem_product.mpr ⟨h_mem S hb, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), h_closed S hb⟩
  calc ∑ S ∈ FC, Real.tanh β ^ S.card = ∑ S ∈ FC, g (φ S) := Finset.sum_congr rfl hsplit
    _ = ∑ x ∈ FC.image φ, g x := (Finset.sum_image hinj).symm
    _ ≤ ∑ x ∈ 𝒯 ×ˢ F0, g x :=
        Finset.sum_le_sum_of_subset_of_nonneg himg
          (fun x _ _ => mul_nonneg (pow_nonneg ht _) (pow_nonneg ht _))
    _ = (∑ T ∈ 𝒯, Real.tanh β ^ T.card) * ∑ R ∈ F0, Real.tanh β ^ R.card := by
        rw [Finset.sum_product, Finset.sum_mul_sum]

/-- ⟨W_C⟩ is bounded by the sum over attached surfaces alone. -/
theorem wilson_le_polymer (bd : P → Finset L) (β : ℝ) (hβ : 0 ≤ β) (C : Finset L)
    (𝒯 : Finset (Finset P)) (comp : Finset P → Finset P)
    (h_sub : ∀ S, comp S ⊆ S)
    (h_mem : ∀ S, HasBoundary bd S C → comp S ∈ 𝒯)
    (h_closed : ∀ S, HasBoundary bd S C → HasBoundary bd (S \ comp S) ∅) :
    numer bd β C / Z bd β ≤ ∑ T ∈ 𝒯, Real.tanh β ^ T.card := by
  rw [wilson_ratio]
  have h1 := surf_closed_ge_one bd β hβ
  rw [div_le_iff₀ (by linarith)]
  exact polymer_cancellation bd β hβ C 𝒯 comp h_sub h_mem h_closed

/-- Geometric tail: Σ_{A ≤ k < n} r^k ≤ r^A / (1 - r). -/
lemma geom_tail (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r < 1) (A n : ℕ) :
    ∑ k ∈ Finset.range n, (if A ≤ k then r ^ k else 0) ≤ r ^ A / (1 - r) := by
  rw [← Finset.sum_filter]
  have hI : (Finset.range n).filter (fun k => A ≤ k) = Finset.Ico A n := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    tauto
  rw [hI, Finset.sum_Ico_eq_sum_range]
  simp only [pow_add, ← Finset.mul_sum]
  rw [div_eq_mul_one_div]
  have hb := polymer_series_bound r (by rw [abs_of_nonneg hr0]; exact hr1) (n - A)
  rw [abs_of_nonneg hr0] at hb
  exact mul_le_mul_of_nonneg_left hb (pow_nonneg hr0 _)

/-- **Counting gives a uniform area law.** If every attached surface has at least A
plaquettes and there are at most c^k of size k, the sum is at most (ct)^A / (1 - ct),
independent of the volume. -/
theorem area_law_uniform (𝒯 : Finset (Finset P)) (t c : ℝ) (ht : 0 ≤ t) (hc : 0 ≤ c)
    (hct : c * t < 1) (A : ℕ) (hA : ∀ T ∈ 𝒯, A ≤ T.card)
    (hcount : ∀ k : ℕ, ((𝒯.filter (fun T => T.card = k)).card : ℝ) ≤ c ^ k) :
    ∑ T ∈ 𝒯, t ^ T.card ≤ (c * t) ^ A / (1 - c * t) := by
  have hmaps : ∀ T ∈ 𝒯, T.card ∈ Finset.range (Fintype.card P + 1) :=
    fun T _ => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.card_le_univ T))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine le_trans (Finset.sum_le_sum (fun k _ => ?_)) (geom_tail (c * t) (mul_nonneg hc ht) hct A _)
  have hk' : ∀ T ∈ 𝒯.filter (fun T => T.card = k), t ^ T.card = t ^ k :=
    fun T hT => by rw [(Finset.mem_filter.mp hT).2]
  have hfib : ∑ T ∈ 𝒯.filter (fun T => T.card = k), t ^ T.card =
      ((𝒯.filter (fun T => T.card = k)).card : ℝ) * t ^ k := by
    rw [Finset.sum_congr rfl hk', Finset.sum_const, nsmul_eq_mul]
  split_ifs with hk
  · rw [hfib, mul_pow]
    exact mul_le_mul_of_nonneg_right (hcount k) (pow_nonneg ht k)
  · have hempty : 𝒯.filter (fun T => T.card = k) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro T hT hTk
      exact hk (by rw [← hTk]; exact hA T hT)
    rw [hfib, hempty]
    simp

/-- **Strong-coupling area law, any dimension, uniform in the volume**, given the two
combinatorial inputs (a splitting into attached and closed parts, and a c^k count). -/
theorem strong_coupling_area_law (bd : P → Finset L) (β : ℝ) (hβ : 0 ≤ β) (C : Finset L)
    (𝒯 : Finset (Finset P)) (comp : Finset P → Finset P)
    (h_sub : ∀ S, comp S ⊆ S)
    (h_mem : ∀ S, HasBoundary bd S C → comp S ∈ 𝒯)
    (h_closed : ∀ S, HasBoundary bd S C → HasBoundary bd (S \ comp S) ∅)
    (c : ℝ) (hc : 0 ≤ c) (hct : c * Real.tanh β < 1) (A : ℕ) (hA : ∀ T ∈ 𝒯, A ≤ T.card)
    (hcount : ∀ k : ℕ, ((𝒯.filter (fun T => T.card = k)).card : ℝ) ≤ c ^ k) :
    numer bd β C / Z bd β ≤ (c * Real.tanh β) ^ A / (1 - c * Real.tanh β) :=
  (wilson_le_polymer bd β hβ C 𝒯 comp h_sub h_mem h_closed).trans
    (area_law_uniform 𝒯 _ c (tanh_nonneg' β hβ) hc hct A hA hcount)

/-- The string tension σ = -log(c tanh β) is positive throughout the strong-coupling regime
0 < c tanh β < 1, and the bound reads ⟨W_C⟩ ≤ exp(-σ A) / (1 - c tanh β). -/
theorem string_tension_exponential (c t : ℝ) (h0 : 0 < c * t) (h1 : c * t < 1) (A : ℕ) :
    0 < -Real.log (c * t) ∧
      (c * t) ^ A / (1 - c * t) = Real.exp (-(-Real.log (c * t)) * A) / (1 - c * t) := by
  refine ⟨neg_pos.mpr (Real.log_neg h0 h1), ?_⟩
  rw [neg_neg, mul_comm (Real.log (c * t)) (A : ℝ), ← Real.log_pow, Real.exp_log (pow_pos h0 A)]

end HTE

namespace Hypercubic

variable (N : ℕ) [NeZero N]

/-- The volume-uniform strong-coupling area law on the 4D hypercubic lattice, given the
two combinatorial inputs. Discharging them for this lattice is the next milestone. -/
theorem strong_coupling_area_law_4d (β : ℝ) (hβ : 0 ≤ β) (C : Finset (Link 4 N))
    (𝒯 : Finset (Finset (Plaq 4 N))) (comp : Finset (Plaq 4 N) → Finset (Plaq 4 N))
    (h_sub : ∀ S, comp S ⊆ S)
    (h_mem : ∀ S, HTE.HasBoundary (@bd 4 N _) S C → comp S ∈ 𝒯)
    (h_closed : ∀ S, HTE.HasBoundary (@bd 4 N _) S C → HTE.HasBoundary (@bd 4 N _) (S \ comp S) ∅)
    (c : ℝ) (hc : 0 ≤ c) (hct : c * Real.tanh β < 1) (A : ℕ) (hA : ∀ T ∈ 𝒯, A ≤ T.card)
    (hcount : ∀ k : ℕ, ((𝒯.filter (fun T => T.card = k)).card : ℝ) ≤ c ^ k) :
    HTE.numer (@bd 4 N _) β C / HTE.Z (@bd 4 N _) β ≤
      (c * Real.tanh β) ^ A / (1 - c * Real.tanh β) :=
  HTE.strong_coupling_area_law (@bd 4 N _) β hβ C 𝒯 comp h_sub h_mem h_closed c hc hct A hA hcount

end Hypercubic


/-! ## Part G: the splitting map, constructed and verified, any lattice

Part F assumed a map sending each surface S bounded by C to a part `comp S` attached to C
with a closed remainder. Here it is built explicitly: `comp S` is the set of plaquettes of S
reachable from a plaquette touching C by steps between plaquettes of S that share a link.
Everything Part F needed is proved, and `comp S` is shown to be connected and attached to C,
so only two purely combinatorial facts remain: the minimal area of surfaces bounded by C
and the number of connected attached surfaces of each size. -/

namespace HTE

set_option linter.unusedSectionVars false

variable {L P : Type} [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]

/-- Two plaquettes of S sharing a link. -/
def adj (bd : P → Finset L) (S : Finset P) (p q : P) : Prop :=
  p ∈ S ∧ q ∈ S ∧ ∃ l, l ∈ bd p ∧ l ∈ bd q

/-- p is reachable inside S from a plaquette of S that touches C. -/
def Attached (bd : P → Finset L) (S : Finset P) (C : Finset L) (p : P) : Prop :=
  ∃ q, q ∈ S ∧ (∃ l, l ∈ C ∧ l ∈ bd q) ∧ Relation.ReflTransGen (adj bd S) q p

open Classical in
/-- The part of S attached to C. -/
noncomputable def comp (bd : P → Finset L) (C : Finset L) (S : Finset P) : Finset P :=
  S.filter (Attached bd S C)

lemma comp_sub (bd : P → Finset L) (C : Finset L) (S : Finset P) : comp bd C S ⊆ S := by
  classical
  unfold comp
  exact Finset.filter_subset _ _

lemma mem_comp (bd : P → Finset L) (C : Finset L) (S : Finset P) (p : P) :
    p ∈ comp bd C S ↔ p ∈ S ∧ Attached bd S C p := by
  classical
  unfold comp
  exact Finset.mem_filter

/-- comp S is closed under sharing a link inside S. -/
lemma comp_closed_step (bd : P → Finset L) (C : Finset L) (S : Finset P) {p q : P} {l : L}
    (hp : p ∈ comp bd C S) (hq : q ∈ S) (hlp : l ∈ bd p) (hlq : l ∈ bd q) :
    q ∈ comp bd C S := by
  rw [mem_comp] at hp ⊢
  obtain ⟨hpS, r, hr, hrC, hpath⟩ := hp
  exact ⟨hq, r, hr, hrC, hpath.tail ⟨hpS, hq, l, hlp, hlq⟩⟩

/-- A plaquette of S touching C is attached. -/
lemma touch_mem_comp (bd : P → Finset L) (C : Finset L) (S : Finset P) {p : P} {l : L}
    (hp : p ∈ S) (hlC : l ∈ C) (hl : l ∈ bd p) : p ∈ comp bd C S := by
  rw [mem_comp]
  exact ⟨hp, p, hp, ⟨l, hlC, hl⟩, Relation.ReflTransGen.refl⟩

/-- Incidence counts split between comp S and the rest. -/
lemma card_split (bd : P → Finset L) (C : Finset L) (S : Finset P) (l : L) :
    (S.filter (fun p => l ∈ bd p)).card =
      ((comp bd C S).filter (fun p => l ∈ bd p)).card +
        ((S \ comp bd C S).filter (fun p => l ∈ bd p)).card := by
  classical
  rw [← Finset.card_filter_add_card_filter_not (s := S.filter (fun p => l ∈ bd p))
    (fun p => p ∈ comp bd C S)]
  congr 2
  · ext p
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h2, h1⟩; exact ⟨⟨comp_sub bd C S h2, h1⟩, h2⟩
  · ext p
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    tauto

/-- At each link, the remainder S \ comp S has either no incidence, or all of S's incidence
at a link outside C. -/
lemma rest_incidence (bd : P → Finset L) (C : Finset L) (S : Finset P) (l : L) :
    ((S \ comp bd C S).filter (fun p => l ∈ bd p)).card = 0 ∨
      (((S \ comp bd C S).filter (fun p => l ∈ bd p)).card =
          (S.filter (fun p => l ∈ bd p)).card ∧ l ∉ C) := by
  by_cases h : ∃ p ∈ comp bd C S, l ∈ bd p
  · left
    obtain ⟨p, hp, hlp⟩ := h
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro q hq hlq
    rw [Finset.mem_sdiff] at hq
    exact hq.2 (comp_closed_step bd C S hp hq.1 hlp hlq)
  · push Not at h
    have hzero : ((comp bd C S).filter (fun p => l ∈ bd p)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      exact fun p hp hl => h p hp hl
    by_cases hlC : l ∈ C
    · left
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro q hq hlq
      rw [Finset.mem_sdiff] at hq
      exact hq.2 (touch_mem_comp bd C S hq.1 hlC hlq)
    · right
      refine ⟨?_, hlC⟩
      have := card_split bd C S l
      omega

/-- **The remainder is closed.** -/
theorem rest_closed (bd : P → Finset L) (C : Finset L) (S : Finset P)
    (hS : HasBoundary bd S C) : HasBoundary bd (S \ comp bd C S) ∅ := by
  intro l
  have h := hS l
  simp only [mult, Finset.notMem_empty, ite_false, zero_add] at h ⊢
  rcases rest_incidence bd C S l with h0 | ⟨heq, hlC⟩
  · rw [h0]; exact ⟨0, rfl⟩
  · rw [heq]; simpa [hlC] using h

/-- **The attached part has the same boundary C.** -/
theorem comp_boundary (bd : P → Finset L) (C : Finset L) (S : Finset P)
    (hS : HasBoundary bd S C) : HasBoundary bd (comp bd C S) C := by
  intro l
  have h := hS l
  have hr := rest_closed bd C S hS l
  have hs := card_split bd C S l
  simp only [mult, Finset.notMem_empty, ite_false, zero_add] at h hr ⊢
  rw [Nat.even_iff] at h hr ⊢
  split_ifs at h ⊢ <;> omega

/-- **comp S is connected and attached in its own right**: every plaquette is reachable
from a plaquette touching C through plaquettes of comp S. -/
theorem comp_attached (bd : P → Finset L) (C : Finset L) (S : Finset P) (p : P)
    (hp : p ∈ comp bd C S) : Attached bd (comp bd C S) C p := by
  obtain ⟨_, q, hq, hqC, hpath⟩ := (mem_comp bd C S p).mp hp
  have hq' : q ∈ comp bd C S := by
    obtain ⟨l, hlC, hl⟩ := hqC
    exact touch_mem_comp bd C S hq hlC hl
  have key : ∀ x, Relation.ReflTransGen (adj bd S) q x →
      x ∈ comp bd C S ∧ Relation.ReflTransGen (adj bd (comp bd C S)) q x := by
    intro x hx
    induction hx with
    | refl => exact ⟨hq', Relation.ReflTransGen.refl⟩
    | tail _ hyz ih =>
      obtain ⟨hy, hpath'⟩ := ih
      obtain ⟨_, hzS, l, hly, hlz⟩ := hyz
      have hz := comp_closed_step bd C S hy hzS hly hlz
      exact ⟨hz, hpath'.tail ⟨hy, hz, l, hly, hlz⟩⟩
  exact ⟨q, hq', hqC, (key p hpath).2⟩

open Classical in
/-- Connected surfaces attached to C (the lattice animals that need counting). -/
noncomputable def connAttached (bd : P → Finset L) (C : Finset L) : Finset (Finset P) :=
  (Finset.univ : Finset P).powerset.filter (fun T => ∀ p ∈ T, Attached bd T C p)

open Classical in
/-- **Strong-coupling area law, any dimension, uniform in the volume.** The only inputs are
two combinatorial facts: every surface bounded by C has at least A plaquettes (minimal
area), and there are at most c^k connected attached surfaces of size k (lattice animals). -/
theorem strong_coupling_area_law_connected (bd : P → Finset L) (β : ℝ) (hβ : 0 ≤ β)
    (C : Finset L) (c : ℝ) (hc : 0 ≤ c) (hct : c * Real.tanh β < 1) (A : ℕ)
    (hA : ∀ T : Finset P, HasBoundary bd T C → A ≤ T.card)
    (hcount : ∀ k : ℕ, (((connAttached bd C).filter (fun T => T.card = k)).card : ℝ) ≤ c ^ k) :
    numer bd β C / Z bd β ≤ (c * Real.tanh β) ^ A / (1 - c * Real.tanh β) := by
  set 𝒯 := ((Finset.univ : Finset P).powerset.filter (fun S => HasBoundary bd S C)).image
    (comp bd C) with h𝒯
  have hmem : ∀ S, HasBoundary bd S C → comp bd C S ∈ 𝒯 := fun S hS =>
    Finset.mem_image.mpr ⟨S, Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), hS⟩, rfl⟩
  have h𝒯sub : 𝒯 ⊆ connAttached bd C := by
    intro T hT
    obtain ⟨S, _, rfl⟩ := Finset.mem_image.mp hT
    unfold connAttached
    exact Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),
      fun p hp => comp_attached bd C S p hp⟩
  have hA𝒯 : ∀ T ∈ 𝒯, A ≤ T.card := by
    intro T hT
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hT
    exact hA _ (comp_boundary bd C S (Finset.mem_filter.mp hS).2)
  have hcount𝒯 : ∀ k : ℕ, ((𝒯.filter (fun T => T.card = k)).card : ℝ) ≤ c ^ k := by
    intro k
    refine le_trans ?_ (hcount k)
    exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ h𝒯sub)
  exact strong_coupling_area_law bd β hβ C 𝒯 (comp bd C) (comp_sub bd C) hmem
    (rest_closed bd C) c hc hct A hA𝒯 hcount𝒯

end HTE

namespace Hypercubic

variable (N : ℕ) [NeZero N]

open Classical in
/-- **4D, uniform in the volume**: the strong-coupling area law on the 4D hypercubic lattice,
with only the minimal-area and lattice-animal facts as inputs. -/
theorem strong_coupling_area_law_4d_connected (β : ℝ) (hβ : 0 ≤ β) (C : Finset (Link 4 N))
    (c : ℝ) (hc : 0 ≤ c) (hct : c * Real.tanh β < 1) (A : ℕ)
    (hA : ∀ T : Finset (Plaq 4 N), HTE.HasBoundary (@bd 4 N _) T C → A ≤ T.card)
    (hcount : ∀ k : ℕ,
      (((HTE.connAttached (@bd 4 N _) C).filter (fun T => T.card = k)).card : ℝ) ≤ c ^ k) :
    HTE.numer (@bd 4 N _) β C / HTE.Z (@bd 4 N _) β ≤
      (c * Real.tanh β) ^ A / (1 - c * Real.tanh β) :=
  HTE.strong_coupling_area_law_connected (@bd 4 N _) β hβ C c hc hct A hA hcount

end Hypercubic


/-! ## Part H: lattice animals in any bounded-degree graph

**Theorem (`animal_count`).** In any finite graph with symmetric adjacency R in which every
vertex has at most Δ neighbours, the number of connected vertex sets of size k + 1 containing
a given vertex v is at most Δ^(2k).

Proof: a connected set can be grown from {v} one neighbour at a time (`growth`); each
growth step extends a covering walk by a detour out and back (`cover_step`), so every
connected set of size k + 1 is the vertex set of a walk from v with 2k steps
(`exists_cover`); there are at most Δ^m walks with m steps (`card_walksFrom`). -/

namespace Animals

set_option linter.unusedSectionVars false

variable {V : Type} [Fintype V] [DecidableEq V] (R : V → V → Prop) [DecidableRel R]

/-- Neighbours of v. -/
def nbr (v : V) : Finset V := Finset.univ.filter (R v)

/-- A step between two vertices of T. -/
def stepIn (T : Finset V) (a b : V) : Prop := a ∈ T ∧ b ∈ T ∧ R a b

/-- T contains v and is connected: every vertex of T is reachable from v inside T. -/
def RootedConn (T : Finset V) (v : V) : Prop :=
  v ∈ T ∧ ∀ x ∈ T, Relation.ReflTransGen (stepIn R T) v x

/-- All walks with m steps starting at v, as vertex lists. -/
def walksFrom : ℕ → V → Finset (List V)
  | 0, v => {[v]}
  | m + 1, v => (nbr R v).biUnion (fun u => (walksFrom m u).image (fun w => v :: w))

theorem card_walksFrom (Δ : ℕ) (hΔ : ∀ v, (nbr R v).card ≤ Δ) :
    ∀ m v, (walksFrom R m v).card ≤ Δ ^ m
  | 0, v => by simp [walksFrom]
  | m + 1, v => by
      simp only [walksFrom]
      calc _ ≤ ∑ u ∈ nbr R v, ((walksFrom R m u).image (fun w => v :: w)).card :=
            Finset.card_biUnion_le
        _ ≤ ∑ u ∈ nbr R v, Δ ^ m :=
            Finset.sum_le_sum (fun u _ => Finset.card_image_le.trans (card_walksFrom Δ hΔ m u))
        _ = (nbr R v).card * Δ ^ m := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ Δ * Δ ^ m := Nat.mul_le_mul_right _ (hΔ v)
        _ = Δ ^ (m + 1) := by ring

theorem mem_walksFrom : ∀ (m : ℕ) (v : V) (w : List V), w.head? = some v →
    w.length = m + 1 → List.IsChain R w → w ∈ walksFrom R m v
  | 0, v, [], hh, _, _ => by simp at hh
  | 0, v, [a], hh, _, _ => by simp at hh; subst hh; simp [walksFrom]
  | 0, _, _ :: _ :: _, _, hl, _ => by simp at hl
  | _ + 1, _, [], hh, _, _ => by simp at hh
  | _ + 1, _, [_], _, hl, _ => by simp at hl
  | m + 1, v, a :: u :: rest, hh, hl, hc => by
      simp at hh; subst hh
      rw [List.isChain_cons_cons] at hc
      simp only [walksFrom, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨u, by simp [nbr, hc.1], u :: rest,
        mem_walksFrom m u (u :: rest) rfl (by simpa using hl) hc.2, rfl⟩

/-- A connected set can always be grown by one neighbour of the current part. -/
theorem growth (T A : Finset V) (v : V) (hT : RootedConn R T v) (hvA : v ∈ A) (hAT : A ⊆ T)
    (hne : A ≠ T) : ∃ a ∈ A, ∃ y ∈ T, y ∉ A ∧ R a y := by
  have hx : ∃ x ∈ T, x ∉ A := by
    by_contra h
    push Not at h
    exact hne (Finset.Subset.antisymm hAT h)
  obtain ⟨x, hxT, hxA⟩ := hx
  have key : ∀ z, Relation.ReflTransGen (stepIn R T) v z →
      z ∈ A ∨ ∃ a ∈ A, ∃ y ∈ T, y ∉ A ∧ R a y := by
    intro z hz
    induction hz with
    | refl => exact Or.inl hvA
    | @tail b c _ hbc ih =>
      rcases ih with hb | h
      · by_cases hc : c ∈ A
        · exact Or.inl hc
        · exact Or.inr ⟨b, hb, c, hbc.2.1, hc, hbc.2.2⟩
      · exact Or.inr h
  rcases key x (hT.2 x hxT) with h | h
  · exact absurd h hxA
  · exact h

/-- w is a walk from v whose vertex set is exactly T, with 2|T| - 1 vertices. -/
def Covers (T : Finset V) (v : V) (w : List V) : Prop :=
  w.head? = some v ∧ List.IsChain R w ∧ w.toFinset = T ∧ w.length = 2 * T.card - 1

/-- Adding a neighbour y of a covered vertex a: detour a → y → a. -/
theorem cover_step (A : Finset V) (v a y : V) (w : List V) (hw : Covers R A v w)
    (ha : a ∈ A) (hy : y ∉ A) (hay : R a y) (hya : R y a) :
    ∃ w', Covers R (insert y A) v w' := by
  obtain ⟨hh, hc, hset, hlen⟩ := hw
  have haw : a ∈ w := by rw [← List.mem_toFinset, hset]; exact ha
  obtain ⟨l1, l2, rfl⟩ := List.append_of_mem haw
  refine ⟨l1 ++ a :: y :: a :: l2, ?_, ?_, ?_, ?_⟩
  · cases l1 <;> simpa using hh
  · rw [List.isChain_split] at hc ⊢
    refine ⟨hc.1, ?_⟩
    rw [List.isChain_cons_cons, List.isChain_cons_cons]
    exact ⟨hay, hya, hc.2⟩
  · rw [← hset]
    ext x
    simp only [List.mem_toFinset, List.mem_append, List.mem_cons, Finset.mem_insert]
    tauto
  · have hA : 1 ≤ A.card := Finset.card_pos.mpr ⟨a, ha⟩
    rw [Finset.card_insert_of_notMem hy]
    simp only [List.length_append, List.length_cons] at hlen ⊢
    omega

/-- **Every connected set is covered by a walk from v with 2(|T| - 1) steps.** -/
theorem exists_cover (T : Finset V) (v : V) (hT : RootedConn R T v)
    (hsymm : ∀ a b, R a b → R b a) : ∃ w, Covers R T v w := by
  have main : ∀ n, ∀ A : Finset V, v ∈ A → A ⊆ T → A.card + n = T.card →
      (∃ w, Covers R A v w) → ∃ w, Covers R T v w := by
    intro n
    induction n with
    | zero =>
      intro A _ hAT hc hw
      have : A = T := Finset.eq_of_subset_of_card_le hAT (by omega)
      subst this
      exact hw
    | succ n ih =>
      intro A hvA hAT hc hw
      obtain ⟨w, hw⟩ := hw
      have hne : A ≠ T := by
        intro h; subst h; omega
      obtain ⟨a, ha, y, hyT, hyA, hay⟩ := growth R T A v hT hvA hAT hne
      exact ih (insert y A) (Finset.mem_insert_of_mem hvA) (Finset.insert_subset hyT hAT)
        (by rw [Finset.card_insert_of_notMem hyA]; omega)
        (cover_step R A v a y w hw ha hyA hay (hsymm _ _ hay))
  have hpos : 1 ≤ T.card := Finset.card_pos.mpr ⟨v, hT.1⟩
  exact main (T.card - 1) {v} (Finset.mem_singleton_self v)
    (Finset.singleton_subset_iff.mpr hT.1) (by rw [Finset.card_singleton]; omega)
    ⟨[v], rfl, List.isChain_singleton v, by simp, by simp⟩

open Classical in
/-- **Lattice-animal bound.** At most Δ^(2k) connected sets of size k + 1 contain v. -/
theorem animal_count (Δ : ℕ) (hΔ : ∀ v, (nbr R v).card ≤ Δ) (hsymm : ∀ a b, R a b → R b a)
    (v : V) (k : ℕ) :
    ((Finset.univ : Finset (Finset V)).filter
      (fun T => RootedConn R T v ∧ T.card = k + 1)).card ≤ Δ ^ (2 * k) := by
  have hw : ∀ T, RootedConn R T v → ∃ w, Covers R T v w :=
    fun T hT => exists_cover R T v hT hsymm
  let f : Finset V → List V := fun T =>
    if h : RootedConn R T v then Classical.choose (hw T h) else []
  have hf : ∀ T, RootedConn R T v → Covers R T v (f T) := by
    intro T hT
    simp only [f, dif_pos hT]
    exact Classical.choose_spec (hw T hT)
  calc _ ≤ (walksFrom R (2 * k) v).card := by
        apply Finset.card_le_card_of_injOn f
        · intro T hT
          have hT' := Finset.mem_filter.mp hT
          have hc := hf T hT'.2.1
          exact mem_walksFrom R (2 * k) v (f T) hc.1 (by rw [hc.2.2.2, hT'.2.2]; omega) hc.2.1
        · intro T₁ h₁ T₂ h₂ heq
          have c1 := hf T₁ (Finset.mem_filter.mp h₁).2.1
          have c2 := hf T₂ (Finset.mem_filter.mp h₂).2.1
          rw [← c1.2.2.1, ← c2.2.2.1, heq]
    _ ≤ Δ ^ (2 * k) := card_walksFrom R Δ hΔ (2 * k) v

end Animals
