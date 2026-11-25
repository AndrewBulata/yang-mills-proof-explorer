/-
  Verified.lean: every proof in this file is checked by Lean 4 against Mathlib.
  Part A closes the 10 targets the first engine run left open.
  Part B: Haar invariance, the Elitzur mechanism, exact area law of 2D Z₂ gauge theory.
  Part C: transfer-matrix spectrum and mass gap of 2D Z₂ gauge theory at every coupling.
  Part D: the complete-graph gap for every n, generalised from conjecture-mode results.
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

Conjecture mode proved `complete_gap_n` for n = 3, 4, 5 and refuted the constant n + 1.
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
