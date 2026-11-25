/-
  YangMillsToy.lean

  Honest, provable fragments around the Yang–Mills existence and mass gap problem.
  None of this proves the Millennium Problem. It formalises the parts of the
  setup that are pure algebra, and one toy statement showing *why* the gap is hard.

  Sections
    1. Lattice gauge theory: gauge transformations, plaquette holonomy,
       gauge invariance of the Wilson action (for any group G).
    2. Continuum algebra: Lie bracket, Jacobi identity, gauge covariance of
       the curvature F = [A_μ, A_ν] for constant fields, invariance of tr F².
    3. The mass gap as a uniformity statement: finitely many gaps always have
       a common positive lower bound, infinitely many need not.

  Check it with Mathlib, e.g. at https://live.lean-lang.org or inside a
  project created with `lake new myproj math`.
-/
import Mathlib

namespace YangMillsToy

/-! ## 1. Lattice gauge theory -/

section Lattice

variable {G : Type*} [Group G] {X : Type*}

/-- A class function on `G`: invariant under conjugation.
In physics, `f U = Re tr U` for `U` in a unitary representation of `SU(N)`. -/
def IsClassFunction (f : G → ℝ) : Prop :=
  ∀ g h : G, f (g * h * g⁻¹) = f h

/-- A plaquette: an oriented loop through four lattice sites `a → b → c → d → a`. -/
structure Plaquette (X : Type*) where
  a : X
  b : X
  c : X
  d : X

/-- A gauge transformation `g : X → G` acts on link variables `U x y`
(the parallel transporter on the link between `x` and `y`). -/
def gaugeTransform (g : X → G) (U : X → X → G) : X → X → G :=
  fun x y => g x * U x y * (g y)⁻¹

/-- The holonomy (Wilson loop) of `U` around a plaquette. -/
def holonomy (U : X → X → G) (p : Plaquette X) : G :=
  U p.a p.b * U p.b p.c * U p.c p.d * U p.d p.a

/-- The trivial gauge transformation does nothing. -/
theorem gaugeTransform_one (U : X → X → G) :
    gaugeTransform (1 : X → G) U = U := by
  funext x y
  simp [gaugeTransform]

/-- Gauge transformations compose: this is a group action of `X → G`. -/
theorem gaugeTransform_mul (g₁ g₂ : X → G) (U : X → X → G) :
    gaugeTransform g₁ (gaugeTransform g₂ U) = gaugeTransform (g₁ * g₂) U := by
  funext x y
  simp only [gaugeTransform, Pi.mul_apply]
  group

/-- Key lemma: the holonomy around a closed loop transforms by conjugation
at the base point. All interior gauge factors cancel. -/
theorem holonomy_gaugeTransform (g : X → G) (U : X → X → G) (p : Plaquette X) :
    holonomy (gaugeTransform g U) p = g p.a * holonomy U p * (g p.a)⁻¹ := by
  simp only [holonomy, gaugeTransform]
  group

/-- The Wilson action of a finite collection of plaquettes. -/
def wilsonAction (f : G → ℝ) (P : Finset (Plaquette X)) (U : X → X → G) : ℝ :=
  ∑ p ∈ P, f (holonomy U p)

/-- **Gauge invariance of the Wilson action.** -/
theorem wilsonAction_gauge_invariant (f : G → ℝ) (hf : IsClassFunction f)
    (P : Finset (Plaquette X)) (g : X → G) (U : X → X → G) :
    wilsonAction f P (gaugeTransform g U) = wilsonAction f P U := by
  unfold wilsonAction
  refine Finset.sum_congr rfl ?_
  intro p _
  rw [holonomy_gaugeTransform, hf]

end Lattice

/-! ## 2. Continuum algebra (constant gauge fields) -/

section Algebra

variable {R : Type*} [Ring R]

/-- The commutator bracket `[a, b] = ab - ba`. For matrices this is the Lie bracket
of `𝔰𝔲(N)`. -/
def bracket (a b : R) : R := a * b - b * a

theorem bracket_antisymm (a b : R) : bracket a b = -bracket b a := by
  simp only [bracket]
  noncomm_ring

/-- The Jacobi identity. In the continuum theory this is what makes the
Bianchi identity `D ∧ F = 0` hold. -/
theorem bracket_jacobi (a b c : R) :
    bracket a (bracket b c) + bracket b (bracket c a) + bracket c (bracket a b) = 0 := by
  simp only [bracket]
  noncomm_ring

/-- Conjugation by a unit: a constant (global) gauge transformation. -/
def conj (u : Rˣ) (a : R) : R := u * a * ↑u⁻¹

theorem conj_mul (u : Rˣ) (a b : R) : conj u a * conj u b = conj u (a * b) := by
  simp [conj, mul_assoc]

theorem conj_sub (u : Rˣ) (a b : R) : conj u (a - b) = conj u a - conj u b := by
  simp [conj, mul_sub, sub_mul]

theorem conj_bracket (u : Rˣ) (a b : R) :
    bracket (conj u a) (conj u b) = conj u (bracket a b) := by
  simp only [bracket, conj_mul, conj_sub]

/-- For a constant connection `A : ι → R` (one component per spacetime direction)
the curvature reduces to `F μ ν = [A μ, A ν]`. -/
def fieldStrength {ι : Type*} (A : ι → R) (μ ν : ι) : R :=
  bracket (A μ) (A ν)

/-- **Gauge covariance**: under `A ↦ u A u⁻¹`, the curvature goes to `u F u⁻¹`. -/
theorem fieldStrength_gauge_covariant {ι : Type*} (u : Rˣ) (A : ι → R) (μ ν : ι) :
    fieldStrength (fun i => conj u (A i)) μ ν = conj u (fieldStrength A μ ν) := by
  simp only [fieldStrength, conj_bracket]

/-- **Gauge invariance of the Yang–Mills energy density** `tr (F²)`.
NOTE: if this line fails, the lemma name `Matrix.trace_units_conj` may have
changed in your Mathlib version; search for it with `#check` or `exact?`. -/
theorem trace_sq_gauge_invariant {n : Type*} [Fintype n] [DecidableEq n]
    (u : (Matrix n n ℂ)ˣ) (F : Matrix n n ℂ) :
    Matrix.trace (conj u F * conj u F) = Matrix.trace (F * F) := by
  rw [conj_mul]
  unfold conj
  exact Matrix.trace_units_conj u (F * F)

end Algebra

/-! ## 3. Why the mass gap is hard: uniformity

On a finite lattice the Hamiltonian is a finite-dimensional matrix, so a
positive gap above the vacuum exists for trivial reasons. The Millennium
Problem asks for a gap that survives the infinite-volume and continuum
limits. The two theorems below isolate that logical point. -/

/-- Finitely many positive gaps always have a common positive lower bound. -/
theorem finite_family_uniform_gap (s : Finset ℝ) (hpos : ∀ x ∈ s, 0 < x) :
    ∃ m > 0, ∀ x ∈ s, m ≤ x := by
  by_cases h : s.Nonempty
  · exact ⟨s.min' h, hpos _ (s.min'_mem h), fun x hx => s.min'_le x hx⟩
  · exact ⟨1, one_pos, fun x hx => absurd ⟨x, hx⟩ h⟩

/-- But a gap on every lattice of size `L` does **not** imply a mass gap:
here `Δ L = 1/(L+1)` is positive for every `L`, yet no `m > 0` bounds it below. -/
theorem gaps_can_close :
    ∃ Δ : ℕ → ℝ, (∀ L, 0 < Δ L) ∧ ¬ ∃ m > 0, ∀ L, m ≤ Δ L := by
  refine ⟨fun L => 1 / ((L : ℝ) + 1), fun L => by positivity, ?_⟩
  rintro ⟨m, hm, h⟩
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hm
  have hN' : m ≤ 1 / ((N : ℝ) + 1) := h N
  linarith

/-- The mass gap property for a family of finite-volume gaps: a uniform bound. -/
def HasUniformMassGap (Δ : ℕ → ℝ) : Prop :=
  ∃ m > 0, ∀ L, m ≤ Δ L

end YangMillsToy
