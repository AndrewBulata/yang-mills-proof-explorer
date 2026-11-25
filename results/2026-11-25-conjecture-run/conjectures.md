# Conjecture run

45 candidate statements over 2 round(s): 11 open, 16 proved, 18 refuted.

## Findings

- `path_gap_one_4` is false (4-site chain has gap ≥ 1 fails), refuted by an explicit counterexample.
- `two_site_gap`: the constant 2 is sharp among integers (3 is refuted by an explicit counterexample).
- `two_site_gap`: hypothesis `h` is necessary (dropping it is refuted).
- `three_site_gap`: the constant 3 is sharp among integers (4 is refuted by an explicit counterexample).
- `three_site_gap`: hypothesis `h` is necessary (dropping it is refuted).
- `gap_from_contraction`: hypothesis `hq` is necessary (dropping it is refuted).
- `z2_string_tension_pos`: hypothesis `hβ` is necessary (dropping it is refuted).
- `complete_gap_3`: the constant 3 is sharp among integers (4 is refuted by an explicit counterexample).
- `complete_gap_4`: the constant 4 is sharp among integers (5 is refuted by an explicit counterexample).

## Proved (16)

**two_site_gap__c1down** (mutation)

```lean
theorem two_site_gap__c1down (v₀ v₁ : ℝ) (h : v₀ + v₁ = 0) : (v₀ - v₁) ^ 2 ≥ 1 * (v₀ ^ 2 + v₁ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem two_site_gap__c1down (v₀ v₁ : ℝ) (h : v₀ + v₁ = 0) : (v₀ - v₁) ^ 2 ≥ 1 * (v₀ ^ 2 + v₁ ^ 2) := by
  nlinarith [sq_nonneg (0 : ℝ)]
```

</details>

**three_site_gap__c3down** (mutation)

```lean
theorem three_site_gap__c3down (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0) : (v₀ - v₁) ^ 2 + (v₁ - v₂) ^ 2 + (v₂ - v₀) ^ 2 ≥ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem three_site_gap__c3down (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0) : (v₀ - v₁) ^ 2 + (v₁ - v₂) ^ 2 + (v₂ - v₀) ^ 2 ≥ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2) := by
  nlinarith [sq_nonneg (0 : ℝ)]
```

</details>

**massive_uniform_gap__c0up** (mutation)

```lean
theorem massive_uniform_gap__c0up (N : ℕ) (v : ℕ → ℝ) (m : ℝ) : ∑ i ∈ Finset.range N, (v (i + 2) - v i) ^ 2 + m ^ 2 * ∑ i ∈ Finset.range N, v i ^ 2 ≥ m ^ 2 * ∑ i ∈ Finset.range N, v i ^ 2
```

<details><summary>Lean proof</summary>

```lean
theorem massive_uniform_gap__c0up (N : ℕ) (v : ℕ → ℝ) (m : ℝ) : ∑ i ∈ Finset.range N, (v (i + 2) - v i) ^ 2 + m ^ 2 * ∑ i ∈ Finset.range N, v i ^ 2 ≥ m ^ 2 * ∑ i ∈ Finset.range N, v i ^ 2 := by
  norm_num
  positivity
```

</details>

**path_gap_one_2** (family)

```lean
theorem path_gap_one_2 (v₀ v₁ : ℝ) (h : v₀ + v₁ = 0) : (v₁ - v₀) ^ 2 ≥ v₀ ^ 2 + v₁ ^ 2
```

<details><summary>Lean proof</summary>

```lean
theorem path_gap_one_2 (v₀ v₁ : ℝ) (h : v₀ + v₁ = 0) : (v₁ - v₀) ^ 2 ≥ v₀ ^ 2 + v₁ ^ 2 := by
  nlinarith [sq_nonneg (0 : ℝ)]
```

</details>

**complete_gap_3** (family)

```lean
theorem complete_gap_3 (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₁ - v₂) ^ 2 ≥ 3 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem complete_gap_3 (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₁ - v₂) ^ 2 ≥ 3 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2) := by
  nlinarith [sq_nonneg (0 : ℝ)]
```

</details>

**complete_gap_4** (family)

```lean
theorem complete_gap_4 (v₀ v₁ v₂ v₃ : ℝ) (h : v₀ + v₁ + v₂ + v₃ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₀ - v₃) ^ 2 + (v₁ - v₂) ^ 2 + (v₁ - v₃) ^ 2 + (v₂ - v₃) ^ 2 ≥ 4 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem complete_gap_4 (v₀ v₁ v₂ v₃ : ℝ) (h : v₀ + v₁ + v₂ + v₃ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₀ - v₃) ^ 2 + (v₁ - v₂) ^ 2 + (v₁ - v₃) ^ 2 + (v₂ - v₃) ^ 2 ≥ 4 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2) := by
  nlinarith [sq_nonneg (0 : ℝ)]
```

</details>

**complete_gap_5** (family)

```lean
theorem complete_gap_5 (v₀ v₁ v₂ v₃ v₄ : ℝ) (h : v₀ + v₁ + v₂ + v₃ + v₄ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₀ - v₃) ^ 2 + (v₀ - v₄) ^ 2 + (v₁ - v₂) ^ 2 + (v₁ - v₃) ^ 2 + (v₁ - v₄) ^ 2 + (v₂ - v₃) ^ 2 + (v₂ - v₄) ^ 2 + (v₃ - v₄) ^ 2 ≥ 5 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2 + v₄ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem complete_gap_5 (v₀ v₁ v₂ v₃ v₄ : ℝ) (h : v₀ + v₁ + v₂ + v₃ + v₄ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₀ - v₃) ^ 2 + (v₀ - v₄) ^ 2 + (v₁ - v₂) ^ 2 + (v₁ - v₃) ^ 2 + (v₁ - v₄) ^ 2 + (v₂ - v₃) ^ 2 + (v₂ - v₄) ^ 2 + (v₃ - v₄) ^ 2 ≥ 5 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2 + v₄ ^ 2) := by
  nlinarith [sq_nonneg (0 : ℝ)]
```

</details>

**massive_chain_gap_2** (family)

```lean
theorem massive_chain_gap_2 (v₀ v₁ m : ℝ) : (v₁ - v₀) ^ 2 + m ^ 2 * (v₀ ^ 2 + v₁ ^ 2) ≥ m ^ 2 * (v₀ ^ 2 + v₁ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem massive_chain_gap_2 (v₀ v₁ m : ℝ) : (v₁ - v₀) ^ 2 + m ^ 2 * (v₀ ^ 2 + v₁ ^ 2) ≥ m ^ 2 * (v₀ ^ 2 + v₁ ^ 2) := by
  nlinarith [sq_nonneg (0 : ℝ)]
```

</details>

**massive_chain_gap_3** (family)

```lean
theorem massive_chain_gap_3 (v₀ v₁ v₂ m : ℝ) : (v₁ - v₀) ^ 2 + (v₂ - v₁) ^ 2 + m ^ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2) ≥ m ^ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem massive_chain_gap_3 (v₀ v₁ v₂ m : ℝ) : (v₁ - v₀) ^ 2 + (v₂ - v₁) ^ 2 + m ^ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2) ≥ m ^ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2) := by
  nlinarith [sq_nonneg (0 : ℝ)]
```

</details>

**massive_chain_gap_4** (family)

```lean
theorem massive_chain_gap_4 (v₀ v₁ v₂ v₃ m : ℝ) : (v₁ - v₀) ^ 2 + (v₂ - v₁) ^ 2 + (v₃ - v₂) ^ 2 + m ^ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2) ≥ m ^ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem massive_chain_gap_4 (v₀ v₁ v₂ v₃ m : ℝ) : (v₁ - v₀) ^ 2 + (v₂ - v₁) ^ 2 + (v₃ - v₂) ^ 2 + m ^ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2) ≥ m ^ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2) := by
  nlinarith [sq_nonneg (0 : ℝ)]
```

</details>

**three_site_gap__c3down__c3down** (mutation)

```lean
theorem three_site_gap__c3down__c3down (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0) : (v₀ - v₁) ^ 2 + (v₁ - v₂) ^ 2 + (v₂ - v₀) ^ 2 ≥ 1 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem three_site_gap__c3down__c3down (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0) : (v₀ - v₁) ^ 2 + (v₁ - v₂) ^ 2 + (v₂ - v₀) ^ 2 ≥ 1 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2) := by
  nlinarith [sq_nonneg (0 : ℝ)]
```

</details>

**massive_uniform_gap__c0up__c0up** (mutation)

```lean
theorem massive_uniform_gap__c0up__c0up (N : ℕ) (v : ℕ → ℝ) (m : ℝ) : ∑ i ∈ Finset.range N, (v (i + 3) - v i) ^ 2 + m ^ 2 * ∑ i ∈ Finset.range N, v i ^ 2 ≥ m ^ 2 * ∑ i ∈ Finset.range N, v i ^ 2
```

<details><summary>Lean proof</summary>

```lean
theorem massive_uniform_gap__c0up__c0up (N : ℕ) (v : ℕ → ℝ) (m : ℝ) : ∑ i ∈ Finset.range N, (v (i + 3) - v i) ^ 2 + m ^ 2 * ∑ i ∈ Finset.range N, v i ^ 2 ≥ m ^ 2 * ∑ i ∈ Finset.range N, v i ^ 2 := by
  norm_num
  positivity
```

</details>

**massive_uniform_gap__c0up__c0down** (mutation)

```lean
theorem massive_uniform_gap__c0up__c0down (N : ℕ) (v : ℕ → ℝ) (m : ℝ) : ∑ i ∈ Finset.range N, (v (i + 1) - v i) ^ 2 + m ^ 2 * ∑ i ∈ Finset.range N, v i ^ 2 ≥ m ^ 2 * ∑ i ∈ Finset.range N, v i ^ 2
```

<details><summary>Lean proof</summary>

```lean
theorem massive_uniform_gap__c0up__c0down (N : ℕ) (v : ℕ → ℝ) (m : ℝ) : ∑ i ∈ Finset.range N, (v (i + 1) - v i) ^ 2 + m ^ 2 * ∑ i ∈ Finset.range N, v i ^ 2 ≥ m ^ 2 * ∑ i ∈ Finset.range N, v i ^ 2 := by
  norm_num
  positivity
```

</details>

**complete_gap_3__c3down** (mutation)

```lean
theorem complete_gap_3__c3down (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₁ - v₂) ^ 2 ≥ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem complete_gap_3__c3down (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₁ - v₂) ^ 2 ≥ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2) := by
  nlinarith [sq_nonneg (0 : ℝ)]
```

</details>

**complete_gap_4__c6down** (mutation)

```lean
theorem complete_gap_4__c6down (v₀ v₁ v₂ v₃ : ℝ) (h : v₀ + v₁ + v₂ + v₃ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₀ - v₃) ^ 2 + (v₁ - v₂) ^ 2 + (v₁ - v₃) ^ 2 + (v₂ - v₃) ^ 2 ≥ 3 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem complete_gap_4__c6down (v₀ v₁ v₂ v₃ : ℝ) (h : v₀ + v₁ + v₂ + v₃ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₀ - v₃) ^ 2 + (v₁ - v₂) ^ 2 + (v₁ - v₃) ^ 2 + (v₂ - v₃) ^ 2 ≥ 3 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2) := by
  nlinarith [sq_nonneg (0 : ℝ)]
```

</details>

**complete_gap_5__c10down** (mutation)

```lean
theorem complete_gap_5__c10down (v₀ v₁ v₂ v₃ v₄ : ℝ) (h : v₀ + v₁ + v₂ + v₃ + v₄ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₀ - v₃) ^ 2 + (v₀ - v₄) ^ 2 + (v₁ - v₂) ^ 2 + (v₁ - v₃) ^ 2 + (v₁ - v₄) ^ 2 + (v₂ - v₃) ^ 2 + (v₂ - v₄) ^ 2 + (v₃ - v₄) ^ 2 ≥ 4 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2 + v₄ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem complete_gap_5__c10down (v₀ v₁ v₂ v₃ v₄ : ℝ) (h : v₀ + v₁ + v₂ + v₃ + v₄ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₀ - v₃) ^ 2 + (v₀ - v₄) ^ 2 + (v₁ - v₂) ^ 2 + (v₁ - v₃) ^ 2 + (v₁ - v₄) ^ 2 + (v₂ - v₃) ^ 2 + (v₂ - v₄) ^ 2 + (v₃ - v₄) ^ 2 ≥ 4 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2 + v₄ ^ 2) := by
  nlinarith [sq_nonneg (0 : ℝ)]
```

</details>

## Refuted (18)

**two_site_gap__c1up** (mutation)

```lean
theorem two_site_gap__c1up (v₀ v₁ : ℝ) (h : v₀ + v₁ = 0) : (v₀ - v₁) ^ 2 ≥ 3 * (v₀ ^ 2 + v₁ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem two_site_gap__c1up_refuted : ¬ (∀ (v₀ v₁ : ℝ) (h : v₀ + v₁ = 0), (v₀ - v₁) ^ 2 ≥ 3 * (v₀ ^ 2 + v₁ ^ 2)) := by
  (push Not; refine ⟨(1 : ℝ), (-1 : ℝ), ?_⟩ <;> norm_num)
```

</details>

**two_site_gap__gt** (mutation)

```lean
theorem two_site_gap__gt (v₀ v₁ : ℝ) (h : v₀ + v₁ = 0) : (v₀ - v₁) ^ 2 > 2 * (v₀ ^ 2 + v₁ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem two_site_gap__gt_refuted : ¬ (∀ (v₀ v₁ : ℝ) (h : v₀ + v₁ = 0), (v₀ - v₁) ^ 2 > 2 * (v₀ ^ 2 + v₁ ^ 2)) := by
  (push Not; refine ⟨(1 : ℝ), (-1 : ℝ), ?_⟩ <;> norm_num)
```

</details>

**two_site_gap__no_h** (mutation)

```lean
theorem two_site_gap__no_h (v₀ v₁ : ℝ) : (v₀ - v₁) ^ 2 ≥ 2 * (v₀ ^ 2 + v₁ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem two_site_gap__no_h_refuted : ¬ (∀ (v₀ v₁ : ℝ), (v₀ - v₁) ^ 2 ≥ 2 * (v₀ ^ 2 + v₁ ^ 2)) := by
  (push Not; refine ⟨(1 : ℝ), (1 : ℝ), ?_⟩ <;> norm_num)
```

</details>

**three_site_gap__c3up** (mutation)

```lean
theorem three_site_gap__c3up (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0) : (v₀ - v₁) ^ 2 + (v₁ - v₂) ^ 2 + (v₂ - v₀) ^ 2 ≥ 4 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem three_site_gap__c3up_refuted : ¬ (∀ (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0), (v₀ - v₁) ^ 2 + (v₁ - v₂) ^ 2 + (v₂ - v₀) ^ 2 ≥ 4 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)) := by
  (push Not; refine ⟨(1 : ℝ), (1 : ℝ), (-2 : ℝ), ?_⟩ <;> norm_num)
```

</details>

**three_site_gap__gt** (mutation)

```lean
theorem three_site_gap__gt (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0) : (v₀ - v₁) ^ 2 + (v₁ - v₂) ^ 2 + (v₂ - v₀) ^ 2 > 3 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem three_site_gap__gt_refuted : ¬ (∀ (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0), (v₀ - v₁) ^ 2 + (v₁ - v₂) ^ 2 + (v₂ - v₀) ^ 2 > 3 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)) := by
  (push Not; refine ⟨(1 : ℝ), (1 : ℝ), (-2 : ℝ), ?_⟩ <;> norm_num)
```

</details>

**three_site_gap__no_h** (mutation)

```lean
theorem three_site_gap__no_h (v₀ v₁ v₂ : ℝ) : (v₀ - v₁) ^ 2 + (v₁ - v₂) ^ 2 + (v₂ - v₀) ^ 2 ≥ 3 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem three_site_gap__no_h_refuted : ¬ (∀ (v₀ v₁ v₂ : ℝ), (v₀ - v₁) ^ 2 + (v₁ - v₂) ^ 2 + (v₂ - v₀) ^ 2 ≥ 3 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)) := by
  (push Not; refine ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), ?_⟩ <;> norm_num)
```

</details>

**gap_from_contraction__no_hq** (mutation)

```lean
theorem gap_from_contraction__no_hq (q τ : ℝ) (hq1 : q < 1) (hτ : 0 < τ) : 0 < -Real.log q / τ
```

<details><summary>Lean proof</summary>

```lean
theorem gap_from_contraction__no_hq_refuted : ¬ (∀ (q τ : ℝ) (hq1 : q < 1) (hτ : 0 < τ), 0 < -Real.log q / τ) := by
  (push Not; refine ⟨(-1 : ℝ), (1 : ℝ), ?_⟩ <;> norm_num)
```

</details>

**z2_string_tension_pos__no_hβ** (mutation)

```lean
theorem z2_string_tension_pos__no_hβ (β : ℝ) : 0 < -Real.log (Real.tanh β)
```

<details><summary>Lean proof</summary>

```lean
theorem z2_string_tension_pos__no_hβ_refuted : ¬ (∀ (β : ℝ), 0 < -Real.log (Real.tanh β)) := by
  (push Not; refine ⟨(0 : ℝ), ?_⟩ <;> norm_num)
```

</details>

**path_gap_one_4** (family)

```lean
theorem path_gap_one_4 (v₀ v₁ v₂ v₃ : ℝ) (h : v₀ + v₁ + v₂ + v₃ = 0) : (v₁ - v₀) ^ 2 + (v₂ - v₁) ^ 2 + (v₃ - v₂) ^ 2 ≥ v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2
```

<details><summary>Lean proof</summary>

```lean
theorem path_gap_one_4_refuted : ¬ (∀ (v₀ v₁ v₂ v₃ : ℝ) (h : v₀ + v₁ + v₂ + v₃ = 0), (v₁ - v₀) ^ 2 + (v₂ - v₁) ^ 2 + (v₃ - v₂) ^ 2 ≥ v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2) := by
  (push Not; refine ⟨(3 : ℝ), (1 : ℝ), (-1 : ℝ), (-3 : ℝ), ?_⟩ <;> norm_num)
```

</details>

**two_site_gap__c1down__gt** (mutation)

```lean
theorem two_site_gap__c1down__gt (v₀ v₁ : ℝ) (h : v₀ + v₁ = 0) : (v₀ - v₁) ^ 2 > 1 * (v₀ ^ 2 + v₁ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem two_site_gap__c1down__gt_refuted : ¬ (∀ (v₀ v₁ : ℝ) (h : v₀ + v₁ = 0), (v₀ - v₁) ^ 2 > 1 * (v₀ ^ 2 + v₁ ^ 2)) := by
  (push Not; refine ⟨(0 : ℝ), (0 : ℝ), ?_⟩ <;> norm_num)
```

</details>

**three_site_gap__c3down__gt** (mutation)

```lean
theorem three_site_gap__c3down__gt (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0) : (v₀ - v₁) ^ 2 + (v₁ - v₂) ^ 2 + (v₂ - v₀) ^ 2 > 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem three_site_gap__c3down__gt_refuted : ¬ (∀ (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0), (v₀ - v₁) ^ 2 + (v₁ - v₂) ^ 2 + (v₂ - v₀) ^ 2 > 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)) := by
  (push Not; refine ⟨(0 : ℝ), (0 : ℝ), (0 : ℝ), ?_⟩ <;> norm_num)
```

</details>

**path_gap_one_2__gt** (mutation)

```lean
theorem path_gap_one_2__gt (v₀ v₁ : ℝ) (h : v₀ + v₁ = 0) : (v₁ - v₀) ^ 2 > v₀ ^ 2 + v₁ ^ 2
```

<details><summary>Lean proof</summary>

```lean
theorem path_gap_one_2__gt_refuted : ¬ (∀ (v₀ v₁ : ℝ) (h : v₀ + v₁ = 0), (v₁ - v₀) ^ 2 > v₀ ^ 2 + v₁ ^ 2) := by
  (push Not; refine ⟨(0 : ℝ), (0 : ℝ), ?_⟩ <;> norm_num)
```

</details>

**complete_gap_3__c3up** (mutation)

```lean
theorem complete_gap_3__c3up (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₁ - v₂) ^ 2 ≥ 4 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem complete_gap_3__c3up_refuted : ¬ (∀ (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0), (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₁ - v₂) ^ 2 ≥ 4 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)) := by
  (push Not; refine ⟨(1 : ℝ), (1 : ℝ), (-2 : ℝ), ?_⟩ <;> norm_num)
```

</details>

**complete_gap_3__gt** (mutation)

```lean
theorem complete_gap_3__gt (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₁ - v₂) ^ 2 > 3 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem complete_gap_3__gt_refuted : ¬ (∀ (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0), (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₁ - v₂) ^ 2 > 3 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)) := by
  (push Not; refine ⟨(1 : ℝ), (1 : ℝ), (-2 : ℝ), ?_⟩ <;> norm_num)
```

</details>

**complete_gap_4__c6up** (mutation)

```lean
theorem complete_gap_4__c6up (v₀ v₁ v₂ v₃ : ℝ) (h : v₀ + v₁ + v₂ + v₃ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₀ - v₃) ^ 2 + (v₁ - v₂) ^ 2 + (v₁ - v₃) ^ 2 + (v₂ - v₃) ^ 2 ≥ 5 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem complete_gap_4__c6up_refuted : ¬ (∀ (v₀ v₁ v₂ v₃ : ℝ) (h : v₀ + v₁ + v₂ + v₃ = 0), (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₀ - v₃) ^ 2 + (v₁ - v₂) ^ 2 + (v₁ - v₃) ^ 2 + (v₂ - v₃) ^ 2 ≥ 5 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2)) := by
  (push Not; refine ⟨(3 : ℝ), (3 : ℝ), (-3 : ℝ), (-3 : ℝ), ?_⟩ <;> norm_num)
```

</details>

**complete_gap_4__gt** (mutation)

```lean
theorem complete_gap_4__gt (v₀ v₁ v₂ v₃ : ℝ) (h : v₀ + v₁ + v₂ + v₃ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₀ - v₃) ^ 2 + (v₁ - v₂) ^ 2 + (v₁ - v₃) ^ 2 + (v₂ - v₃) ^ 2 > 4 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem complete_gap_4__gt_refuted : ¬ (∀ (v₀ v₁ v₂ v₃ : ℝ) (h : v₀ + v₁ + v₂ + v₃ = 0), (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₀ - v₃) ^ 2 + (v₁ - v₂) ^ 2 + (v₁ - v₃) ^ 2 + (v₂ - v₃) ^ 2 > 4 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2)) := by
  (push Not; refine ⟨(3 : ℝ), (3 : ℝ), (-3 : ℝ), (-3 : ℝ), ?_⟩ <;> norm_num)
```

</details>

**massive_chain_gap_2__gt** (mutation)

```lean
theorem massive_chain_gap_2__gt (v₀ v₁ m : ℝ) : (v₁ - v₀) ^ 2 + m ^ 2 * (v₀ ^ 2 + v₁ ^ 2) > m ^ 2 * (v₀ ^ 2 + v₁ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem massive_chain_gap_2__gt_refuted : ¬ (∀ (v₀ v₁ m : ℝ), (v₁ - v₀) ^ 2 + m ^ 2 * (v₀ ^ 2 + v₁ ^ 2) > m ^ 2 * (v₀ ^ 2 + v₁ ^ 2)) := by
  (push Not; refine ⟨(1 : ℝ), (1 : ℝ), (1 : ℝ), ?_⟩ <;> norm_num)
```

</details>

**massive_chain_gap_3__gt** (mutation)

```lean
theorem massive_chain_gap_3__gt (v₀ v₁ v₂ m : ℝ) : (v₁ - v₀) ^ 2 + (v₂ - v₁) ^ 2 + m ^ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2) > m ^ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)
```

<details><summary>Lean proof</summary>

```lean
theorem massive_chain_gap_3__gt_refuted : ¬ (∀ (v₀ v₁ v₂ m : ℝ), (v₁ - v₀) ^ 2 + (v₂ - v₁) ^ 2 + m ^ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2) > m ^ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2)) := by
  (push Not; refine ⟨(3 : ℝ), (3 : ℝ), (3 : ℝ), (3 : ℝ), ?_⟩ <;> norm_num)
```

</details>

## Open (11)

**massive_uniform_gap__gt** (mutation)

```lean
theorem massive_uniform_gap__gt (N : ℕ) (v : ℕ → ℝ) (m : ℝ) : ∑ i ∈ Finset.range N, (v (i + 1) - v i) ^ 2 + m ^ 2 * ∑ i ∈ Finset.range N, v i ^ 2 > m ^ 2 * ∑ i ∈ Finset.range N, v i ^ 2
```

**gap_from_contraction__c0up** (mutation)

```lean
theorem gap_from_contraction__c0up (q τ : ℝ) (hq : 0 < q) (hq1 : q < 1) (hτ : 0 < τ) : 1 < -Real.log q / τ
```

**gap_from_contraction__le** (mutation)

```lean
theorem gap_from_contraction__le (q τ : ℝ) (hq : 0 < q) (hq1 : q < 1) (hτ : 0 < τ) : 0 ≤ -Real.log q / τ
```

**z2_string_tension_pos__c0up** (mutation)

```lean
theorem z2_string_tension_pos__c0up (β : ℝ) (hβ : 0 < β) : 1 < -Real.log (Real.tanh β)
```

**z2_string_tension_pos__le** (mutation)

```lean
theorem z2_string_tension_pos__le (β : ℝ) (hβ : 0 < β) : 0 ≤ -Real.log (Real.tanh β)
```

**path_gap_one_3** (family)

```lean
theorem path_gap_one_3 (v₀ v₁ v₂ : ℝ) (h : v₀ + v₁ + v₂ = 0) : (v₁ - v₀) ^ 2 + (v₂ - v₁) ^ 2 ≥ v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2
```

**path_gap_one_5** (family)

```lean
theorem path_gap_one_5 (v₀ v₁ v₂ v₃ v₄ : ℝ) (h : v₀ + v₁ + v₂ + v₃ + v₄ = 0) : (v₁ - v₀) ^ 2 + (v₂ - v₁) ^ 2 + (v₃ - v₂) ^ 2 + (v₄ - v₃) ^ 2 ≥ v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2 + v₄ ^ 2
```

**massive_uniform_gap__c0up__gt** (mutation)

```lean
theorem massive_uniform_gap__c0up__gt (N : ℕ) (v : ℕ → ℝ) (m : ℝ) : ∑ i ∈ Finset.range N, (v (i + 2) - v i) ^ 2 + m ^ 2 * ∑ i ∈ Finset.range N, v i ^ 2 > m ^ 2 * ∑ i ∈ Finset.range N, v i ^ 2
```

**complete_gap_5__c10up** (mutation)

```lean
theorem complete_gap_5__c10up (v₀ v₁ v₂ v₃ v₄ : ℝ) (h : v₀ + v₁ + v₂ + v₃ + v₄ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₀ - v₃) ^ 2 + (v₀ - v₄) ^ 2 + (v₁ - v₂) ^ 2 + (v₁ - v₃) ^ 2 + (v₁ - v₄) ^ 2 + (v₂ - v₃) ^ 2 + (v₂ - v₄) ^ 2 + (v₃ - v₄) ^ 2 ≥ 6 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2 + v₄ ^ 2)
```

**complete_gap_5__gt** (mutation)

```lean
theorem complete_gap_5__gt (v₀ v₁ v₂ v₃ v₄ : ℝ) (h : v₀ + v₁ + v₂ + v₃ + v₄ = 0) : (v₀ - v₁) ^ 2 + (v₀ - v₂) ^ 2 + (v₀ - v₃) ^ 2 + (v₀ - v₄) ^ 2 + (v₁ - v₂) ^ 2 + (v₁ - v₃) ^ 2 + (v₁ - v₄) ^ 2 + (v₂ - v₃) ^ 2 + (v₂ - v₄) ^ 2 + (v₃ - v₄) ^ 2 > 5 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2 + v₄ ^ 2)
```

**massive_chain_gap_4__gt** (mutation)

```lean
theorem massive_chain_gap_4__gt (v₀ v₁ v₂ v₃ m : ℝ) : (v₁ - v₀) ^ 2 + (v₂ - v₁) ^ 2 + (v₃ - v₂) ^ 2 + m ^ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2) > m ^ 2 * (v₀ ^ 2 + v₁ ^ 2 + v₂ ^ 2 + v₃ ^ 2)
```
