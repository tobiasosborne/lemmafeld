/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Dual.ComplexExtension

/-! # Normalization to M-Positive State

This file normalizes the symmetric separating functional to get an MPositiveState.

## Main results

* `phi_one_pos` - For symmetric φ with φ ≥ 0 on M and φ(A) < 0, we have φ(1) > 0
* `normalizedMPositiveState` - Normalize φ by φ(1) to get an MPositiveState
* `exists_MPositiveState_negative` - Combined: ∃ MPositiveState with φ(A) < 0

## Proof Strategy for φ(1) > 0

**Case φ(1) = 0:** By Cauchy-Schwarz, φ(a)² ≤ φ(star a * a) * φ(1) = 0 for all a.
Thus φ(a) = 0 for all a, contradicting φ(A) < 0.

**Case φ(1) < 0:** By Archimedean: N·1 - star(A)*A ∈ M for some N.
Then N·φ(1) ≥ φ(star A * A) ≥ 0. Since φ(1) < 0, we need N = 0 and φ(star A * A) = 0.
By Cauchy-Schwarz: φ(A)² ≤ φ(star A * A) * φ(1) = 0, so φ(A) = 0. Contradiction.
-/

namespace FreeStarAlgebra

variable {n : ℕ} [IsArchimedean n]

/-! ### Cauchy-Schwarz for Symmetric Functionals -/

set_option linter.unusedSectionVars false in
/-- Cauchy-Schwarz for symmetric M-nonneg functional: φ(a)² ≤ φ(star a * a) * φ(1).

This is proved by expanding φ(star(a + t·1) * (a + t·1)) ≥ 0 and using discriminant. -/
private theorem cauchy_schwarz_general (φ : FreeStarAlgebra n →ₗ[ℝ] ℝ)
    (hφ_symm : ∀ a, φ (star a) = φ a)
    (hφ_nonneg : ∀ m ∈ QuadraticModule n, 0 ≤ φ m)
    (a : FreeStarAlgebra n) :
    φ a ^ 2 ≤ φ (star a * a) * φ 1 := by
  -- Quadratic in t: φ(star(a + t·1) * (a + t·1)) ≥ 0
  have hquad : ∀ t : ℝ, 0 ≤ φ (star (a + t • (1 : FreeStarAlgebra n)) * (a + t • 1)) := fun t =>
    hφ_nonneg _ (star_mul_self_mem _)
  -- star(a + t·1) = star a + t·1
  have hstar : ∀ t : ℝ, star (a + t • (1 : FreeStarAlgebra n)) = star a + t • 1 := fun t => by
    rw [star_add]
    congr 1
    rw [Algebra.smul_def, star_mul, FreeAlgebra.star_algebraMap, star_one, Algebra.commutes]
  -- Expansion: (star a + t·1)(a + t·1) = star a * a + t * a + t * star a + t² * 1
  have hexp : ∀ t : ℝ, φ (star (a + t • (1 : FreeStarAlgebra n)) * (a + t • 1)) =
      φ (star a * a) + 2 * t * φ a + t^2 * φ 1 := by
    intro t
    rw [hstar]
    -- Expand (star a + t • 1) * (a + t • 1) step by step
    have hmul : (star a + t • (1 : FreeStarAlgebra n)) * (a + t • 1) =
        star a * a + t • a + t • star a + t^2 • (1 : FreeStarAlgebra n) := by
      simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_add]
      rw [sq, smul_smul]
      abel
    rw [hmul]
    simp only [φ.map_add, φ.map_smul, smul_eq_mul]
    rw [hφ_symm a]
    ring
  -- Rewrite as standard quadratic form
  have hquad' : ∀ t : ℝ, 0 ≤ φ 1 * t^2 + 2 * φ a * t + φ (star a * a) := fun t => by
    have := hquad t; rw [hexp] at this; linarith
  by_cases h1 : φ 1 = 0
  · -- If φ(1) = 0, the "quadratic" is linear: 2 * φ a * t + φ(star a * a) ≥ 0 for all t
    simp only [h1, zero_mul, zero_add] at hquad'
    -- For this to hold for all t, we need φ a = 0
    have hpos : φ (star a * a) ≥ 0 := hφ_nonneg _ (star_mul_self_mem a)
    by_cases ha : φ a = 0
    · simp only [ha, h1, mul_zero, sq, le_refl]
    · -- φ a ≠ 0, so we can pick t to make 2 * φ a * t + φ(star a * a) < 0
      exfalso
      have ht := hquad' (-(φ (star a * a) + 1) / (2 * φ a))
      have hne2 : (2 : ℝ) * φ a ≠ 0 := mul_ne_zero two_ne_zero ha
      have hdiv := div_mul_cancel₀ (-(φ (star a * a) + 1)) hne2
      linarith
  · -- Standard discriminant bound
    have hquad'' : ∀ t : ℝ, 0 ≤ φ 1 * (t * t) + 2 * φ a * t + φ (star a * a) := fun t => by
      have := hquad' t; simp only [sq] at this; exact this
    have hdiscrim := discrim_le_zero hquad''
    unfold discrim at hdiscrim
    nlinarith [sq_nonneg (φ a)]

/-! ### φ(1) > 0 -/

/-- For symmetric φ with φ ≥ 0 on M and φ(A) < 0, we have φ(1) > 0. -/
theorem phi_one_pos {φ : FreeStarAlgebra n →ₗ[ℝ] ℝ}
    (hφ_symm : ∀ a, φ (star a) = φ a)
    (hφ_nonneg : ∀ m ∈ QuadraticModule n, 0 ≤ φ m)
    {A : FreeStarAlgebra n} (_hA : IsSelfAdjoint A) (hφA : φ A < 0) :
    0 < φ 1 := by
  by_contra h
  push_neg at h
  rcases h.lt_or_eq with h1_neg | h1_zero
  · -- Case φ(1) < 0
    -- By Archimedean: N·1 - star(A)*A ∈ M
    obtain ⟨N, hN⟩ := IsArchimedean.bound A
    have hineq : N * φ 1 - φ (star A * A) ≥ 0 := by
      calc N * φ 1 - φ (star A * A)
          = φ ((N : ℝ) • 1 - star A * A) := by simp [φ.map_sub, φ.map_smul]
        _ ≥ 0 := hφ_nonneg _ hN
    have hAA_nonneg : φ (star A * A) ≥ 0 := hφ_nonneg _ (star_mul_self_mem A)
    -- Since φ(1) < 0 and N ≥ 0, we have N * φ(1) ≤ 0
    have hN_nonneg : (N : ℝ) ≥ 0 := Nat.cast_nonneg N
    have hprod_nonpos : N * φ 1 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hN_nonneg (le_of_lt h1_neg)
    -- Combined: 0 ≤ N * φ(1) - φ(star A * A) and N * φ(1) ≤ 0 and φ(star A * A) ≥ 0
    have hAA_zero : φ (star A * A) = 0 := by linarith
    -- By Cauchy-Schwarz: φ(A)² ≤ φ(star A * A) * φ(1) = 0
    have hCS := cauchy_schwarz_general φ hφ_symm hφ_nonneg A
    rw [hAA_zero, zero_mul] at hCS
    have hA_zero : φ A = 0 := by nlinarith [sq_nonneg (φ A)]
    linarith
  · -- Case φ(1) = 0
    have hCS := cauchy_schwarz_general φ hφ_symm hφ_nonneg A
    rw [h1_zero, mul_zero] at hCS
    have hA_zero : φ A = 0 := by nlinarith [sq_nonneg (φ A)]
    linarith

/-! ### Normalized MPositiveState -/

/-- Construct an MPositiveState by normalizing φ. -/
noncomputable def normalizedMPositiveState {φ : FreeStarAlgebra n →ₗ[ℝ] ℝ}
    (hφ_symm : ∀ a, φ (star a) = φ a)
    (hφ_nonneg : ∀ m ∈ QuadraticModule n, 0 ≤ φ m)
    (hφ1_pos : 0 < φ 1) : MPositiveState n where
  toFun := (φ 1)⁻¹ • φ
  map_star a := by simp [hφ_symm a]
  map_one := by simp [inv_mul_cancel₀ (ne_of_gt hφ1_pos)]
  map_m_nonneg m hm := by
    simp only [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr (le_of_lt hφ1_pos)) (hφ_nonneg m hm)

omit [IsArchimedean n] in
/-- The normalized state preserves the sign on A. -/
theorem normalizedMPositiveState_negative {φ : FreeStarAlgebra n →ₗ[ℝ] ℝ}
    (hφ_symm : ∀ a, φ (star a) = φ a)
    (hφ_nonneg : ∀ m ∈ QuadraticModule n, 0 ≤ φ m)
    (hφ1_pos : 0 < φ 1)
    {A : FreeStarAlgebra n} (hφA : φ A < 0) :
    (normalizedMPositiveState hφ_symm hφ_nonneg hφ1_pos) A < 0 := by
  change (φ 1)⁻¹ * φ A < 0
  exact mul_neg_of_pos_of_neg (inv_pos.mpr hφ1_pos) hφA

/-! ### Main Theorem: Existence of Negative MPositiveState -/

/-- For A ∉ M̄, there exists an MPositiveState φ with φ(A) < 0. -/
theorem exists_MPositiveState_negative {A : FreeStarAlgebra n}
    (hA : IsSelfAdjoint A) (hA_not : A ∉ quadraticModuleClosure) :
    ∃ φ : MPositiveState n, φ A < 0 := by
  -- Get symmetric separating functional from ComplexExtension
  obtain ⟨ψ, hψ_symm, hψ_nonneg, hψ_neg⟩ := symmetrize_separation hA hA_not
  -- Show ψ(1) > 0
  have hψ1_pos : 0 < ψ 1 := phi_one_pos hψ_symm hψ_nonneg hA hψ_neg
  -- Normalize to get MPositiveState
  exact ⟨normalizedMPositiveState hψ_symm hψ_nonneg hψ1_pos,
    normalizedMPositiveState_negative hψ_symm hψ_nonneg hψ1_pos hψ_neg⟩

end FreeStarAlgebra
