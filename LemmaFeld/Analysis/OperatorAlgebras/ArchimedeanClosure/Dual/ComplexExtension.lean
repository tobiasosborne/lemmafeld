/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Dual.RieszApplication
import Mathlib.Tactic.Ring

/-! # Symmetrization of Real Functional

This file symmetrizes the real linear functional from `riesz_extension_exists`
to create a functional satisfying φ(star a) = φ(a).

## Main results

* `starAsLinearMap` - Star operation as an ℝ-linear map
* `symmetrize` - Given ψ : A₀ →ₗ[ℝ] ℝ, produces φ with φ(star a) = φ(a)
* `symmetrize_separation` - Combined symmetrized separating functional

## Mathematical Background

The separation theorem gives us ψ : A₀ →ₗ[ℝ] ℝ with ψ ≥ 0 on M and ψ(A) < 0.
However, MPositiveState requires symmetry: φ(star a) = φ(a).

The symmetrization φ(a) = (ψ(a) + ψ(star a))/2 satisfies:
1. φ(star a) = (ψ(star a) + ψ(a))/2 = φ(a) ✓
2. For m ∈ M (self-adjoint): φ(m) = ψ(m) ≥ 0 ✓
3. For A self-adjoint: φ(A) = ψ(A) < 0 ✓

## Key Technical Detail

The star operation on FreeAlgebra ℝ (Fin n) is ℝ-linear because:
- star(a + b) = star a + star b (star_add)
- star(c • a) = c • star a (using FreeAlgebra.star_algebraMap: star of ℝ-scalar is itself)
-/

namespace FreeStarAlgebra

variable {n : ℕ}

/-- Star operation as an ℝ-linear map on FreeStarAlgebra.

This uses that for r : ℝ, we have star(algebraMap r) = algebraMap r
by `FreeAlgebra.star_algebraMap`. -/
noncomputable def starAsLinearMap : FreeStarAlgebra n →ₗ[ℝ] FreeStarAlgebra n where
  toFun := star
  map_add' := star_add
  map_smul' := fun c a => by
    rw [Algebra.smul_def, Algebra.smul_def, star_mul, FreeAlgebra.star_algebraMap]
    rw [Algebra.commutes]
    simp only [RingHom.id_apply]

@[simp]
theorem starAsLinearMap_apply (a : FreeStarAlgebra n) : starAsLinearMap a = star a := rfl

/-- Symmetrize an ℝ-linear functional: φ(a) = (ψ(a) + ψ(star a))/2 -/
noncomputable def symmetrize (ψ : FreeStarAlgebra n →ₗ[ℝ] ℝ) :
    FreeStarAlgebra n →ₗ[ℝ] ℝ :=
  (1/2 : ℝ) • (ψ + ψ.comp starAsLinearMap)

/-- Symmetrization is symmetric: φ(star a) = φ(a) -/
theorem symmetrize_map_star (ψ : FreeStarAlgebra n →ₗ[ℝ] ℝ) (a : FreeStarAlgebra n) :
    symmetrize ψ (star a) = symmetrize ψ a := by
  simp only [symmetrize, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    starAsLinearMap_apply, star_star]
  ring

/-- On self-adjoint elements, symmetrization equals original -/
theorem symmetrize_eq_of_selfAdjoint (ψ : FreeStarAlgebra n →ₗ[ℝ] ℝ)
    {a : FreeStarAlgebra n} (ha : IsSelfAdjoint a) :
    symmetrize ψ a = ψ a := by
  simp only [symmetrize, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply,
    starAsLinearMap_apply, ha.star_eq, smul_eq_mul]
  ring

/-- c • m is self-adjoint when m is self-adjoint, for c : ℝ. -/
theorem isSelfAdjoint_smul_of_isSelfAdjoint {m : FreeStarAlgebra n}
    (hm : IsSelfAdjoint m) (c : ℝ) : IsSelfAdjoint (c • m) := by
  unfold IsSelfAdjoint at *
  rw [Algebra.smul_def, star_mul, FreeAlgebra.star_algebraMap, hm, Algebra.commutes]

variable [hArch : IsArchimedean n]

omit hArch in
/-- Elements of M are self-adjoint.

This follows from the definition: squares star(a)*a and generator-weighted
squares star(b)*gⱼ*b are both self-adjoint. The property is preserved by
addition and nonnegative scaling. -/
theorem isSelfAdjoint_of_mem_quadraticModule {m : FreeStarAlgebra n}
    (hm : m ∈ QuadraticModule n) : IsSelfAdjoint m := by
  induction hm with
  | generator_mem m hm =>
    cases hm with
    | inl hsq =>
      obtain ⟨a, rfl⟩ := hsq
      unfold IsSelfAdjoint
      simp only [star_mul, star_star]
    | inr hgen =>
      obtain ⟨j, b, rfl⟩ := hgen
      unfold IsSelfAdjoint
      simp only [star_mul, star_star, (isSelfAdjoint_generator j).star_eq, mul_assoc]
  | add_mem _ _ _ _ ih1 ih2 =>
    exact ih1.add ih2
  | smul_mem c _ _ _ ih =>
    exact isSelfAdjoint_smul_of_isSelfAdjoint ih c

omit hArch in
/-- Symmetrization preserves nonnegativity on M -/
theorem symmetrize_nonneg_on_M (ψ : FreeStarAlgebra n →ₗ[ℝ] ℝ)
    (hψ : ∀ m ∈ QuadraticModule n, 0 ≤ ψ m) :
    ∀ m ∈ QuadraticModule n, 0 ≤ symmetrize ψ m := by
  intro m hm
  rw [symmetrize_eq_of_selfAdjoint ψ (isSelfAdjoint_of_mem_quadraticModule hm)]
  exact hψ m hm

omit hArch in
/-- Symmetrization preserves negativity on self-adjoint elements -/
theorem symmetrize_neg_of_selfAdjoint (ψ : FreeStarAlgebra n →ₗ[ℝ] ℝ)
    {A : FreeStarAlgebra n} (hA : IsSelfAdjoint A) (hψA : ψ A < 0) :
    symmetrize ψ A < 0 := by
  rw [symmetrize_eq_of_selfAdjoint ψ hA]
  exact hψA

/-- Combined result: symmetrization of separation functional gives symmetric functional
with same properties on M and A -/
theorem symmetrize_separation {A : FreeStarAlgebra n}
    (hA : IsSelfAdjoint A) (hA_not : A ∉ quadraticModuleClosure) :
    ∃ φ : FreeStarAlgebra n →ₗ[ℝ] ℝ,
      (∀ a, φ (star a) = φ a) ∧
      (∀ m ∈ QuadraticModule n, 0 ≤ φ m) ∧
      φ A < 0 := by
  obtain ⟨ψ, hψ_nonneg, hψ_neg⟩ := riesz_extension_exists hA hA_not
  refine ⟨symmetrize ψ, symmetrize_map_star ψ, symmetrize_nonneg_on_M ψ hψ_nonneg, ?_⟩
  exact symmetrize_neg_of_selfAdjoint ψ hA hψ_neg

end FreeStarAlgebra
