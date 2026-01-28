/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.State.MPositiveState
import Mathlib.Algebra.FreeAlgebra

/-! # Non-emptiness of S_M

This file proves that the state space S_M is nonempty.

## Main definitions

* `scalarExtraction` - ℝ-linear functional extracting scalar coefficient

## Main results

* `scalarExtraction_star_mul_self_nonneg` - scalar extraction is nonneg on star a * a
* `MPositiveStateSet_nonempty` - S_M ≠ ∅

## Mathematical Background

With FreeStarAlgebra over ℝ (not ℂ), scalar extraction works correctly:
- For any c : ℝ, we have star(c·1) * (c·1) = c² ≥ 0
- This was BLOCKED over ℂ where star(I·1) * (I·1) = -1

See LEARNINGS.md for the full story of why ℝ-algebra is required.
-/

namespace FreeStarAlgebra

variable {n : ℕ}

/-- Scalar extraction: the algebra map inverse, extracting coefficient of 1.

This is `FreeAlgebra.algebraMapInv`, which maps generators to 0 and
extracts the scalar part. -/
noncomputable def scalarExtraction : FreeStarAlgebra n →ₐ[ℝ] ℝ :=
  FreeAlgebra.algebraMapInv

/-- scalarExtraction as a linear map. -/
noncomputable def scalarExtractionLinear : FreeStarAlgebra n →ₗ[ℝ] ℝ :=
  scalarExtraction.toLinearMap

/-- Scalar extraction maps 1 to 1. -/
@[simp]
theorem scalarExtraction_one : scalarExtraction (1 : FreeStarAlgebra n) = 1 := by
  simp [scalarExtraction, FreeAlgebra.algebraMapInv]

/-- Scalar extraction maps generators to 0. -/
@[simp]
theorem scalarExtraction_generator (j : Fin n) : scalarExtraction (generator j) = 0 := by
  simp only [scalarExtraction, generator, FreeAlgebra.algebraMapInv]
  rw [FreeAlgebra.lift_ι_apply]
  rfl

/-- Scalar extraction extracts the scalar part.

For a = algebraMap c + (terms with generators), we have scalarExtraction a = c. -/
theorem scalarExtraction_algebraMap (c : ℝ) :
    scalarExtraction (algebraMap (R := ℝ) (A := FreeStarAlgebra n) c) = c := by
  exact FreeAlgebra.algebraMap_leftInverse c

/-- Scalar extraction commutes with star.

This uses that star reverses words (and fixes scalars/generators), so the
scalar part (coefficient of empty word) is preserved. -/
theorem scalarExtraction_star (a : FreeStarAlgebra n) :
    scalarExtraction (star a) = scalarExtraction a := by
  -- Use induction on the FreeAlgebra structure
  induction a using FreeAlgebra.induction with
  | grade0 c =>
    -- star (algebraMap c) = algebraMap c for ℝ-algebras
    simp only [FreeAlgebra.star_algebraMap]
  | grade1 j =>
    -- star (ι j) = ι j (generators are self-adjoint)
    simp only [FreeAlgebra.star_ι]
  | add a b iha ihb =>
    simp only [star_add, map_add, iha, ihb]
  | mul a b iha ihb =>
    simp only [star_mul, map_mul, iha, ihb, mul_comm]

/-- Scalar extraction gives nonnegative values on star a * a over ℝ.

The key insight: scalarExtraction is an algebra homomorphism, so
  scalarExtraction(star a * a) = scalarExtraction(star a) * scalarExtraction(a)
                                = scalarExtraction(a) * scalarExtraction(a)
                                = scalarExtraction(a)²
And any real squared is nonnegative. -/
theorem scalarExtraction_star_mul_self_nonneg (a : FreeStarAlgebra n) :
    0 ≤ scalarExtraction (star a * a) := by
  -- Use that scalarExtraction is an algebra homomorphism
  rw [map_mul, scalarExtraction_star]
  exact mul_self_nonneg _

/-- Scalar extraction of generator-weighted squares is zero (hence nonnegative).

For star a * g_j * a, the scalar part is 0 since every term contains g_j. -/
theorem scalarExtraction_star_mul_generator_mul_self_nonneg (a : FreeStarAlgebra n) (j : Fin n) :
    0 ≤ scalarExtraction (star a * generator j * a) := by
  -- scalarExtraction of anything containing a generator is 0
  -- since scalarExtraction(g_j) = 0 and it's an algebra hom
  simp only [map_mul, scalarExtraction_generator, mul_zero, zero_mul, le_refl]

/-- Scalar extraction is nonnegative on all elements of the quadratic module.

This uses induction on QuadraticModuleSet membership:
- star a * a: nonneg by scalarExtraction_star_mul_self_nonneg
- star a * g_j * a: zero by scalarExtraction_star_mul_generator_mul_self_nonneg
- sums: sum of nonneg is nonneg
- nonneg scalar multiples: nonneg * nonneg = nonneg
-/
theorem scalarExtraction_m_nonneg {m : FreeStarAlgebra n} (hm : m ∈ QuadraticModule n) :
    0 ≤ scalarExtraction m := by
  induction hm with
  | generator_mem m hgen =>
    -- m ∈ QuadraticModuleGenerators = squareSet ∪ generatorWeightedSet
    rcases hgen with ⟨a, rfl⟩ | ⟨j, b, rfl⟩
    · exact scalarExtraction_star_mul_self_nonneg a
    · exact scalarExtraction_star_mul_generator_mul_self_nonneg b j
  | add_mem _ _ _ _ ih₁ ih₂ =>
    simp only [map_add]
    exact add_nonneg ih₁ ih₂
  | smul_mem c _ hc _ ih =>
    simp only [map_smul, smul_eq_mul]
    exact mul_nonneg hc ih

/-- The scalar extraction functional as an M-positive state.

This constructs an M-positive state by:
- Linear map: scalarExtractionLinear
- Symmetry: scalarExtraction_star
- Normalization: scalarExtraction_one
- M-positivity: scalarExtraction_m_nonneg
-/
noncomputable def scalarState : MPositiveState n where
  toFun := scalarExtractionLinear
  map_star := scalarExtraction_star
  map_one := scalarExtraction_one
  map_m_nonneg := fun _ hm => scalarExtraction_m_nonneg hm

/-- The set S_M of M-positive states is nonempty.

scalarState provides a canonical witness. -/
theorem MPositiveStateSet_nonempty : (MPositiveStateSet n).Nonempty :=
  ⟨scalarState, Set.mem_univ _⟩

end FreeStarAlgebra
