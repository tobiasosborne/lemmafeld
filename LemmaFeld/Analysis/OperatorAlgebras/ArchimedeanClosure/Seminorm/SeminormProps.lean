/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Seminorm.StateSeminorm
import Mathlib.Analysis.Seminorm
import Mathlib.Data.Real.Pointwise

/-! # Properties of State Seminorm

This file proves that `stateSeminorm` forms a Seminorm over ℝ.

## Main definitions

* `stateSeminormSeminorm` - The Seminorm ℝ (FreeStarAlgebra n) instance

## Main results

* `stateSeminorm_zero` - ||0||_M = 0
* `stateSeminorm_neg` - ||-a||_M = ||a||_M
* `stateSeminorm_smul` - ||c • a||_M = |c| * ||a||_M
-/

namespace FreeStarAlgebra

variable {n : ℕ}

section Basic
/-! ### Basic properties (no Archimedean needed) -/

/-- The state seminorm maps 0 to 0. -/
theorem stateSeminorm_zero : stateSeminorm (0 : FreeStarAlgebra n) = 0 := by
  unfold stateSeminorm
  have h : ∀ φ : MPositiveState n, |φ 0| = 0 := fun φ => by
    change |φ.toFun 0| = 0
    simp [φ.toFun.map_zero]
  simp_rw [h]
  exact ciSup_const

/-- The state seminorm is symmetric under negation. -/
theorem stateSeminorm_neg (a : FreeStarAlgebra n) :
    stateSeminorm (-a) = stateSeminorm a := by
  unfold stateSeminorm
  congr 1
  ext φ
  change |φ.toFun (-a)| = |φ.toFun a|
  simp [φ.toFun.map_neg, abs_neg]

/-- The state seminorm is homogeneous under ℝ-scalar multiplication. -/
theorem stateSeminorm_smul (c : ℝ) (a : FreeStarAlgebra n) :
    stateSeminorm (c • a) = |c| * stateSeminorm a := by
  unfold stateSeminorm
  by_cases hc : c = 0
  · simp only [hc, zero_smul, abs_zero, zero_mul]
    have h : ∀ φ : MPositiveState n, |φ 0| = 0 := fun φ => by
      change |φ.toFun 0| = 0
      simp [φ.toFun.map_zero]
    simp_rw [h]
    exact ciSup_const
  · have h_eq : ∀ φ : MPositiveState n, |φ (c • a)| = |c| * |φ a| := fun φ => by
      change |φ.toFun (c • a)| = |c| * |φ.toFun a|
      simp [φ.toFun.map_smul, abs_mul]
    simp_rw [h_eq]
    exact (Real.mul_iSup_of_nonneg (abs_nonneg c) _).symm

end Basic

section SeminormInstance
/-! ### Seminorm instance (requires Archimedean for triangle inequality) -/

variable [IsArchimedean n]

/-- The state seminorm as a Seminorm instance. -/
noncomputable def stateSeminormSeminorm : Seminorm ℝ (FreeStarAlgebra n) :=
  Seminorm.of stateSeminorm stateSeminorm_add stateSeminorm_smul

end SeminormInstance

end FreeStarAlgebra
