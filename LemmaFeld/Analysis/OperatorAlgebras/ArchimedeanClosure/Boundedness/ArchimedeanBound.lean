/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Boundedness.CauchySchwarzM
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Algebra.Archimedean
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Archimedean Bound for States

This file proves that M-positive states are bounded using the Archimedean property.

## Main results

* `MPositiveState.apply_star_mul_self_le_bound` - φ(star a * a) ≤ Nₐ
* `MPositiveState.apply_bound` - φ(a)² ≤ Nₐ
* `MPositiveState.apply_abs_le` - |φ(a)| ≤ √Nₐ

## Proof strategy

The Archimedean property gives: N·1 - star a * a ∈ M for some N.
M-positivity gives: φ(N·1 - star a * a) ≥ 0.
By linearity: N·φ(1) - φ(star a * a) ≥ 0, so φ(star a * a) ≤ N.
Combined with Cauchy-Schwarz: |φ(a)|² ≤ φ(star a * a) ≤ N.
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} [IsArchimedean n] (φ : MPositiveState n)

/-- φ(star a * a) ≤ Nₐ from the Archimedean property.

The key steps are:
1. Archimedean: N·1 - star a * a ∈ M
2. M-positivity: φ(N·1 - star a * a) ≥ 0
3. Linearity: N - φ(star a * a) ≥ 0 -/
theorem apply_star_mul_self_le_bound (a : FreeStarAlgebra n) :
    φ (star a * a) ≤ archimedeanBound a := by
  have hmem := archimedeanBound_spec a
  have hpos := φ.apply_m_nonneg hmem
  -- Expand φ(N·1 - star a * a) = N * φ(1) - φ(star a * a) = N - φ(star a * a)
  have hlin : φ ((archimedeanBound a : ℝ) • (1 : FreeStarAlgebra n) - star a * a) =
      (archimedeanBound a : ℝ) - φ (star a * a) := by
    simp only [sub_eq_add_neg, φ.map_add, φ.map_smul, φ.apply_one, mul_one]
    congr 1
    exact φ.toFun.map_neg _
  rw [hlin] at hpos
  linarith

/-- Combined bound: φ(a)² ≤ Nₐ.

This follows from Cauchy-Schwarz: φ(a)² ≤ φ(star a * a) ≤ Nₐ -/
theorem apply_bound (a : FreeStarAlgebra n) :
    φ a ^ 2 ≤ archimedeanBound a := by
  calc φ a ^ 2 ≤ φ (star a * a) := φ.apply_sq_le a
    _ ≤ archimedeanBound a := φ.apply_star_mul_self_le_bound a

/-- |φ(a)| ≤ √Nₐ.

This is the bound needed for compactness of the state space. -/
theorem apply_abs_le (a : FreeStarAlgebra n) :
    |φ a| ≤ Real.sqrt (archimedeanBound a) := by
  apply abs_le_of_sq_le_sq _ (Real.sqrt_nonneg _)
  calc (φ a) ^ 2 ≤ archimedeanBound a := φ.apply_bound a
    _ = Real.sqrt (archimedeanBound a) ^ 2 := by
        rw [Real.sq_sqrt (Nat.cast_nonneg _)]

end MPositiveState

end FreeStarAlgebra
