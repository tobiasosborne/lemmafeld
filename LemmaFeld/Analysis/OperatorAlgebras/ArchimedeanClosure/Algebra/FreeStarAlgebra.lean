/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import Mathlib.Algebra.FreeAlgebra
import Mathlib.Algebra.Star.Free
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Data.Real.Basic

/-! # Free *-Algebra with Self-Adjoint Generators

This file defines the free *-algebra on n self-adjoint generators over ℝ.

## Main definitions

* `FreeStarAlgebra n` - Free *-algebra on `Fin n` self-adjoint generators
* `FreeStarAlgebra.generator j` - The j-th generator gⱼ
* `FreeStarAlgebra.isSelfAdjoint_generator` - Generators satisfy star(gⱼ) = gⱼ

## Implementation Notes

We use `FreeAlgebra ℝ (Fin n)` with the star structure from `Mathlib.Algebra.Star.Free`.
Working over ℝ ensures that for any scalar c, star(c·1) * (c·1) = c² ≥ 0, which is
essential for scalar extraction to yield M-positive states.

See LEARNINGS.md for the critical discovery about why ℂ doesn't work.
-/

/-- The free *-algebra on n self-adjoint generators over ℝ. -/
abbrev FreeStarAlgebra (n : ℕ) := FreeAlgebra ℝ (Fin n)

namespace FreeStarAlgebra

variable {n : ℕ}

/-- The j-th generator gⱼ of the free *-algebra. -/
def generator (j : Fin n) : FreeStarAlgebra n := FreeAlgebra.ι ℝ j

/-- Generators are self-adjoint: star(gⱼ) = gⱼ. -/
theorem isSelfAdjoint_generator (j : Fin n) : IsSelfAdjoint (generator j) := by
  unfold IsSelfAdjoint generator
  exact FreeAlgebra.star_ι j

/-- The generator embedding. -/
def ι : Fin n → FreeStarAlgebra n := generator

/-- ι is the same as generator. -/
@[simp]
theorem ι_eq_generator (j : Fin n) : ι j = generator j := rfl

/-- The unit is self-adjoint. -/
theorem one_isSelfAdjoint : IsSelfAdjoint (1 : FreeStarAlgebra n) :=
  IsSelfAdjoint.one _

end FreeStarAlgebra
