/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.State.MPositiveState
import Mathlib.Tactic.Ring

/-! # Properties of M-Positive States

This file proves additional properties of M-positive states.

## Main results

* `MPositiveState.apply_self_adjoint_add` - φ(a + star a) = 2 * φ(a)
* `MPositiveState.apply_self_adjoint_sub` - φ(a - star a) = 0

## Implementation Notes

With the ℝ-linear structure (RF-4), many properties that previously required
complex proofs are now trivial or follow directly from the structure:

- `map_star` is an axiom: φ(star a) = φ(a)
- All values are real (codomain is ℝ, no `.im = 0` proofs needed)
- Conjugate symmetry is automatic (no complex conjugation involved)

See LEARNINGS.md for the RF-4 design decision.
-/

namespace FreeStarAlgebra

variable {n : ℕ}

namespace MPositiveState

variable (φ : MPositiveState n)

/-- For any element, φ(a + star a) = 2 * φ(a). -/
theorem apply_self_adjoint_add (a : FreeStarAlgebra n) :
    φ (a + star a) = 2 * φ a := by
  rw [φ.map_add, φ.apply_star]
  ring

/-- For any element, φ(a - star a) = 0. -/
theorem apply_self_adjoint_sub (a : FreeStarAlgebra n) :
    φ (a - star a) = 0 := by
  have h1 : φ (a - star a) = φ a - φ (star a) := φ.toFun.map_sub a (star a)
  rw [h1, φ.apply_star, sub_self]

/-- Self-adjoint elements satisfy star a = a, so φ(star a) = φ(a). -/
theorem apply_isSelfAdjoint {a : FreeStarAlgebra n} (ha : IsSelfAdjoint a) :
    φ (star a) = φ a := by
  rw [ha.star_eq]

/-- The real and "imaginary" parts: (a + star a)/2 and (a - star a)/2. -/
theorem apply_decomposition (a : FreeStarAlgebra n) :
    φ a = (1/2 : ℝ) * φ (a + star a) := by
  rw [apply_self_adjoint_add]
  ring

end MPositiveState

end FreeStarAlgebra
