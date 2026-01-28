/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.NullSpace.Basic

/-!
# GNS Null Space is a Left Ideal

This file proves that the GNS null space N_φ is closed under left multiplication,
making it a left ideal of A.

## Main results

* `State.gnsNullSpace_mul_mem_left` - If a ∈ N_φ then b * a ∈ N_φ for all b

## Proof strategy

The proof uses Cauchy-Schwarz in a "swapped" form:
1. We need: φ((ba)*(ba)) = 0 when a ∈ N_φ
2. Compute: (ba)*(ba) = a* b* b a = a* · (b*ba)
3. By Cauchy-Schwarz: |φ(a* · x)|² ≤ φ(x*x).re · φ(a*a).re
4. Since φ(a*a) = 0, we get φ(a* · x) = 0 for all x
5. In particular, φ(a* · (b*ba)) = φ((ba)*(ba)) = 0
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### Cauchy-Schwarz with swapped arguments -/

/-- If φ(a*a) = 0, then φ(a* · x) = 0 for all x.
    This is the "swapped" version of `apply_star_mul_eq_zero_of_apply_star_self_eq_zero`. -/
theorem apply_mul_star_eq_zero_of_apply_star_self_eq_zero {a : A}
    (ha : φ (star a * a) = 0) (x : A) : φ (star a * x) = 0 := by
  -- By Cauchy-Schwarz: |φ(a* · x)|² ≤ φ(x*x).re · φ(a*a).re
  -- Swapping a ↔ x in inner_mul_le_norm_mul_norm gives:
  -- |φ(a* · x)|² ≤ φ(x*x).re · φ(a*a).re
  have h := inner_mul_le_norm_mul_norm φ x a
  simp only [ha, Complex.zero_re, mul_zero] at h
  exact Complex.normSq_eq_zero.mp (le_antisymm h (Complex.normSq_nonneg _))

/-! ### Left ideal property -/

/-- The GNS null space is closed under left multiplication: if a ∈ N_φ then b * a ∈ N_φ. -/
theorem gnsNullSpace_mul_mem_left {a : A} (ha : a ∈ φ.gnsNullSpace) (b : A) :
    b * a ∈ φ.gnsNullSpace := by
  simp only [mem_gnsNullSpace_iff] at ha ⊢
  -- (ba)*(ba) = a* b* b a = a* · (b*ba)
  rw [star_mul, mul_assoc]
  -- φ(a* · (b*ba)) = 0 by the swapped Cauchy-Schwarz
  exact apply_mul_star_eq_zero_of_apply_star_self_eq_zero φ ha (star b * (b * a))

/-- Alternative form: left multiplication preserves null space membership. -/
theorem mul_mem_gnsNullSpace_of_mem {a : A} (ha : a ∈ φ.gnsNullSpace) (b : A) :
    b * a ∈ φ.gnsNullSpace :=
  gnsNullSpace_mul_mem_left φ ha b

end State
