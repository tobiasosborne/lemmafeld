/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.PreHilbert.Seminorm

/-!
# GNS Positive Definiteness

This file proves positive definiteness of the GNS inner product on the quotient.

## Main results

* `State.gnsInner_self_eq_zero_iff` - ⟨x, x⟩ = 0 ↔ x = 0 (positive definiteness)
* `State.gnsInner_pos_def` - x ≠ 0 → 0 < (⟨x, x⟩).re

## Note

Some basic properties (`gnsInner_self_nonneg`, `gnsInner_self_im`, `gnsInner_self_eq_re`)
are in Seminorm.lean since they're needed for the PreInnerProductSpace.Core instance.
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### Positive definiteness -/

/-- Positive definiteness: ⟨x, x⟩ = 0 iff x = 0 in the quotient.
    This is the crucial property that makes A ⧸ N_φ a pre-inner product space. -/
theorem gnsInner_self_eq_zero_iff (x : φ.gnsQuotient) :
    φ.gnsInner x x = 0 ↔ x = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal x
  simp only [gnsInner_mk]
  rw [Submodule.Quotient.mk_eq_zero]
  exact mem_gnsNullIdeal_iff φ

/-- If x ≠ 0, then ⟨x, x⟩.re > 0. -/
theorem gnsInner_pos_def {x : φ.gnsQuotient} (hx : x ≠ 0) :
    0 < (φ.gnsInner x x).re := by
  have h_nonneg := gnsInner_self_nonneg φ x
  have h_ne_zero : φ.gnsInner x x ≠ 0 := by
    intro h
    exact hx ((gnsInner_self_eq_zero_iff φ x).mp h)
  rcases h_nonneg.lt_or_eq with h_lt | h_eq
  · exact h_lt
  · exfalso
    apply h_ne_zero
    apply Complex.ext
    · exact h_eq.symm
    · exact gnsInner_self_im φ x

/-- The norm is zero iff the element is zero. -/
theorem gnsNorm_eq_zero_iff (x : φ.gnsQuotient) :
    φ.gnsNorm x = 0 ↔ x = 0 := by
  unfold gnsNorm
  rw [Real.sqrt_eq_zero (gnsInner_self_nonneg φ x)]
  constructor
  · intro h_re
    rw [← gnsInner_self_eq_zero_iff φ x]
    apply Complex.ext
    · exact h_re
    · exact gnsInner_self_im φ x
  · intro hx
    simp [hx]

/-- If x ≠ 0, then ‖x‖ > 0. -/
theorem gnsNorm_pos {x : φ.gnsQuotient} (hx : x ≠ 0) : 0 < φ.gnsNorm x := by
  have h : φ.gnsNorm x ≠ 0 := mt (gnsNorm_eq_zero_iff φ x).mp hx
  exact (gnsNorm_nonneg φ x).lt_of_ne' h

end State
