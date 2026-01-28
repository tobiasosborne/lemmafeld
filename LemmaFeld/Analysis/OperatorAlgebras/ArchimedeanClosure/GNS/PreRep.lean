/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Quotient
import Mathlib.Algebra.Algebra.Bilinear

/-! # GNS Pre-Representation for M-Positive States

This file defines the pre-representation π_φ(a) on the GNS quotient A₀/N_φ.

## Main definitions

* `MPositiveState.gnsLeftAction` - Left multiplication action on quotient
* `MPositiveState.gnsPreRep` - Alias for gnsLeftAction

## Main results

* `gnsPreRep_mk` - π_φ(a)[b] = [ab]

## Mathematical Background

The pre-representation is defined as left multiplication: π_φ(a)[b] = [ab].
This is well-defined because N_φ is a left ideal (GNS-2b).
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} (φ : MPositiveState n)

/-! ### Left multiplication action -/

/-- Left multiplication by a as an ℝ-linear map on FreeStarAlgebra. -/
private abbrev mulLeft (a : FreeStarAlgebra n) : FreeStarAlgebra n →ₗ[ℝ] FreeStarAlgebra n :=
  LinearMap.mul ℝ (FreeStarAlgebra n) a

/-- The left multiplication action on the GNS quotient: a • [b] = [a*b].

Well-defined because N_φ is a left ideal: b ∈ N_φ implies a*b ∈ N_φ. -/
def gnsLeftAction (a : FreeStarAlgebra n) : φ.gnsQuotient →ₗ[ℝ] φ.gnsQuotient :=
  φ.gnsNullIdeal.liftQ (φ.gnsQuotientMk ∘ₗ mulLeft a) (by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply]
    rw [gnsQuotientMk_apply, Submodule.Quotient.mk_eq_zero]
    exact gnsNullIdeal_mul_mem_left φ hx a)

/-- The pre-representation is just the left action. -/
abbrev gnsPreRep (a : FreeStarAlgebra n) := φ.gnsLeftAction a

/-! ### Basic properties -/

/-- The left action on representatives: π_φ(a)[b] = [ab]. -/
@[simp]
theorem gnsPreRep_mk (a b : FreeStarAlgebra n) :
    φ.gnsPreRep a (Submodule.Quotient.mk b) = Submodule.Quotient.mk (a * b) := by
  simp only [gnsPreRep, gnsLeftAction, Submodule.liftQ_apply, LinearMap.coe_comp,
    Function.comp_apply, gnsQuotientMk_apply]
  rfl

/-- The pre-representation is additive in the algebra element. -/
theorem gnsPreRep_add (a b : FreeStarAlgebra n) :
    φ.gnsPreRep (a + b) = φ.gnsPreRep a + φ.gnsPreRep b := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := φ.gnsQuotient_mk_surjective x
  simp only [gnsPreRep_mk, add_mul, Submodule.Quotient.mk_add, LinearMap.add_apply]

/-- The pre-representation preserves multiplication. -/
theorem gnsPreRep_mul (a b : FreeStarAlgebra n) :
    φ.gnsPreRep (a * b) = φ.gnsPreRep a ∘ₗ φ.gnsPreRep b := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := φ.gnsQuotient_mk_surjective x
  simp only [gnsPreRep_mk, mul_assoc, LinearMap.coe_comp, Function.comp_apply]

/-- The pre-representation sends 1 to id. -/
theorem gnsPreRep_one : φ.gnsPreRep 1 = LinearMap.id := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨y, rfl⟩ := φ.gnsQuotient_mk_surjective x
  simp only [gnsPreRep_mk, one_mul, LinearMap.id_coe, id_eq]

end MPositiveState

end FreeStarAlgebra
