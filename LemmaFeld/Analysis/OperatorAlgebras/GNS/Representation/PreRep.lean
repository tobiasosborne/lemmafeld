/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.NullSpace.Quotient

/-!
# GNS Pre-Representation

This file defines the pre-representation π_φ(a) on the GNS quotient A/N_φ.

## Main definitions

* `State.gnsPreRep` - The pre-representation π_φ(a) : A/N_φ →ₗ[ℂ] A/N_φ

## Main results

* `State.gnsPreRep_mk` - π_φ(a)[b] = [ab]
* `State.gnsPreRep_mul` - π_φ(ab) = π_φ(a) ∘ π_φ(b)
* `State.gnsPreRep_one` - π_φ(1) = id
* `State.gnsPreRep_add` - π_φ(a+b) = π_φ(a) + π_φ(b)
* `State.gnsPreRep_smul` - π_φ(c•a) = c • π_φ(a)

## Mathematical Background

The pre-representation is defined as left multiplication:
  π_φ(a)[b] = [ab]

This is well-defined because N_φ is a left ideal. At this stage, the
representation is on the pre-Hilbert space (quotient), not the completed
Hilbert space. Extension to the completion is done in later files.
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### Pre-representation definition -/

/-- The GNS pre-representation: π_φ(a) acts on A/N_φ by left multiplication.
    This is the representation before extending to the Hilbert space completion. -/
abbrev gnsPreRep (a : A) : φ.gnsQuotient →ₗ[ℂ] φ.gnsQuotient :=
  φ.gnsLeftAction a

/-! ### Basic properties -/

/-- The pre-representation on representatives: π_φ(a)[b] = [ab]. -/
@[simp]
theorem gnsPreRep_mk (a b : A) :
    φ.gnsPreRep a (Submodule.Quotient.mk b) = Submodule.Quotient.mk (a * b) :=
  φ.gnsLeftAction_mk a b

/-- The pre-representation is multiplicative: π_φ(ab) = π_φ(a) ∘ π_φ(b). -/
theorem gnsPreRep_mul (a b : A) :
    φ.gnsPreRep (a * b) = φ.gnsPreRep a ∘ₗ φ.gnsPreRep b :=
  φ.gnsLeftAction_mul a b

/-- The pre-representation of 1 is the identity: π_φ(1) = id. -/
@[simp]
theorem gnsPreRep_one : φ.gnsPreRep 1 = LinearMap.id :=
  φ.gnsLeftAction_one

/-- The pre-representation is additive: π_φ(a+b) = π_φ(a) + π_φ(b). -/
theorem gnsPreRep_add (a b : A) :
    φ.gnsPreRep (a + b) = φ.gnsPreRep a + φ.gnsPreRep b :=
  φ.gnsLeftAction_add a b

/-- The pre-representation respects scalar multiplication: π_φ(c•a) = c • π_φ(a). -/
theorem gnsPreRep_smul (c : ℂ) (a : A) :
    φ.gnsPreRep (c • a) = c • φ.gnsPreRep a := by
  ext x
  -- x : A, goal involves mkQ x = Submodule.Quotient.mk x
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply,
    gnsPreRep_mk, LinearMap.smul_apply, Submodule.Quotient.mk_smul, smul_mul_assoc]

/-- The pre-representation respects negation: π_φ(-a) = -π_φ(a). -/
theorem gnsPreRep_neg (a : A) : φ.gnsPreRep (-a) = -φ.gnsPreRep a := by
  have h : -a = (-1 : ℂ) • a := by simp
  rw [h, gnsPreRep_smul]
  simp

/-- The pre-representation respects subtraction: π_φ(a-b) = π_φ(a) - π_φ(b). -/
theorem gnsPreRep_sub (a b : A) :
    φ.gnsPreRep (a - b) = φ.gnsPreRep a - φ.gnsPreRep b := by
  rw [sub_eq_add_neg, gnsPreRep_add, gnsPreRep_neg, sub_eq_add_neg]

/-- The pre-representation of 0 is zero: π_φ(0) = 0. -/
@[simp]
theorem gnsPreRep_zero : φ.gnsPreRep 0 = 0 := by
  have h : (0 : A) = (0 : ℂ) • (1 : A) := by simp
  rw [h, gnsPreRep_smul]
  simp

end State
