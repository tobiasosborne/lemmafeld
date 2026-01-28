/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.NullSpace.LeftIdeal
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# GNS Quotient Space

This file constructs the quotient A/N_φ with ℂ-module structure and left A-action.

## Main definitions

* `State.gnsNullIdeal` - The GNS null space as a `Submodule ℂ A`
* `State.gnsQuotient` - The quotient A ⧸ N_φ
* `State.gnsQuotientMk` - The quotient map A →ₗ[ℂ] A ⧸ N_φ
* `State.gnsLeftAction` - Left A-action: a • [b] = [a * b]

## Main results

* `State.gnsLeftAction_mk` - gnsLeftAction φ a (mk b) = mk (a * b)
* `State.gnsLeftAction_mul` - gnsLeftAction φ (a * b) = gnsLeftAction φ a ∘ₗ gnsLeftAction φ b
* `State.gnsLeftAction_one` - gnsLeftAction φ 1 = id
* `State.gnsLeftAction_add` - gnsLeftAction φ (a + b) = gnsLeftAction φ a + gnsLeftAction φ b
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### The GNS null space as a submodule -/

/-- The GNS null space as a ℂ-submodule of A. -/
def gnsNullIdeal : Submodule ℂ A where
  carrier := {a : A | φ (star a * a) = 0}
  add_mem' := fun {_ _} ha hb => φ.gnsNullSpace.add_mem ha hb
  zero_mem' := φ.gnsNullSpace.zero_mem
  smul_mem' := fun c {_} ha => gnsNullSpace_smul_mem φ ha c

/-- Membership in gnsNullIdeal is equivalent to membership in gnsNullSpace. -/
theorem mem_gnsNullIdeal_iff {a : A} : a ∈ φ.gnsNullIdeal ↔ φ (star a * a) = 0 := Iff.rfl

/-- The null ideal is a left ideal: if a ∈ N_φ then b * a ∈ N_φ. -/
theorem gnsNullIdeal_mul_mem_left {a : A} (ha : a ∈ φ.gnsNullIdeal) (b : A) :
    b * a ∈ φ.gnsNullIdeal :=
  gnsNullSpace_mul_mem_left φ ha b

/-! ### The quotient space -/

/-- The GNS quotient space A ⧸ N_φ. -/
abbrev gnsQuotient := A ⧸ φ.gnsNullIdeal

/-- The quotient map A →ₗ[ℂ] A ⧸ N_φ. -/
def gnsQuotientMk : A →ₗ[ℂ] φ.gnsQuotient := φ.gnsNullIdeal.mkQ

/-- Apply the quotient map. -/
theorem gnsQuotientMk_apply (a : A) : φ.gnsQuotientMk a = Submodule.Quotient.mk a := rfl

/-! ### Left A-action on the quotient -/

/-- Left multiplication by a : A as a linear map A →ₗ[ℂ] A. -/
def mulLeft (a : A) : A →ₗ[ℂ] A where
  toFun b := a * b
  map_add' _ _ := mul_add a _ _
  map_smul' c b := by simp only [mul_smul_comm, RingHom.id_apply]

/-- Left A-action on the quotient: a • [b] = [a * b].
    Well-defined because N_φ is a left ideal. -/
def gnsLeftAction (a : A) : φ.gnsQuotient →ₗ[ℂ] φ.gnsQuotient :=
  φ.gnsNullIdeal.liftQ (φ.gnsQuotientMk ∘ₗ mulLeft a) (by
    intro x hx
    simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply]
    rw [gnsQuotientMk_apply, Submodule.Quotient.mk_eq_zero]
    exact gnsNullIdeal_mul_mem_left φ hx a)

/-- The left action on representatives. -/
@[simp]
theorem gnsLeftAction_mk (a b : A) :
    φ.gnsLeftAction a (Submodule.Quotient.mk b) = Submodule.Quotient.mk (a * b) := by
  simp only [gnsLeftAction, Submodule.liftQ_apply, LinearMap.coe_comp, Function.comp_apply,
    gnsQuotientMk_apply]
  rfl

/-- The left action is multiplicative. -/
theorem gnsLeftAction_mul (a b : A) :
    φ.gnsLeftAction (a * b) = φ.gnsLeftAction a ∘ₗ φ.gnsLeftAction b := by
  ext x
  -- x : A, goal involves mkQ x
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, gnsLeftAction_mk,
    mul_assoc]

/-- The left action of 1 is the identity. -/
@[simp]
theorem gnsLeftAction_one : φ.gnsLeftAction 1 = LinearMap.id := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, gnsLeftAction_mk,
    one_mul, LinearMap.id_coe, id_eq]

/-- The left action is additive in the algebra element. -/
theorem gnsLeftAction_add (a b : A) :
    φ.gnsLeftAction (a + b) = φ.gnsLeftAction a + φ.gnsLeftAction b := by
  ext x
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, gnsLeftAction_mk,
    add_mul, LinearMap.add_apply, Submodule.Quotient.mk_add]

end State
