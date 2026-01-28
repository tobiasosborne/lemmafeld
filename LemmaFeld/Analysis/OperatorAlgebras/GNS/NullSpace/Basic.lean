/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.State.CauchySchwarzTight

/-!
# GNS Null Space

This file defines the GNS null space N_φ = {a ∈ A : φ(a*a) = 0} and proves it is
an additive subgroup.

## Main definitions

* `State.gnsNullSpace` - The GNS null space as an `AddSubgroup A`

## Main results

* `State.mem_gnsNullSpace_iff` - Membership characterization
* `State.gnsNullSpace.zero_mem` - 0 ∈ N_φ
* `State.gnsNullSpace.add_mem` - Closure under addition (uses Cauchy-Schwarz)
* `State.gnsNullSpace.neg_mem` - Closure under negation
* `State.gnsNullSpace.smul_mem` - Closure under scalar multiplication
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### The GNS null space -/

/-- The GNS null space N_φ = {a ∈ A : φ(a*a) = 0}.
    This is the set of elements with zero "norm squared" under the state. -/
def gnsNullSpace : AddSubgroup A where
  carrier := {a : A | φ (star a * a) = 0}
  zero_mem' := by simp [star_zero, map_zero]
  add_mem' := fun {a b} ha hb => by
    -- Need: φ((a+b)*(a+b)) = 0
    -- Expand: (a+b)*(a+b) = a*a + a*b + b*a + b*b (using star (a+b) = a* + b*)
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [star_add, add_mul, mul_add, mul_add]
    -- Now we have φ(a*a + a*b + (b*a + b*b))
    rw [φ.map_add, φ.map_add, φ.map_add]
    -- By Cauchy-Schwarz: φ(a*a) = 0 implies φ(x*a) = 0 for all x
    have h1 : φ (star a * a) = 0 := ha
    have h2 : φ (star b * b) = 0 := hb
    have h3 : φ (star a * b) = 0 := apply_star_mul_eq_zero_of_apply_star_self_eq_zero φ hb a
    have h4 : φ (star b * a) = 0 := apply_star_mul_eq_zero_of_apply_star_self_eq_zero φ ha b
    simp [h1, h2, h3, h4]
  neg_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    simp [star_neg, ha]

/-- Membership in the GNS null space. -/
theorem mem_gnsNullSpace_iff {a : A} : a ∈ φ.gnsNullSpace ↔ φ (star a * a) = 0 := Iff.rfl

/-- 0 is in the GNS null space. -/
theorem gnsNullSpace_zero_mem : (0 : A) ∈ φ.gnsNullSpace := φ.gnsNullSpace.zero_mem

/-- The GNS null space is closed under addition. -/
theorem gnsNullSpace_add_mem {a b : A} (ha : a ∈ φ.gnsNullSpace) (hb : b ∈ φ.gnsNullSpace) :
    a + b ∈ φ.gnsNullSpace :=
  φ.gnsNullSpace.add_mem ha hb

/-- The GNS null space is closed under negation. -/
theorem gnsNullSpace_neg_mem {a : A} (ha : a ∈ φ.gnsNullSpace) : -a ∈ φ.gnsNullSpace :=
  φ.gnsNullSpace.neg_mem ha

/-- The GNS null space is closed under scalar multiplication. -/
theorem gnsNullSpace_smul_mem {a : A} (ha : a ∈ φ.gnsNullSpace) (c : ℂ) :
    c • a ∈ φ.gnsNullSpace := by
  simp only [mem_gnsNullSpace_iff] at ha ⊢
  rw [star_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  rw [φ.map_smul, ha, mul_zero]

end State
