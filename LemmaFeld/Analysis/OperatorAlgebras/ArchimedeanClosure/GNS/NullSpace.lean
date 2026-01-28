/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Boundedness.CauchySchwarzM

/-! # GNS Null Space for M-Positive States

This file defines the GNS null space N_φ = {a : φ(star a * a) = 0} for M-positive states
and proves it is an additive subgroup.

## Main definitions

* `MPositiveState.gnsNullSpace` - The GNS null space as an `AddSubgroup`

## Main results

* `MPositiveState.mem_gnsNullSpace_iff` - Membership characterization
* `MPositiveState.gnsNullSpace_zero_mem` - 0 ∈ N_φ
* `MPositiveState.gnsNullSpace_add_mem` - Closure under addition (uses Cauchy-Schwarz)
* `MPositiveState.gnsNullSpace_neg_mem` - Closure under negation

## Mathematical Background

The null space is the set of elements with zero "length" under the state.
For a ∈ N_φ, we have φ(star a * a) = 0, which by Cauchy-Schwarz implies
φ(star b * a) = 0 for all b. This is key for proving closure under addition.
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} (φ : MPositiveState n)

/-! ### The GNS null space -/

/-- The GNS null space N_φ = {a : φ(star a * a) = 0}.
    This is the set of elements with zero "norm squared" under the state. -/
def gnsNullSpace : AddSubgroup (FreeStarAlgebra n) where
  carrier := {a : FreeStarAlgebra n | φ (star a * a) = 0}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, star_zero, zero_mul]
    exact φ.toFun.map_zero
  add_mem' := fun {a b} ha hb => by
    -- Need: φ(star(a+b) * (a+b)) = 0
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [star_add, add_mul, mul_add, mul_add]
    -- φ(star a * a + star a * b + (star b * a + star b * b))
    rw [φ.map_add, φ.map_add, φ.map_add]
    -- By Cauchy-Schwarz: φ(star a * a) = 0 implies φ(star x * a) = 0 for all x
    have h1 : φ (star a * a) = 0 := ha
    have h2 : φ (star b * b) = 0 := hb
    have h3 : φ (star a * b) = 0 := apply_star_mul_eq_zero_of_apply_star_self_eq_zero φ hb a
    have h4 : φ (star b * a) = 0 := apply_star_mul_eq_zero_of_apply_star_self_eq_zero φ ha b
    simp [h1, h2, h3, h4]
  neg_mem' := fun {a} ha => by
    simp only [Set.mem_setOf_eq] at ha ⊢
    simp [star_neg, ha]

/-- Membership in the GNS null space. -/
theorem mem_gnsNullSpace_iff {a : FreeStarAlgebra n} :
    a ∈ φ.gnsNullSpace ↔ φ (star a * a) = 0 := Iff.rfl

/-- 0 is in the GNS null space. -/
theorem gnsNullSpace_zero_mem : (0 : FreeStarAlgebra n) ∈ φ.gnsNullSpace :=
  φ.gnsNullSpace.zero_mem

/-- The GNS null space is closed under addition. -/
theorem gnsNullSpace_add_mem {a b : FreeStarAlgebra n}
    (ha : a ∈ φ.gnsNullSpace) (hb : b ∈ φ.gnsNullSpace) : a + b ∈ φ.gnsNullSpace :=
  φ.gnsNullSpace.add_mem ha hb

/-- The GNS null space is closed under negation. -/
theorem gnsNullSpace_neg_mem {a : FreeStarAlgebra n}
    (ha : a ∈ φ.gnsNullSpace) : -a ∈ φ.gnsNullSpace :=
  φ.gnsNullSpace.neg_mem ha

/-! ### Left ideal property -/

/-- The GNS null space is closed under left multiplication: if a ∈ N_φ then b * a ∈ N_φ.

This makes N_φ a left ideal. The proof uses the "swapped" Cauchy-Schwarz:
- Need: φ(star(b*a) * (b*a)) = 0 when a ∈ N_φ
- Compute: star(b*a) * (b*a) = star a * star b * b * a = star a * (star b * b * a)
- Apply: φ(star a * x) = 0 for all x when φ(star a * a) = 0 -/
theorem gnsNullSpace_mul_mem_left {a : FreeStarAlgebra n}
    (ha : a ∈ φ.gnsNullSpace) (b : FreeStarAlgebra n) :
    b * a ∈ φ.gnsNullSpace := by
  simp only [mem_gnsNullSpace_iff] at ha ⊢
  -- star(b*a) * (b*a) = star a * star b * b * a = star a * (star b * b * a)
  rw [star_mul, mul_assoc]
  -- φ(star a * (star b * b * a)) = 0 by the swapped Cauchy-Schwarz
  exact apply_mul_star_eq_zero_of_apply_star_self_eq_zero φ ha (star b * (b * a))

/-- Alternative form: left multiplication preserves null space membership. -/
theorem mul_mem_gnsNullSpace_of_mem {a : FreeStarAlgebra n}
    (ha : a ∈ φ.gnsNullSpace) (b : FreeStarAlgebra n) :
    b * a ∈ φ.gnsNullSpace :=
  gnsNullSpace_mul_mem_left φ ha b

/-! ### Scalar closure -/

/-- star (c • a) = c • star a for c : ℝ in FreeStarAlgebra. -/
private lemma star_smul_real (c : ℝ) (a : FreeStarAlgebra n) :
    star (c • a) = c • star a := by
  rw [Algebra.smul_def, Algebra.smul_def, star_mul, FreeAlgebra.star_algebraMap]
  rw [Algebra.commutes]

/-- The GNS null space is closed under ℝ-scalar multiplication. -/
theorem gnsNullSpace_smul_mem {a : FreeStarAlgebra n}
    (ha : a ∈ φ.gnsNullSpace) (c : ℝ) : c • a ∈ φ.gnsNullSpace := by
  simp only [mem_gnsNullSpace_iff] at ha ⊢
  -- star(c • a) * (c • a) = (c • star a) * (c • a) = c² • (star a * a)
  rw [star_smul_real, smul_mul_smul_comm]
  -- φ(c² • (star a * a)) = c² * φ(star a * a) = c² * 0 = 0
  rw [φ.map_smul, ha, mul_zero]

/-! ### The GNS null space as a Submodule -/

/-- The GNS null space as an ℝ-submodule of FreeStarAlgebra.
    This is the correct structure for forming the quotient. -/
def gnsNullIdeal : Submodule ℝ (FreeStarAlgebra n) where
  carrier := {a : FreeStarAlgebra n | φ (star a * a) = 0}
  add_mem' := fun {_ _} ha hb => φ.gnsNullSpace.add_mem ha hb
  zero_mem' := φ.gnsNullSpace.zero_mem
  smul_mem' := fun c {_} ha => gnsNullSpace_smul_mem φ ha c

/-- Membership in gnsNullIdeal is equivalent to membership in gnsNullSpace. -/
theorem mem_gnsNullIdeal_iff {a : FreeStarAlgebra n} :
    a ∈ φ.gnsNullIdeal ↔ φ (star a * a) = 0 := Iff.rfl

/-- The null ideal is a left ideal: if a ∈ N_φ then b * a ∈ N_φ. -/
theorem gnsNullIdeal_mul_mem_left {a : FreeStarAlgebra n}
    (ha : a ∈ φ.gnsNullIdeal) (b : FreeStarAlgebra n) :
    b * a ∈ φ.gnsNullIdeal :=
  gnsNullSpace_mul_mem_left φ ha b

end MPositiveState

end FreeStarAlgebra
