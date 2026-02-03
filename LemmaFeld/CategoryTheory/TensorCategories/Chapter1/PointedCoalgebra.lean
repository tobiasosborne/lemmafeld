/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.Comodules
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Chapter 1, Section 1.9.13: Pointed Coalgebras

This file defines pointed coalgebras following Etingof et al.
"Tensor Categories" §1.9, Definition 1.9.13.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.9

## Main Definitions

* `IsRightSubcomodule`: submodule stable under coaction (§1.9)
* `IsSimpleRightComodule`: right comodule with no nontrivial subcomodules
* `IsPointedCoalgebra`: every simple right comodule is 1-dimensional (Def 1.9.13)

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Subcomodule | `IsRightSubcomodule` | NEW: defined below |
| Simple comodule | `IsSimpleRightComodule` | NEW: defined below |
| Pointed coalgebra | `IsPointedCoalgebra` | NEW: Def 1.9.13 |

-/

namespace LemmaFeld.TensorCategories.Chapter1

open scoped TensorProduct

/-! ## Right Subcomodules -/

section Subcomodule

variable (R : Type*) [CommSemiring R]
variable (C : Type*) [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type*} [AddCommMonoid M] [Module R M] [RightComodule R C M]

/-- A submodule S of a right C-comodule M is a right subcomodule if the coaction
maps S into S ⊗ C ⊆ M ⊗ C.

Book §1.9: A subcomodule is a subspace stable under the coaction. -/
def IsRightSubcomodule (S : Submodule R M) : Prop :=
  ∀ s ∈ S, RightComoduleStruct.coaction (R := R) (C := C) s ∈
    Submodule.map₂ (TensorProduct.mk R M C) S ⊤

/-- The zero submodule is a right subcomodule. -/
lemma isRightSubcomodule_bot :
    IsRightSubcomodule R C (⊥ : Submodule R M) := by
  intro s hs
  rw [Submodule.mem_bot] at hs
  subst hs
  simp [map_zero]

/-- The whole module is a right subcomodule. -/
lemma isRightSubcomodule_top :
    IsRightSubcomodule R C (⊤ : Submodule R M) := by
  intro s _
  rw [TensorProduct.map₂_mk_top_top_eq_top]
  exact Submodule.mem_top

end Subcomodule

/-! ## Simple Right Comodules -/

section Simple

variable (R : Type*) [CommSemiring R]
variable (C : Type*) [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable (M : Type*) [AddCommMonoid M] [Module R M] [RightComodule R C M]

/-- A right comodule M is simple if it is nontrivial and every subcomodule
is either zero or the whole module.

Book §1.9.13: Simple comodules are the building blocks for the definition of
pointed coalgebras. -/
class IsSimpleRightComodule [Nontrivial M] : Prop where
  /-- Every subcomodule is trivial. -/
  eq_bot_or_eq_top : ∀ (S : Submodule R M),
    IsRightSubcomodule R C S → S = ⊥ ∨ S = ⊤

end Simple

/-! ## §1.9.13 Definition: Pointed Coalgebra -/

section Pointed

variable (R : Type*) [Field R]
variable (C : Type*) [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- §1.9.13 Definition: A coalgebra C is pointed if any simple right C-comodule
is 1-dimensional.

Book: "A coalgebra C is pointed if any simple right C-comodule is 1-dimensional."

Remark 1.9.14: A finite dimensional coalgebra C is pointed iff C* is basic,
i.e., C*/Rad(C*) is commutative. -/
class IsPointedCoalgebra : Prop where
  /-- Every simple right comodule has dimension 1 over the base field. -/
  finrank_simple_eq_one : ∀ (M : Type*) [AddCommMonoid M] [Module R M]
    [RightComodule R C M] [Nontrivial M] [IsSimpleRightComodule R C M],
    Module.finrank R M = 1

end Pointed

end LemmaFeld.TensorCategories.Chapter1
