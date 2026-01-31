/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Chapter 1, Section 1.9: Comodules over Coalgebras

This file defines comodules over coalgebras, following Etingof et al.
"Tensor Categories" §1.9, Definition 1.9.2.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.9

## Main Definitions

* `LeftComodule`: A left comodule over a coalgebra C (Definition 1.9.2)
* `RightComodule`: A right comodule over a coalgebra C (Definition 1.9.2)

## Mathlib Status

As of mathlib v4.26.0, comodules are NOT in mathlib. This file provides the definition.

## Implementation Notes

We follow mathlib's pattern for `Coalgebra`:
- Separate `LeftComoduleStruct` for the data (coaction map)
- `LeftComodule` class adds the axioms (coassociativity, counit)

The axioms match the book exactly:
- Left comodule ρ: M → C ⊗ M with (Δ ⊗ id) ∘ ρ = (id ⊗ ρ) ∘ ρ and (ε ⊗ id) ∘ ρ = id
- Right comodule ρ: M → M ⊗ C with (ρ ⊗ id) ∘ ρ = (id ⊗ Δ) ∘ ρ and (id ⊗ ε) ∘ ρ = id
-/

namespace LemmaFeld.TensorCategories.Chapter1

open scoped TensorProduct

/-! ## §1.9 Definition 1.9.2: Left Comodules

Book: "A left comodule over a coalgebra C is a vector space M together with a
linear map ρ: M → C ⊗ M (called the coaction map), such that for any m ∈ M,
one has (Δ ⊗ id)(ρ(m)) = (id ⊗ ρ)(ρ(m)) and (ε ⊗ id)(ρ(m)) = m."
-/

/-- Data for a left comodule: the coaction map ρ: M → C ⊗ M. -/
class LeftComoduleStruct (R : Type*) (C : Type*) (M : Type*)
    [CommSemiring R]
    [AddCommMonoid C] [Module R C]
    [AddCommMonoid M] [Module R M] where
  /-- The coaction map ρ: M → C ⊗ M -/
  coaction : M →ₗ[R] TensorProduct R C M

/-- A left comodule over a coalgebra C is an R-module M with a coaction ρ: M → C ⊗ M
satisfying coassociativity and counit axioms.

Book Definition 1.9.2: The axioms are:
- (Δ ⊗ id)(ρ(m)) = (id ⊗ ρ)(ρ(m)) [coassociativity]
- (ε ⊗ id)(ρ(m)) = m [counit]
-/
class LeftComodule (R : Type*) (C : Type*) (M : Type*)
    [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M]
    extends LeftComoduleStruct R C M where
  /-- Coassociativity: (Δ ⊗ id) ∘ ρ = (id ⊗ ρ) ∘ ρ (after applying associator) -/
  coassoc : (TensorProduct.assoc R C C M) ∘ₗ (Coalgebra.comul.rTensor M) ∘ₗ coaction =
            (LinearMap.lTensor C coaction) ∘ₗ coaction
  /-- Counit axiom: (ε ⊗ id) ∘ ρ = id (via lid isomorphism) -/
  left_counit : (TensorProduct.lid R M) ∘ₗ (Coalgebra.counit.rTensor M) ∘ₗ coaction =
                LinearMap.id

namespace LeftComodule

variable (R : Type*) (C : Type*) (M : Type*)
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [LeftComodule R C M]

/-- The coaction map ρ: M → C ⊗ M. -/
def coact : M →ₗ[R] TensorProduct R C M := LeftComoduleStruct.coaction

variable {R C M}

@[simp]
theorem coassoc_apply (m : M) :
    TensorProduct.assoc R C C M (Coalgebra.comul.rTensor M (coact R C M m)) =
    LinearMap.lTensor C (coact R C M) (coact R C M m) :=
  LinearMap.congr_fun coassoc m

@[simp]
theorem left_counit_apply (m : M) :
    TensorProduct.lid R M (Coalgebra.counit.rTensor M (coact R C M m)) = m :=
  LinearMap.congr_fun left_counit m

end LeftComodule

/-! ## §1.9 Definition 1.9.2: Right Comodules

Book: "Similarly, a right comodule over C is a vector space M together with a
linear map ρ: M → M ⊗ C, such that for any m ∈ M, one has
(ρ ⊗ id)(ρ(m)) = (id ⊗ Δ)(ρ(m)) and (id ⊗ ε)(ρ(m)) = m."
-/

/-- Data for a right comodule: the coaction map ρ: M → M ⊗ C. -/
class RightComoduleStruct (R : Type*) (C : Type*) (M : Type*)
    [CommSemiring R]
    [AddCommMonoid C] [Module R C]
    [AddCommMonoid M] [Module R M] where
  /-- The coaction map ρ: M → M ⊗ C -/
  coaction : M →ₗ[R] TensorProduct R M C

/-- A right comodule over a coalgebra C is an R-module M with a coaction ρ: M → M ⊗ C
satisfying coassociativity and counit axioms.

Book Definition 1.9.2: The axioms are:
- (ρ ⊗ id)(ρ(m)) = (id ⊗ Δ)(ρ(m)) [coassociativity]
- (id ⊗ ε)(ρ(m)) = m [counit]
-/
class RightComodule (R : Type*) (C : Type*) (M : Type*)
    [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M]
    extends RightComoduleStruct R C M where
  /-- Coassociativity: (ρ ⊗ id) ∘ ρ = (id ⊗ Δ) ∘ ρ (after applying associator) -/
  coassoc : (TensorProduct.assoc R M C C).symm ∘ₗ (Coalgebra.comul.lTensor M) ∘ₗ coaction =
            (LinearMap.rTensor C coaction) ∘ₗ coaction
  /-- Counit axiom: (id ⊗ ε) ∘ ρ = id (via rid isomorphism) -/
  right_counit : (TensorProduct.rid R M) ∘ₗ (Coalgebra.counit.lTensor M) ∘ₗ coaction =
                 LinearMap.id

namespace RightComodule

variable (R : Type*) (C : Type*) (M : Type*)
variable [CommSemiring R]
variable [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable [AddCommMonoid M] [Module R M] [RightComodule R C M]

/-- The coaction map ρ: M → M ⊗ C. -/
def coact : M →ₗ[R] TensorProduct R M C := RightComoduleStruct.coaction

variable {R C M}

@[simp]
theorem coassoc_apply (m : M) :
    (TensorProduct.assoc R M C C).symm (Coalgebra.comul.lTensor M (coact R C M m)) =
    LinearMap.rTensor C (coact R C M) (coact R C M m) :=
  LinearMap.congr_fun coassoc m

@[simp]
theorem right_counit_apply (m : M) :
    TensorProduct.rid R M (Coalgebra.counit.lTensor M (coact R C M m)) = m :=
  LinearMap.congr_fun right_counit m

end RightComodule

/-! ## §1.9: Examples

Book: "For example, C is a left and right comodule over itself with ρ = Δ."
-/

section SelfComodule

variable (R : Type*) (C : Type*)
variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- A coalgebra C is a left comodule over itself with coaction = comultiplication.

Book Example after Definition 1.9.2: "For example, C is a left and right comodule
over itself with ρ = Δ."
-/
instance instLeftComoduleSelf : LeftComodule R C C where
  coaction := Coalgebra.comul
  coassoc := Coalgebra.coassoc
  left_counit := by
    ext c
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.id_coe,
      id_eq]
    rw [Coalgebra.rTensor_counit_comul]
    simp only [TensorProduct.lid_tmul, one_smul]

/-- A coalgebra C is a right comodule over itself with coaction = comultiplication.

Book Example after Definition 1.9.2: "For example, C is a left and right comodule
over itself with ρ = Δ."
-/
instance instRightComoduleSelf : RightComodule R C C where
  coaction := Coalgebra.comul
  coassoc := Coalgebra.coassoc_symm
  right_counit := by
    ext c
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, LinearMap.id_coe,
      id_eq]
    rw [Coalgebra.lTensor_counit_comul]
    simp only [TensorProduct.rid_tmul, one_smul]

end SelfComodule

end LemmaFeld.TensorCategories.Chapter1
