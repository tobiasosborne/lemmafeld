/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.EssentiallySmall
import Mathlib.CategoryTheory.Skeletal

/-!
# Chapter 1, Section 1.1: Locally Small and Essentially Small Categories

This file documents the `LocallySmall` and `EssentiallySmall` APIs from mathlib,
corresponding to the size conditions in §1.1 of Etingof et al.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.1

## Book Definitions

> "A category is called *locally small* if for any objects X, Y, Hom_C(X, Y) is a set,
> and is called *essentially small* if in addition its isomorphism classes of objects
> form a set. In other words, an essentially small category is a category equivalent
> to a small category."

## Mathlib Correspondence

| Book Concept | Mathlib | Description |
|--------------|---------|-------------|
| Locally small | `LocallySmall C` | Hom-sets are small (fit in universe w) |
| Essentially small | `EssentiallySmall C` | Equivalent to a small category |
| Small category | `SmallCategory C` | Objects and morphisms in same universe |

## Key APIs

### LocallySmall
- `LocallySmall.hom_small` : ∀ X Y, Small (X ⟶ Y)
- `locallySmall_self` : every category is locally small at its morphism universe
- `locallySmall_congr` : LocallySmall preserved by equivalences
- `locallySmall_of_faithful` : transfers along faithful functors

### EssentiallySmall
- `EssentiallySmall.equiv_smallCategory` : ∃ S [SmallCategory S], Nonempty (C ≌ S)
- `equivSmallModel` : canonical equivalence to a small model
- `essentiallySmall_congr` : EssentiallySmall preserved by equivalences
- `essentiallySmall_iff` : ↔ skeleton is small ∧ locally small

-/

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory

/-! ## LocallySmall: Hom-sets are sets

Book: "A category is called locally small if for any objects X, Y, Hom_C(X, Y) is a set."

Mathlib interprets "is a set" as fitting in a specified universe w.
The class `LocallySmall.{w} C` means `∀ X Y : C, Small.{w} (X ⟶ Y)`.
-/

section LocallySmallAPI

variable {C : Type u} [Category.{v} C]

-- Every category is locally small at its own morphism universe
#check (locallySmall_self C : LocallySmall.{v} C)

-- LocallySmall is preserved by equivalences
example {D : Type*} [Category D] (e : C ≌ D) [LocallySmall.{w} C] : LocallySmall.{w} D :=
  (locallySmall_congr e).mp inferInstance

-- LocallySmall transfers along faithful functors
example {D : Type*} [Category D] (F : C ⥤ D) [F.Faithful] [LocallySmall.{w} D] :
    LocallySmall.{w} C :=
  locallySmall_of_faithful F

-- Opposite category inherits LocallySmall
example [LocallySmall.{w} C] : LocallySmall.{w} Cᵒᵖ := inferInstance

end LocallySmallAPI

/-! ## EssentiallySmall: Equivalent to a small category

Book: "A category is called essentially small if in addition its isomorphism classes
of objects form a set. In other words, an essentially small category is a category
equivalent to a small category."

Mathlib captures "equivalent to a small category" directly:
`∃ (S : Type w) (_ : SmallCategory S), Nonempty (C ≌ S)`
-/

section EssentiallySmallAPI

universe w

variable {C : Type u} [Category.{v} C]

-- When C is essentially small, we get a canonical small model
#check (SmallModel : (C : Type u) → [Category.{v} C] → [EssentiallySmall.{w} C] → Type w)

-- And an equivalence to it
#check (equivSmallModel : (C : Type u) → [Category.{v} C] →
    [EssentiallySmall.{w} C] → C ≌ SmallModel.{w} C)

-- EssentiallySmall is preserved by equivalences
example {D : Type*} [Category D] (e : C ≌ D) [EssentiallySmall.{w} C] :
    EssentiallySmall.{w} D :=
  (essentiallySmall_congr e).mp inferInstance

-- Characterization: EssentiallySmall ↔ skeleton is small ∧ locally small
#check (essentiallySmall_iff C : EssentiallySmall.{w} C ↔
    Small.{w} (Skeleton C) ∧ LocallySmall.{w} C)

-- EssentiallySmall implies LocallySmall
example [EssentiallySmall.{w} C] : LocallySmall.{w} C :=
  locallySmall_of_essentiallySmall C

-- Opposite category inherits EssentiallySmall
example [EssentiallySmall.{w} C] : EssentiallySmall.{w} Cᵒᵖ := inferInstance

-- Constructing EssentiallySmall from an equivalence to a small category
example {S : Type w} [SmallCategory S] (e : C ≌ S) : EssentiallySmall.{w} C :=
  EssentiallySmall.mk' e

end EssentiallySmallAPI

/-! ## Book Context

The book notes that "All categories considered in this book will be locally small
(except in the section on 2-categories), and most of them will be essentially small.
So set-theoretical subtleties will not play any role in this book."

In Lean/mathlib, these conditions are tracked via typeclasses, which makes universe
management explicit but straightforward.
-/

end LemmaFeld.TensorCategories.Chapter1
