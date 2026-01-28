/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Chapter 1, Section 1.1: Categorical Prerequisites and Notation

This file establishes the correspondence between Etingof et al. "Tensor Categories"
§1.1 and mathlib's category theory foundations.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.1

## §1.1 Summary

The book assumes familiarity with basic category theory and introduces notation:

- `id_C` : identity endofunctor
- `C^∨` : dual/opposite category (reversing morphisms)
- Locally small: `Hom_C(X,Y)` is a set
- Essentially small: isomorphism classes form a set (equivalent to a small category)

## Mathlib Correspondence

| Book Notation | Mathlib | Notes |
|---------------|---------|-------|
| `id_C` | `𝟭 C` or `Functor.id C` | Identity functor |
| `C^∨` | `Cᵒᵖ` | Opposite category |
| `Hom_C(X,Y)` | `X ⟶ Y` | Morphism type |
| locally small | `LocallySmall C` | Hom-sets are small |
| essentially small | `EssentiallySmall C` | Equivalent to small category |
| equivalence | `C ≌ D` | `Equivalence C D` type |
| quasi-inverse | `e.inverse` | For `e : C ≌ D` |

-/

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory

/-! ## §1.1: Identity Endofunctor

Book: "The identity endofunctor of a category C will be denoted id_C."

Mathlib: `𝟭 C` (notation) or `Functor.id C` (explicit)
-/

/-- Book notation `id_C` maps to mathlib's identity functor `𝟭 C`. -/
abbrev idFunctor (C : Type*) [Category C] : C ⥤ C := 𝟭 C

/-! ## §1.1: Equivalence of Categories

Book: "We say that a functor F : C → D is an equivalence if there is a functor
F⁻¹ : D → C, called a quasi-inverse of F, such that F⁻¹ ∘ F ≅ id_C and F ∘ F⁻¹ ≅ id_D."

Mathlib: `Equivalence C D` (or notation `C ≌ D`) provides:
- `e.functor : C ⥤ D`
- `e.inverse : D ⥤ C`
- `e.unitIso : 𝟭 C ≅ e.functor ⋙ e.inverse`
- `e.counitIso : e.inverse ⋙ e.functor ≅ 𝟭 D`
-/

-- The type is `CategoryTheory.Equivalence C D`, with notation `C ≌ D`

/-! ## §1.1: Dual/Opposite Category

Book: "We denote by C^∨ the category dual to C, i.e., the one obtained from C
by reversing the direction of morphisms."

Mathlib: `Cᵒᵖ` (the opposite category)
-/

-- The book's C^∨ is mathlib's Cᵒᵖ
-- No additional definition needed; `Opposite` and `Cᵒᵖ` are in Mathlib.CategoryTheory.Opposites

/-! ## §1.1: Locally Small Categories

Book Definition: "A category is called locally small if for any objects X, Y,
Hom_C(X, Y) is a set."

Mathlib: `LocallySmall C` class in `Mathlib.CategoryTheory.Category.Basic`
-/

-- Book's "locally small" = mathlib's `LocallySmall` class
-- Usage: `[LocallySmall C]` as a typeclass assumption

/-! ## §1.1: Essentially Small Categories

Book Definition: "A category is called essentially small if in addition its
isomorphism classes of objects form a set. In other words, an essentially small
category is a category equivalent to a small category."

Mathlib: `EssentiallySmall C` class in `Mathlib.CategoryTheory.EssentiallySmall`

The mathlib definition captures "equivalent to a small category" directly:
```
class EssentiallySmall (C : Type u) [Category.{v} C] : Prop where
  equiv_smallCategory : ∃ (S : Type w) (_ : SmallCategory S), Nonempty (C ≌ S)
```
-/

-- Book's "essentially small" = mathlib's `EssentiallySmall` class
-- Usage: `[EssentiallySmall C]` as a typeclass assumption

/-! ## §1.1: Morphism Notation

Book: "The set of morphisms between X, Y ∈ C will be denoted by Hom_C(X, Y).
An element φ ∈ Hom_C(X, Y) will be usually depicted either as φ : X → Y or as X →^φ Y."

Mathlib: `X ⟶ Y` (typed as `\hom` or `\-->`)
-/

-- Morphism type is `X ⟶ Y` in mathlib
-- Composition is `f ≫ g` (diagrammatic order, not traditional ∘)

/-! ## §1.1: Field Convention

Book: "Unless otherwise specified, all fields are assumed to be algebraically closed."

This is a standing assumption throughout the book. When formalizing later sections,
we will often require `[IsAlgClosed k]` from `Mathlib.FieldTheory.IsAlgClosed.Basic`.
-/

end LemmaFeld.TensorCategories.Chapter1
