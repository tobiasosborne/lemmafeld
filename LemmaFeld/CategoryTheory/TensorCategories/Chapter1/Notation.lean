/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Category
import Mathlib.CategoryTheory.Opposites

/-!
# Chapter 1, Section 1.1: Notation Conventions

This file documents the notation conventions used in Etingof et al. "Tensor Categories"
and their correspondence to mathlib notation.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.1

## Notation Comparison

| Concept | Book Notation | Mathlib Notation | Notes |
|---------|---------------|------------------|-------|
| Object membership | `X ∈ C` | `X : C` | Lean type membership |
| Morphism set | `Hom_C(X,Y)` | `X ⟶ Y` | `\hom` or `\-->` |
| Morphism element | `φ ∈ Hom(X,Y)` | `φ : X ⟶ Y` | |
| Composition | `g ∘ f` or `gf` | `f ≫ g` | **Order reversed!** |
| Identity | `id_X` | `𝟙 X` | `\b1` |
| Identity functor | `id_C` | `𝟭 C` | `\b1` |
| Dual category | `C^∨` | `Cᵒᵖ` | `\^op` |
| Functor application | `F(X)` | `F.obj X` | |
| Functor on morphisms | `F(f)` | `F.map f` | |
| Natural transformation | `η : F → G` | `η : F ⟶ G` | Same as morphisms |
| Isomorphism | `X ≅ Y` | `X ≅ Y` | Same notation |
| Equivalence | `C ≃ D` | `C ≌ D` | `\cmark` for mathlib |

## Important: Composition Order

The book uses traditional composition order: `g ∘ f` means "first f, then g".

Mathlib uses **diagrammatic order**: `f ≫ g` means "first f, then g".

So `g ∘ f` in the book corresponds to `f ≫ g` in mathlib.

-/

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory

/-! ## Morphism Notation

Book: "An element φ ∈ Hom_C(X,Y) will be usually depicted either as φ : X → Y
or as X →^φ Y."

In mathlib, morphisms use the `⟶` arrow (typed as `\hom` or `\-->`).
-/

section MorphismExamples

variable {C : Type*} [Category C] {X Y Z : C}

-- Book: φ : X → Y
-- Mathlib: φ : X ⟶ Y
example (φ : X ⟶ Y) : X ⟶ Y := φ

-- Book: composition g ∘ f (traditional order)
-- Mathlib: f ≫ g (diagrammatic order)
example (f : X ⟶ Y) (g : Y ⟶ Z) : X ⟶ Z := f ≫ g

-- Book: id_X
-- Mathlib: 𝟙 X
example : X ⟶ X := 𝟙 X

-- Composition with identity
example (f : X ⟶ Y) : f ≫ 𝟙 Y = f := Category.comp_id f
example (f : X ⟶ Y) : 𝟙 X ≫ f = f := Category.id_comp f

end MorphismExamples

/-! ## Functor Notation

Book: "The identity endofunctor of a category C will be denoted id_C."

Mathlib: `𝟭 C` (typed as `\b1 C`) or `Functor.id C`
-/

section FunctorExamples

variable {C D : Type*} [Category C] [Category D]

-- Book: id_C
-- Mathlib: 𝟭 C
example : C ⥤ C := 𝟭 C

-- Functor application on objects
-- Book: F(X)
-- Mathlib: F.obj X
example (F : C ⥤ D) (X : C) : D := F.obj X

-- Functor application on morphisms
-- Book: F(f)
-- Mathlib: F.map f
example (F : C ⥤ D) {X Y : C} (f : X ⟶ Y) : F.obj X ⟶ F.obj Y := F.map f

-- Functor composition
-- Book: G ∘ F
-- Mathlib: F ⋙ G (diagrammatic order)
example (F : C ⥤ D) {E : Type*} [Category E] (G : D ⥤ E) : C ⥤ E := F ⋙ G

end FunctorExamples

/-! ## Opposite Category Notation

Book: "We denote by C^∨ the category dual to C, i.e., the one obtained from C
by reversing the direction of morphisms."

Mathlib: `Cᵒᵖ` (typed as `C\^op`)
-/

section OppositeExamples

variable {C : Type*} [Category C]

-- Book: C^∨
-- Mathlib: Cᵒᵖ (same type, opposite category structure)

-- Converting objects: X ↦ op X
example (X : C) : Cᵒᵖ := Opposite.op X

-- Converting back: op X ↦ X
example (X : Cᵒᵖ) : C := X.unop

-- Morphisms in opposite category are reversed
-- If f : X ⟶ Y in C, then f.op : op Y ⟶ op X in Cᵒᵖ
example {X Y : C} (f : X ⟶ Y) : Opposite.op Y ⟶ Opposite.op X := f.op

end OppositeExamples

/-! ## Field Convention

Book: "Unless otherwise specified, all fields are assumed to be algebraically closed."

When working over a field k, use `[Field k] [IsAlgClosed k]` for the algebraically
closed assumption. Import from `Mathlib.FieldTheory.IsAlgClosed.Basic`.
-/

end LemmaFeld.TensorCategories.Chapter1
