/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Products.Basic

/-!
# Chapter 1, Section 1.2: Direct Sum Bifunctor

This file establishes the direct sum bifunctor ⊕ : C × C → C for additive categories,
corresponding to Etingof et al. §1.2.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.2

## §1.2 Direct Sum as Bifunctor

Book: "The object Y is unique up to a unique isomorphism, is denoted by X₁ ⊕ X₂,
and is called the direct sum of X₁ and X₂. Thus, every additive category is
equipped with a bifunctor ⊕ : C × C → C."

## Mathlib Implementation

Mathlib provides biproducts via `CategoryTheory.Limits.Shapes.BinaryBiproducts`:
- Object: `X ⊞ Y` (the biproduct, which equals direct sum in additive categories)
- Morphism map: `biprod.map f g : W ⊞ X ⟶ Y ⊞ Z` for `f : W ⟶ Y`, `g : X ⟶ Z`

This file constructs the explicit bifunctor `DirectSum.functor : C × C ⥤ C`.

-/

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

/-! ## Direct Sum Bifunctor Construction

We construct the bifunctor `⊕ : C × C → C` using mathlib's biproduct infrastructure.
-/

namespace DirectSum

variable (C : Type*) [Category C] [Preadditive C] [HasBinaryBiproducts C]

/-- The direct sum bifunctor ⊕ : C × C → C.

This is the bifunctor from Definition 1.2.1 (A3) of Etingof et al.
On objects: `(X, Y) ↦ X ⊞ Y`
On morphisms: `(f, g) ↦ biprod.map f g`
-/
noncomputable def functor : C × C ⥤ C where
  obj := fun ⟨X, Y⟩ => X ⊞ Y
  map := fun ⟨f, g⟩ => biprod.map f g
  map_id := fun ⟨X, Y⟩ => by ext <;> simp
  map_comp := fun ⟨f₁, g₁⟩ ⟨f₂, g₂⟩ => by ext <;> simp

-- Functoriality is automatic from the definition

end DirectSum

/-! ## Structural Morphisms

The biproduct `X ⊞ Y` comes with canonical projections and injections
satisfying the axioms from Definition 1.2.1 (A3).
-/

section StructuralMorphisms

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

/-! ### Projections/Injections and Axiom (A3)

Book notation → Mathlib: p₁ = `biprod.fst`, p₂ = `biprod.snd`, i₁ = `biprod.inl`, i₂ = `biprod.inr`
-/

-- p₁i₁ = id_X
example (X Y : C) : (biprod.inl : X ⟶ X ⊞ Y) ≫ biprod.fst = 𝟙 X := biprod.inl_fst

-- p₂i₂ = id_Y
example (X Y : C) : (biprod.inr : Y ⟶ X ⊞ Y) ≫ biprod.snd = 𝟙 Y := biprod.inr_snd

-- i₁p₁ + i₂p₂ = id_{X⊕Y}  (the "total" identity)
example (X Y : C) :
    (biprod.fst : X ⊞ Y ⟶ X) ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y) :=
  biprod.total

-- Cross terms are zero:
example (X Y : C) : (biprod.inl : X ⟶ X ⊞ Y) ≫ biprod.snd = 0 := biprod.inl_snd
example (X Y : C) : (biprod.inr : Y ⟶ X ⊞ Y) ≫ biprod.fst = 0 := biprod.inr_fst

end StructuralMorphisms

/-! ## Universal Properties

The biproduct is both a product and a coproduct.
-/

section UniversalProperties

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

-- Product: `biprod.lift f g` with `lift_fst`, `lift_snd`
example {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift f g ≫ biprod.fst = f := biprod.lift_fst f g
example {W X Y : C} (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift f g ≫ biprod.snd = g := biprod.lift_snd f g

-- Coproduct: `biprod.desc f g` with `inl_desc`, `inr_desc`
example {X Y W : C} (f : X ⟶ W) (g : Y ⟶ W) :
    biprod.inl ≫ biprod.desc f g = f := biprod.inl_desc f g
example {X Y W : C} (f : X ⟶ W) (g : Y ⟶ W) :
    biprod.inr ≫ biprod.desc f g = g := biprod.inr_desc f g

end UniversalProperties

/-! ## Symmetry

The direct sum is symmetric: X ⊕ Y ≅ Y ⊕ X.
-/

section Symmetry

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

/-- The symmetry isomorphism X ⊞ Y ≅ Y ⊞ X.

Book: Direct sum is commutative up to canonical isomorphism.
Mathlib: `biprod.braiding` provides this isomorphism.
-/
noncomputable def biprodSymm (X Y : C) : X ⊞ Y ≅ Y ⊞ X := biprod.braiding X Y

-- The symmetry satisfies σ ∘ σ = id
example (X Y : C) : (biprodSymm X Y).hom ≫ (biprodSymm Y X).hom = 𝟙 (X ⊞ Y) := by
  simp [biprodSymm, biprod.braiding]

end Symmetry

/-! ## Associativity

The direct sum is associative: (X ⊕ Y) ⊕ Z ≅ X ⊕ (Y ⊕ Z).
-/

section Associativity

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

/-- The associativity isomorphism (X ⊞ Y) ⊞ Z ≅ X ⊞ (Y ⊞ Z).

Book: Direct sum is associative up to canonical isomorphism.
Mathlib: `biprod.associator` provides this isomorphism.
-/
noncomputable def biprodAssoc (X Y Z : C) : (X ⊞ Y) ⊞ Z ≅ X ⊞ (Y ⊞ Z) :=
  biprod.associator X Y Z

end Associativity

/-! ## Zero Object as Unit

Book: 0 ⊕ X ≅ X ≅ X ⊕ 0. Mathlib: Use `IsZero` and biproduct properties.
-/

section ZeroUnit

open scoped ZeroObject

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C] [HasZeroObject C]

-- When one summand is zero, the biproduct is isomorphic to the other summand.
-- This follows from the universal property and `IsZero` characterizations.

-- The zero object satisfies IsZero
-- Notation: `(0 : C)` is the zero object when `HasZeroObject C` and `ZeroObject` scope is open
example : IsZero (0 : C) := isZero_zero C

-- If X is zero, then X ⊞ Y ≅ Y (via biprod.snd being an iso)
-- If Y is zero, then X ⊞ Y ≅ X (via biprod.fst being an iso)

end ZeroUnit

end LemmaFeld.TensorCategories.Chapter1
