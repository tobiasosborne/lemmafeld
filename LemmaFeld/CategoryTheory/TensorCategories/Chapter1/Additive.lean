/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Chapter 1, Section 1.2: Additive and k-Linear Categories

This file establishes the correspondence between Etingof et al. "Tensor Categories"
§1.2 and mathlib's preadditive/linear category infrastructure.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.2

## §1.2 Summary

The book defines:
- **Definition 1.2.1**: Additive categories via axioms (A1), (A2), (A3)
- **Definition 1.2.2**: k-linear categories
- **Definition 1.2.3**: Additive and k-linear functors
- **Proposition 1.2.4**: Additive functors preserve direct sums

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| (A1) Hom groups + biadditive | `Preadditive C` | Core structure |
| (A2) Zero object | `HasZeroObject C` | Limits structure |
| (A3) Direct sums | `HasBinaryBiproducts C` | Limits structure |
| Additive category (full) | All three above | No single class |
| k-linear category | `Linear R C` | Requires `Preadditive` |
| Additive functor | `Functor.Additive F` | `map_add` condition |
| k-linear functor | `Functor.Linear R F` | `map_smul` condition |
| Prop 1.2.4 | `PreservesBinaryBiproducts` | Auto for additive |

-/

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

/-! ## §1.2 Definition 1.2.1: Additive Category

Book: "An additive category is a category C satisfying the following axioms:
- (A1) Every set Hom_C(X,Y) is equipped with a structure of an abelian group
  such that composition of morphisms is biadditive.
- (A2) There exists a zero object 0 ∈ C such that Hom_C(0,0) = 0.
- (A3) For any objects X₁, X₂ there exists an object Y and morphisms
  p₁ : Y → X₁, p₂ : Y → X₂, i₁ : X₁ → Y, i₂ : X₂ → Y such that
  p₁i₁ = id_{X₁}, p₂i₂ = id_{X₂}, and i₁p₁ + i₂p₂ = id_Y."

**Key insight:** Mathlib does not have a single `Additive` class. Instead, an
"additive category" in the book's sense requires three typeclasses:
```
variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
```
-/

section AdditiveCategoryAxioms

variable {C : Type*} [Category C]

/-! ### Axiom (A1): Preadditive Structure

Mathlib: `CategoryTheory.Preadditive` in `Mathlib.CategoryTheory.Preadditive.Basic`

Provides:
- `homGroup : ∀ P Q : C, AddCommGroup (P ⟶ Q)` — Hom sets are abelian groups
- `add_comp` — left distributivity: `(f + f') ≫ g = f ≫ g + f' ≫ g`
- `comp_add` — right distributivity: `f ≫ (g + g') = f ≫ g + f ≫ g'`
-/

-- Axiom (A1) is captured by the `Preadditive` class
-- Example usage:
example [Preadditive C] {X Y Z : C} (f f' : X ⟶ Y) (g : Y ⟶ Z) :
    (f + f') ≫ g = f ≫ g + f' ≫ g := Preadditive.add_comp X Y Z f f' g

/-! ### Axiom (A2): Zero Object

Mathlib: `CategoryTheory.Limits.HasZeroObject` in
`Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects`

A zero object is both initial and terminal. In a preadditive category,
`Hom(0, 0) = 0` follows automatically.
-/

-- Axiom (A2) is captured by the `HasZeroObject` class
-- The zero object is accessed via `0` or `(0 : C)` with notation from `Limits`

/-! ### Axiom (A3): Binary Biproducts (Direct Sums)

Mathlib: `CategoryTheory.Limits.HasBinaryBiproducts` in
`Mathlib.CategoryTheory.Limits.Shapes.Biproducts`

For objects X, Y, the biproduct `X ⊞ Y` comes with:
- `biprod.fst : X ⊞ Y ⟶ X` (projection p₁)
- `biprod.snd : X ⊞ Y ⟶ Y` (projection p₂)
- `biprod.inl : X ⟶ X ⊞ Y` (injection i₁)
- `biprod.inr : Y ⟶ X ⊞ Y` (injection i₂)

Satisfying the book's conditions.
-/

-- Axiom (A3) is captured by the `HasBinaryBiproducts` class
-- The biproduct conditions are:
example [Preadditive C] [HasBinaryBiproducts C] (X Y : C) :
    (biprod.inl : X ⟶ X ⊞ Y) ≫ biprod.fst = 𝟙 X := biprod.inl_fst
example [Preadditive C] [HasBinaryBiproducts C] (X Y : C) :
    (biprod.inr : Y ⟶ X ⊞ Y) ≫ biprod.snd = 𝟙 Y := biprod.inr_snd
example [Preadditive C] [HasBinaryBiproducts C] (X Y : C) :
    (biprod.fst : X ⊞ Y ⟶ X) ≫ biprod.inl + biprod.snd ≫ biprod.inr = 𝟙 (X ⊞ Y) :=
  biprod.total

end AdditiveCategoryAxioms

/-! ## §1.2 Definition 1.2.2: k-Linear Category

Book: "An additive category C is said to be k-linear if for any objects X, Y,
Hom_C(X,Y) is equipped with a structure of a vector space over k, such that
composition of morphisms is k-linear."

Mathlib: `CategoryTheory.Linear R C` in `Mathlib.CategoryTheory.Linear.Basic`

Provides:
- `homModule : ∀ X Y : C, Module R (X ⟶ Y)` — Hom sets are R-modules
- `smul_comp : (r • f) ≫ g = r • (f ≫ g)` — left linearity
- `comp_smul : f ≫ (r • g) = r • (f ≫ g)` — right linearity
-/

section LinearCategory

variable {R : Type*} [CommSemiring R] {C : Type*} [Category C] [Preadditive C]

-- k-linear category = `Linear R C` (or `Linear k C` for a field k)
example [Linear R C] {X Y Z : C} (r : R) (f : X ⟶ Y) (g : Y ⟶ Z) :
    (r • f) ≫ g = r • (f ≫ g) := Linear.smul_comp X Y Z r f g

end LinearCategory

/-! ## §1.2 Definition 1.2.3: Additive and k-Linear Functors

Book: "A functor F : C → D between additive categories is called additive if
the associated maps Hom_C(X,Y) → Hom_D(F(X), F(Y)) are homomorphisms of abelian
groups. If C and D are k-linear categories then F is called k-linear if these
homomorphisms are k-linear."

Mathlib:
- Additive functor: `Functor.Additive F` in `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor`
- k-linear functor: `Functor.Linear R F` in `Mathlib.CategoryTheory.Linear.LinearFunctor`
-/

section AdditiveFunctor

variable {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]

-- Additive functor: preserves addition of morphisms
example (F : C ⥤ D) [F.Additive] {X Y : C} (f g : X ⟶ Y) :
    F.map (f + g) = F.map f + F.map g := F.map_add

-- k-linear functor: preserves scalar multiplication
variable {R : Type*} [CommSemiring R] [Linear R C] [Linear R D]

example (F : C ⥤ D) [F.Additive] [F.Linear R] {X Y : C} (r : R) (f : X ⟶ Y) :
    F.map (r • f) = r • F.map f := F.map_smul r f

end AdditiveFunctor

/-! ## §1.2 Proposition 1.2.4: Additive Functors Preserve Direct Sums

Book: "For any additive functor F : C → D there exists a natural isomorphism
F(X) ⊕ F(Y) ≅ F(X ⊕ Y)."

Mathlib: An additive functor automatically preserves biproducts. This is captured
by `PreservesBinaryBiproducts F` which holds for any additive functor between
categories with binary biproducts.

Key lemma: `Functor.biprodComparison_eq_biprodIso` shows the comparison morphism
is an isomorphism.
-/

section PreservesDirectSums

variable {C D : Type*} [Category C] [Category D]
variable [Preadditive C] [Preadditive D]
variable [HasBinaryBiproducts C] [HasBinaryBiproducts D]

-- For additive functors F between categories with binary biproducts,
-- the comparison morphism `F(X) ⊞ F(Y) ⟶ F(X ⊞ Y)` is an isomorphism.
-- This requires `PreservesBinaryBiproduct X Y F` which follows from additivity.

-- The comparison morphism is given by:
-- `biprod.lift (F.map biprod.fst) (F.map biprod.snd) : F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y)`

-- When F is additive and preserves biproducts:
noncomputable example (F : C ⥤ D) [F.Additive] [∀ X Y, PreservesBinaryBiproduct X Y F]
    (X Y : C) : F.obj X ⊞ F.obj Y ≅ F.obj (X ⊞ Y) :=
  (F.mapBiprod X Y).symm

end PreservesDirectSums

/-! ## §1.2 Bifunctor Structure of Direct Sum

Book: "The object Y is unique up to a unique isomorphism, is denoted by X₁ ⊕ X₂,
and is called the direct sum of X₁ and X₂. Thus, every additive category is
equipped with a bifunctor ⊕ : C × C → C."

Mathlib: The bifunctor structure is given by `biprod.map`:
```
biprod.map : (W ⟶ Y) → (X ⟶ Z) → (W ⊞ X ⟶ Y ⊞ Z)
```
with functoriality laws `biprod.map_id` and `biprod.map_comp`.
-/

section BifunctorStructure

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

-- Functoriality: biprod.map preserves identity
example (X Y : C) : biprod.map (𝟙 X) (𝟙 Y) = 𝟙 (X ⊞ Y) := by ext <;> simp

-- Functoriality: biprod.map preserves composition
example {W X Y Z A B : C} (f : W ⟶ Y) (g : X ⟶ Z) (h : Y ⟶ A) (k : Z ⟶ B) :
    biprod.map (f ≫ h) (g ≫ k) = biprod.map f g ≫ biprod.map h k := by ext <;> simp

end BifunctorStructure

end LemmaFeld.TensorCategories.Chapter1
