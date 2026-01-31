/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# Chapter 1, Section 1.2: k-Linear Categories and Functors

This file covers k-linear categories and additive/linear functors from
Etingof et al. "Tensor Categories" §1.2.

See also `Additive.lean` for additive category axioms (A1)-(A3).

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.2
-/

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

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
