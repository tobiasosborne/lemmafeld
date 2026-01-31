/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

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

end LemmaFeld.TensorCategories.Chapter1
