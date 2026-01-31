/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Chapter 1, Section 1.6: Projective and Injective Objects

This file establishes the correspondence between Etingof et al. "Tensor Categories"
§1.6 projective/injective objects and mathlib's infrastructure.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.6

## §1.6 Definitions

- **Definition 1.6.5**: Projective and injective objects
- **Definition 1.6.6**: Projective cover
- **Definition 1.6.7**: Injective hull

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Projective object | `Projective P` | Lifting property |
| Injective object | `Injective I` | Extension property |
| Enough projectives | `EnoughProjectives C` | |
| Enough injectives | `EnoughInjectives C` | |
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

/-! ## §1.6 Definition 1.6.5: Projective and Injective Objects

Book: "An object P is *projective* if Hom(P, -) is exact.
An object I is *injective* if Hom(-, I) is exact."

Mathlib:
- `Projective P` means Hom(P, -) preserves epis (lifting property)
- `Injective I` means Hom(-, I) preserves monos (extension property)
-/

section ProjectiveInjective

variable {C : Type*} [Category C]

-- Projective: lifting property
-- For any epi f : X ⟶ Y and g : P ⟶ Y, there exists h : P ⟶ X with f ∘ h = g
example [Projective P] {X Y : C} (f : X ⟶ Y) [Epi f] (g : P ⟶ Y) :
    ∃ h : P ⟶ X, h ≫ f = g :=
  ⟨Projective.factorThru g f, Projective.factorThru_comp g f⟩

-- Injective: extension property
-- For any mono f : X ⟶ Y and g : X ⟶ I, there exists h : Y ⟶ I with h ∘ f = g
example [Injective I] {X Y : C} (f : X ⟶ Y) [Mono f] (g : X ⟶ I) :
    ∃ h : Y ⟶ I, f ≫ h = g :=
  ⟨Injective.factorThru g f, Injective.comp_factorThru g f⟩

end ProjectiveInjective

/-! ## §1.6 Definition 1.6.6 & 1.6.7: Projective Covers and Injective Hulls

Book Definition 1.6.6: "A projective cover of X is a projective object P(X) with
an epimorphism p : P(X) → X such that for any epi from projective, it factors."

Book Definition 1.6.7: "An injective hull of X is an injective object Q(X) with
a monomorphism i : X → Q(X) such that any mono to injective factors."
-/

section CoversHulls

variable {C : Type*} [Category C]

-- Enough projectives means we can find projective covers
example [EnoughProjectives C] (X : C) :
    ∃ (P : C) (_ : Projective P) (f : P ⟶ X), Epi f := by
  let pres := (EnoughProjectives.presentation X).some
  exact ⟨pres.p, pres.projective, pres.f, pres.epi⟩

-- Enough injectives means we can embed into injective objects
example [EnoughInjectives C] (X : C) :
    ∃ (I : C) (_ : Injective I) (f : X ⟶ I), Mono f := by
  let pres := (EnoughInjectives.presentation X).some
  exact ⟨pres.J, pres.injective, pres.f, pres.mono⟩

end CoversHulls

/-! ## Key Properties -/

section Summary

variable {C : Type*} [Category C] [Abelian C]

open scoped ZeroObject

-- Zero object is both projective and injective
example : Projective (0 : C) := inferInstance
example : Injective (0 : C) := inferInstance

end Summary

end LemmaFeld.TensorCategories.Chapter1
