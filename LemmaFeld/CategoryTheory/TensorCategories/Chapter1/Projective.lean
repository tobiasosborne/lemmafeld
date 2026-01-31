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
| Projective cover | `ProjectiveCover` | **Gap**: mathlib only has `ProjectivePresentation` |
| Injective hull | `InjectiveHull` | **Gap**: mathlib only has `InjectivePresentation` |
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

/-! ## §1.6 Definition 1.6.6: Projective Cover

Book Definition 1.6.6: "A projective cover of X is a projective object P(X) with
an epimorphism p : P(X) → X such that if g : P → X is an epimorphism from a
projective object P to X, then there exists an epimorphism h : P → P(X) such that ph = g."

**Key difference from mathlib:** Mathlib's `ProjectivePresentation` is just a projective P
with an epi f : P → X. The book's projective cover has a **minimality/universality** property:
any other projective presentation factors through it via an epi.

This is sometimes called an "essential" projective cover.
-/

section ProjectiveCover

variable {C : Type*} [Category C]

/-- A projective cover of X is a projective object P with an epi p : P → X such that
any other projective presentation factors through it via an epi.

Book: Definition 1.6.6

This is stronger than mathlib's `ProjectivePresentation` which only requires
a projective P with an epi to X, without the universality property.
-/
structure ProjectiveCover (X : C) where
  /-- The projective object covering X -/
  P : C
  /-- P is projective -/
  projective : Projective P
  /-- The covering epimorphism -/
  p : P ⟶ X
  /-- p is an epimorphism -/
  epi : Epi p
  /-- Universal property: any epi from projective factors through p via an epi -/
  universalProperty : ∀ (Q : C) [Projective Q] (g : Q ⟶ X) [Epi g],
    ∃ (h : Q ⟶ P), Epi h ∧ h ≫ p = g

/-- A projective cover gives a projective presentation. -/
def ProjectiveCover.toProjectivePresentation {X : C} (cover : ProjectiveCover X) :
    ProjectivePresentation X where
  p := cover.P
  projective := cover.projective
  f := cover.p
  epi := cover.epi

end ProjectiveCover

/-! ## §1.6 Definition 1.6.7: Injective Hull

Book Definition 1.6.7: "An injective hull of X is an injective object Q(X) with
a monomorphism i : X → Q(X) such that if g : X → I is a monomorphism to an
injective object I, then there exists a monomorphism h : Q(X) → I such that hg = i."

This is dual to projective covers.
-/

section InjectiveHull

variable {C : Type*} [Category C]

/-- An injective hull of X is an injective object Q with a mono i : X → Q such that
any other injective presentation factors through it via a mono.

Book: Definition 1.6.7

This is stronger than mathlib's `InjectivePresentation` which only requires
an injective I with a mono from X, without the universality property.
-/
structure InjectiveHull (X : C) where
  /-- The injective object containing X -/
  Q : C
  /-- Q is injective -/
  injective : Injective Q
  /-- The embedding monomorphism -/
  i : X ⟶ Q
  /-- i is a monomorphism -/
  mono : Mono i
  /-- Universal property: any mono to injective factors through i via a mono -/
  universalProperty : ∀ (I : C) [Injective I] (g : X ⟶ I) [Mono g],
    ∃ (h : Q ⟶ I), Mono h ∧ i ≫ h = g

/-- An injective hull gives an injective presentation. -/
def InjectiveHull.toInjectivePresentation {X : C} (hull : InjectiveHull X) :
    InjectivePresentation X where
  J := hull.Q
  injective := hull.injective
  f := hull.i
  mono := hull.mono

end InjectiveHull

/-! ## Mathlib's Projective/Injective Presentations

Mathlib provides `ProjectivePresentation` and `InjectivePresentation` which are
weaker than the book's projective covers and injective hulls. These are sufficient
for constructing resolutions but don't have the minimality property.
-/

section Presentations

variable {C : Type*} [Category C]

-- Enough projectives means we can find projective presentations
example [EnoughProjectives C] (X : C) :
    ∃ (P : C) (_ : Projective P) (f : P ⟶ X), Epi f := by
  let pres := (EnoughProjectives.presentation X).some
  exact ⟨pres.p, pres.projective, pres.f, pres.epi⟩

-- Enough injectives means we can embed into injective objects
example [EnoughInjectives C] (X : C) :
    ∃ (I : C) (_ : Injective I) (f : X ⟶ I), Mono f := by
  let pres := (EnoughInjectives.presentation X).some
  exact ⟨pres.J, pres.injective, pres.f, pres.mono⟩

end Presentations

/-! ## Key Properties -/

section Summary

variable {C : Type*} [Category C] [Abelian C]

open scoped ZeroObject

-- Zero object is both projective and injective
example : Projective (0 : C) := inferInstance
example : Injective (0 : C) := inferInstance

end Summary

end LemmaFeld.TensorCategories.Chapter1
