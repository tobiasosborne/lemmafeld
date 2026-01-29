/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Injective.Basic

/-!
# Chapter 1, Section 1.6: Projective and Injective Objects

This file establishes the correspondence between Etingof et al. "Tensor Categories"
§1.6 and mathlib's projective/injective infrastructure.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.6

## §1.6 Summary

The book defines:
- **Definition 1.6.1**: Left and right exact functors
- **Example 1.6.2**: Hom(-, Y) and Hom(X, -) are left exact
- **Example 1.6.3**: M ⊗_A - is right exact
- **Exercise 1.6.4**: Left adjoints are right exact, right adjoints are left exact
- **Definition 1.6.5**: Projective and injective objects
- **Definition 1.6.6**: Projective cover
- **Definition 1.6.7**: Injective hull

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Left exact functor | `PreservesFiniteLimits F` | Bundled: `LeftExactFunctor` |
| Right exact functor | `PreservesFiniteColimits F` | Bundled: `RightExactFunctor` |
| Exact functor | Both properties | Bundled: `ExactFunctor` |
| Hom(X, -) left exact | `PreservesLimits (coyoneda.obj X)` | Yoneda file |
| Hom(-, Y) left exact | `PreservesLimits (yoneda.obj Y)` | Contravariant |
| Right adjoint → left exact | `rightAdjoint_preservesLimits` | Adjunction.Limits |
| Projective object | `Projective P` | In `Mathlib.CategoryTheory.Projective` |
| Injective object | `Injective I` | In `Mathlib.CategoryTheory.Injective.Basic` |
| Enough projectives | `EnoughProjectives C` | Category has enough projectives |
| Enough injectives | `EnoughInjectives C` | Category has enough injectives |
| Projective cover | `ProjectiveCover.down` | Via `EnoughProjectives` |
| Injective hull | `Injective.factorThru` | Via `EnoughInjectives` |

## Equivalence of Definitions

For abelian categories, there is an equivalence between:
1. Functor preserves finite limits (mathlib's `PreservesFiniteLimits`)
2. Functor preserves kernels
3. Functor takes short exact sequences 0 → X → Y → Z → 0 to 0 → F(X) → F(Y) → F(Z) exact

This is captured in `Functor.exact_tfae` in `Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`.

-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

/-! ## §1.6 Definition 1.6.1: Left and Right Exact Functors

Book: "An additive functor F : C → D is called *left exact* if for any short exact
sequence 0 → X → Y → Z → 0 in C the sequence 0 → F(X) → F(Y) → F(Z) is exact in D.
A functor is *right exact* if F(X) → F(Y) → F(Z) → 0 is exact.
A functor is *exact* if it is both left and right exact."

Mathlib approach:
- `PreservesFiniteLimits F` ≈ left exact (preserves kernels)
- `PreservesFiniteColimits F` ≈ right exact (preserves cokernels)

The bundled types `LeftExactFunctor`, `RightExactFunctor`, `ExactFunctor` provide
functors with these properties as objects of a category.
-/

section ExactFunctors

variable {C : Type*} [Category C] {D : Type*} [Category D]

-- Mathlib's left exact functor type (bundled)
-- `C ⥤ₗ D` is notation for `LeftExactFunctor C D`
-- Definition: functors F : C ⥤ D with `PreservesFiniteLimits F`

-- A left exact functor preserves finite limits
example (F : LeftExactFunctor C D) : PreservesFiniteLimits F.obj := inferInstance

-- A right exact functor preserves finite colimits
example (F : RightExactFunctor C D) : PreservesFiniteColimits F.obj := inferInstance

-- An exact functor preserves both
example (F : ExactFunctor C D) : PreservesFiniteLimits F.obj := inferInstance
example (F : ExactFunctor C D) : PreservesFiniteColimits F.obj := inferInstance

-- Constructing a left exact functor from properties
example (F : C ⥤ D) [PreservesFiniteLimits F] : LeftExactFunctor C D :=
  LeftExactFunctor.of F

-- Constructing a right exact functor from properties
example (F : C ⥤ D) [PreservesFiniteColimits F] : RightExactFunctor C D :=
  RightExactFunctor.of F

-- Constructing an exact functor from properties
example (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    ExactFunctor C D :=
  ExactFunctor.of F

end ExactFunctors

/-! ## §1.6 Example 1.6.2: Hom Functors are Left Exact

Book: "Let X, Y be objects in an abelian category C. The contravariant functor
Hom_C(-, Y) and the covariant functor Hom_C(X, -) from C to the category of
abelian groups are left exact."

Mathlib: `coyoneda.obj X` is Hom(X, -) and `yoneda.obj Y` is Hom(-, Y)^op.
Both preserve limits, which means they are left exact.
-/

section HomFunctorsLeftExact

variable {C : Type*} [Category C]

-- The covariant Hom functor Hom(X, -) preserves all limits
-- This means it is left exact
example [HasLimitsOfSize.{0, 0} C] (X : Cᵒᵖ) : PreservesLimitsOfSize.{0, 0} (coyoneda.obj X) :=
  inferInstance

-- For any shape J, Hom(X, -) preserves J-shaped limits
example (X : Cᵒᵖ) {J : Type*} [Category J] [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J (coyoneda.obj X) :=
  inferInstance

-- The contravariant Hom functor Hom(-, Y) also preserves limits
-- (as a functor C^op → Type, it turns colimits in C to limits)
example [HasLimitsOfSize.{0, 0} Cᵒᵖ] (Y : C) : PreservesLimitsOfSize.{0, 0} (yoneda.obj Y) :=
  inferInstance

end HomFunctorsLeftExact

/-! ## §1.6 Exercise 1.6.4: Adjoint Functors and Exactness

Book: "Show that the left adjoint to any functor between abelian categories is
right exact, and the right adjoint is left exact."

Mathlib: `Adjunction.rightAdjoint_preservesLimits` shows right adjoints preserve limits.
Dually, left adjoints preserve colimits (`Adjunction.leftAdjoint_preservesColimits`).
-/

section AdjointExactness

variable {C : Type*} [Category C] {D : Type*} [Category D]

-- Right adjoints preserve limits (hence are left exact)
example (F : C ⥤ D) (G : D ⥤ C) (h : F ⊣ G) [HasLimits D] : PreservesLimits G :=
  h.rightAdjoint_preservesLimits

-- Left adjoints preserve colimits (hence are right exact)
example (F : C ⥤ D) (G : D ⥤ C) (h : F ⊣ G) [HasColimits C] : PreservesColimits F :=
  h.leftAdjoint_preservesColimits

end AdjointExactness

/-! ## §1.6 Definition 1.6.5: Projective and Injective Objects

Book: "An object P in an abelian category C is called *projective* if the functor
Hom_C(P, -) is exact. An object I in C is called *injective* if the functor
Hom_C(-, I) is exact."

Mathlib:
- `Projective P` means Hom(P, -) preserves epis (lifting property)
- `Injective I` means Hom(-, I) preserves monos (extension property)
-/

section ProjectiveInjective

variable {C : Type*} [Category C]

-- Projective object: has the lifting property
-- For any epi f : X ⟶ Y and any g : P ⟶ Y, there exists h : P ⟶ X with f ∘ h = g
example [Projective P] {X Y : C} (f : X ⟶ Y) [Epi f] (g : P ⟶ Y) :
    ∃ h : P ⟶ X, h ≫ f = g :=
  ⟨Projective.factorThru g f, Projective.factorThru_comp g f⟩

-- Injective object: has the extension property
-- For any mono f : X ⟶ Y and any g : X ⟶ I, there exists h : Y ⟶ I with h ∘ f = g
example [Injective I] {X Y : C} (f : X ⟶ Y) [Mono f] (g : X ⟶ I) :
    ∃ h : Y ⟶ I, f ≫ h = g :=
  ⟨Injective.factorThru g f, Injective.comp_factorThru g f⟩

end ProjectiveInjective

/-! ## §1.6 Definition 1.6.6 & 1.6.7: Projective Covers and Injective Hulls

Book Definition 1.6.6: "A projective cover of X is a projective object P(X) together
with an epimorphism p : P(X) → X such that for any epi g : P → X from projective P,
there exists an epi h : P → P(X) with p ∘ h = g."

Book Definition 1.6.7: "An injective hull of X is an injective object Q(X) together
with a monomorphism i : X → Q(X) such that for any mono g : X → Q to an injective Q,
there exists a mono h : Q(X) → Q with h ∘ i = g."

Mathlib models these through `EnoughProjectives` and `EnoughInjectives`:
- `EnoughProjectives C` provides a projective covering for any object
- `EnoughInjectives C` provides an injective embedding for any object
-/

section CoversHulls

variable {C : Type*} [Category C]

-- Enough projectives means we can find projective covers
-- ProjectivePresentation X has: p (projective object), f : p ⟶ X (epi)
example [EnoughProjectives C] (X : C) :
    ∃ (P : C) (_ : Projective P) (f : P ⟶ X), Epi f := by
  let pres := (EnoughProjectives.presentation X).some
  exact ⟨pres.p, pres.projective, pres.f, pres.epi⟩

-- Enough injectives means we can embed into injective objects
-- InjectivePresentation X has: J (injective object), f : X ⟶ J (mono)
example [EnoughInjectives C] (X : C) :
    ∃ (I : C) (_ : Injective I) (f : X ⟶ I), Mono f := by
  let pres := (EnoughInjectives.presentation X).some
  exact ⟨pres.J, pres.injective, pres.f, pres.mono⟩

end CoversHulls

/-! ## Key Properties

Summary of important relationships:
-/

section Summary

variable {C : Type*} [Category C] [Abelian C]

open scoped ZeroObject

-- Zero object is both projective and injective
-- Note: (0 : C) notation requires `open scoped ZeroObject`
example : Projective (0 : C) := inferInstance
example : Injective (0 : C) := inferInstance

-- Simple objects can be characterized by their projective covers
-- (In a finite abelian category, simples have simple projective covers)

end Summary

end LemmaFeld.TensorCategories.Chapter1
