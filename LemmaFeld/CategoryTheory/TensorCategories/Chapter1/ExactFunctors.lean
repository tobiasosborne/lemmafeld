/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Limits.ExactFunctor
import Mathlib.CategoryTheory.Limits.Yoneda
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Chapter 1, Section 1.6: Exact Functors

This file establishes the correspondence between Etingof et al. "Tensor Categories"
§1.6 exact functors and mathlib's infrastructure.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.6

## §1.6 Definitions

- **Definition 1.6.1**: Left and right exact functors
- **Example 1.6.2**: Hom(-, Y) and Hom(X, -) are left exact
- **Exercise 1.6.4**: Left adjoints are right exact, right adjoints are left exact

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Left exact functor | `PreservesFiniteLimits F` | Bundled: `LeftExactFunctor` |
| Right exact functor | `PreservesFiniteColimits F` | Bundled: `RightExactFunctor` |
| Exact functor | Both properties | Bundled: `ExactFunctor` |
| Right adjoint → left exact | `rightAdjoint_preservesLimits` | |
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

/-! ## §1.6 Definition 1.6.1: Left and Right Exact Functors

Mathlib approach:
- `PreservesFiniteLimits F` ≈ left exact (preserves kernels)
- `PreservesFiniteColimits F` ≈ right exact (preserves cokernels)
-/

section ExactFunctors

variable {C : Type*} [Category C] {D : Type*} [Category D]

-- A left exact functor preserves finite limits
example (F : LeftExactFunctor C D) : PreservesFiniteLimits F.obj := inferInstance

-- A right exact functor preserves finite colimits
example (F : RightExactFunctor C D) : PreservesFiniteColimits F.obj := inferInstance

-- An exact functor preserves both
example (F : ExactFunctor C D) : PreservesFiniteLimits F.obj := inferInstance
example (F : ExactFunctor C D) : PreservesFiniteColimits F.obj := inferInstance

-- Constructing bundled functors from properties
example (F : C ⥤ D) [PreservesFiniteLimits F] : LeftExactFunctor C D :=
  LeftExactFunctor.of F

example (F : C ⥤ D) [PreservesFiniteColimits F] : RightExactFunctor C D :=
  RightExactFunctor.of F

example (F : C ⥤ D) [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    ExactFunctor C D :=
  ExactFunctor.of F

end ExactFunctors

/-! ## §1.6 Example 1.6.2: Hom Functors are Left Exact

Book: "The contravariant functor Hom_C(-, Y) and the covariant functor Hom_C(X, -)
from C to the category of abelian groups are left exact."
-/

section HomFunctorsLeftExact

variable {C : Type*} [Category C]

-- Hom(X, -) preserves all limits (left exact)
example [HasLimitsOfSize.{0, 0} C] (X : Cᵒᵖ) : PreservesLimitsOfSize.{0, 0} (coyoneda.obj X) :=
  inferInstance

-- For any shape J, Hom(X, -) preserves J-shaped limits
example (X : Cᵒᵖ) {J : Type*} [Category J] [HasLimitsOfShape J C] :
    PreservesLimitsOfShape J (coyoneda.obj X) :=
  inferInstance

-- Hom(-, Y) also preserves limits
example [HasLimitsOfSize.{0, 0} Cᵒᵖ] (Y : C) : PreservesLimitsOfSize.{0, 0} (yoneda.obj Y) :=
  inferInstance

end HomFunctorsLeftExact

/-! ## §1.6 Exercise 1.6.4: Adjoint Functors and Exactness

Book: "Show that the left adjoint to any functor between abelian categories is
right exact, and the right adjoint is left exact."
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

end LemmaFeld.TensorCategories.Chapter1
