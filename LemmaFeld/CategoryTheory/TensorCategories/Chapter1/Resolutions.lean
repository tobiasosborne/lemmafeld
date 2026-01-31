/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.CategoryTheory.Abelian.Injective.Resolution

/-!
# Chapter 1, Section 1.7: Projective and Injective Resolutions

This file establishes the correspondence between Etingof et al. "Tensor Categories"
§1.7 resolution theory and mathlib's resolution infrastructure.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.7

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Projective resolution | `ProjectiveResolution X` | In `Preadditive.Projective.Resolution` |
| Injective resolution | `InjectiveResolution X` | In `Preadditive.Injective.Resolution` |

**See also:** DerivedFunctors.lean for left/right derived functors and Ext
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

/-! ## Projective Resolutions

Book: "A projective resolution of M is an exact sequence
  · · · → P₂ → P₁ → P₀ → M → 0
where Pᵢ are projective (e.g., free) R-modules."

Mathlib: `ProjectiveResolution X` is a structure providing:
- `complex : ChainComplex C ℕ` (the complex P•)
- `π : complex ⟶ (ChainComplex.single₀ C).obj X` (augmentation)
- `projective : ∀ n, Projective (complex.X n)` (each term is projective)
- exactness conditions
-/

section ProjectiveResolutions

variable {C : Type*} [Category C] [Abelian C]

-- ProjectiveResolution provides a projective resolution of X
-- `projectiveResolution X` gives an arbitrarily chosen resolution
example (X : C) [EnoughProjectives C] : ProjectiveResolution X :=
  projectiveResolution X

-- Each term of the resolution is projective
example (X : C) (P : ProjectiveResolution X) (n : ℕ) : Projective (P.complex.X n) :=
  P.projective n

-- The augmentation map
example (X : C) (P : ProjectiveResolution X) :
    P.complex ⟶ (ChainComplex.single₀ C).obj X :=
  P.π

end ProjectiveResolutions

/-! ## Injective Resolutions

Dual to projective resolutions:
  0 → X → I₀ → I₁ → I₂ → · · ·
where Iᵢ are injective objects.

Mathlib: `InjectiveResolution X` provides a cochain complex of injectives.
-/

section InjectiveResolutions

variable {C : Type*} [Category C] [Abelian C]

-- InjectiveResolution provides an injective resolution of X
-- `injectiveResolution X` gives an arbitrarily chosen resolution
example (X : C) [EnoughInjectives C] : InjectiveResolution X :=
  injectiveResolution X

-- Each term of the resolution is injective
example (X : C) (I : InjectiveResolution X) (n : ℕ) : Injective (I.cocomplex.X n) :=
  I.injective n

-- The inclusion map
example (X : C) (I : InjectiveResolution X) :
    (CochainComplex.single₀ C).obj X ⟶ I.cocomplex :=
  I.ι

end InjectiveResolutions

/-! ## Summary

| Book | Mathlib | Notes |
|------|---------|-------|
| Projective resolution P• → M → 0 | `ProjectiveResolution X` | Chain complex of projectives |
| Injective resolution 0 → X → I• | `InjectiveResolution X` | Cochain complex of injectives |
| Enough projectives | `EnoughProjectives C` | Existence via `.of` |
| Enough injectives | `EnoughInjectives C` | Existence via `.of` |
-/

end LemmaFeld.TensorCategories.Chapter1
