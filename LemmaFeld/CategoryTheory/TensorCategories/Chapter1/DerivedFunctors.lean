/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Abelian.RightDerived
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.CategoryTheory.Preadditive.Injective.Resolution

/-!
# Chapter 1, Section 1.7: Higher Ext Groups and Group Cohomology

This file establishes the correspondence between Etingof et al. "Tensor Categories"
§1.7 and mathlib's derived functor infrastructure.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.7

## §1.7 Summary

The book covers:
- **Projective resolutions**: · · · → P₂ → P₁ → P₀ → M → 0 with Pᵢ projective
- **Ext^n(M, N)**: Defined as cohomology of Hom(P•, N) where P• resolves M
- **Long exact sequence**: For 0 → N₁ → N₂ → N₃ → 0, get connecting morphisms
- **Group cohomology**: H^i(G, A) = Ext^i_G(ℤ, A)
- **Bar resolution**: Explicit resolution of ℤ as G-module
- **Standard complex**: C^i(G, A) = Fun(G^i, A) with explicit differentials

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Projective resolution | `ProjectiveResolution X` | In `Preadditive.Projective.Resolution` |
| Injective resolution | `InjectiveResolution X` | In `Preadditive.Injective.Resolution` |
| Left derived functor | `Functor.leftDerived F n` | Requires `F.Additive` |
| Right derived functor | `Functor.rightDerived F n` | Requires `F.Additive` |
| Ext^n(X, Y) | `Ext R C n` | In `Mathlib.CategoryTheory.Abelian.Ext` |
| Group cohomology | `groupCohomology` | In `RepresentationTheory.Homological.GroupCohomology` |
| H^n(G, A) ≅ Ext^n(k, A) | `groupCohomologyIsoExt` | Key isomorphism |

## Key Insight

Mathlib defines derived functors via:
- `F.leftDerived n` uses projective resolutions (for right exact F)
- `F.rightDerived n` uses injective resolutions (for left exact F)

Ext is defined by left-deriving Hom in the first argument:
`Ext R C n := (linearYoneda R C).obj Y).rightOp.leftDerived n`

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
example (X : C) [EnoughProjectives C] : ProjectiveResolution X :=
  ProjectiveResolution.of X

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
example (X : C) [EnoughInjectives C] : InjectiveResolution X :=
  InjectiveResolution.of X

-- Each term of the resolution is injective
example (X : C) (I : InjectiveResolution X) (n : ℕ) : Injective (I.cocomplex.X n) :=
  I.injective n

-- The inclusion map
example (X : C) (I : InjectiveResolution X) :
    (CochainComplex.single₀ C).obj X ⟶ I.cocomplex :=
  I.ι

end InjectiveResolutions

/-! ## Left Derived Functors

Book: Given a right exact functor F and a projective resolution P• → M → 0,
the left derived functors are L_n F(M) = H_n(F(P•)).

Mathlib: `F.leftDerived n` for an additive functor F (requires `[F.Additive]`).
Note: Right exactness (`PreservesFiniteColimits F`) is used for the 0th derived
functor isomorphism `leftDerivedZeroIsoSelf : F.leftDerived 0 ≅ F`.
-/

section LeftDerived

variable {C : Type*} [Category C] [Abelian C] [EnoughProjectives C]
variable {D : Type*} [Category D] [Abelian D]

-- Left derived functor of F at degree n
-- Note: requires F.Additive (additive functor), not just right exactness
example (F : C ⥤ D) [F.Additive] (n : ℕ) : C ⥤ D :=
  F.leftDerived n

-- L₀F ≅ F for right exact F (derived functor at degree 0 recovers F)
-- This is `Functor.leftDerivedZeroIsoSelf` in mathlib

end LeftDerived

/-! ## Right Derived Functors

Book: Given a left exact functor F and an injective resolution 0 → M → I•,
the right derived functors are R^n F(M) = H^n(F(I•)).

Mathlib: `F.rightDerived n` for an additive functor F (requires `[F.Additive]`).
Note: Left exactness (`PreservesFiniteLimits F`) is used for the 0th derived
functor isomorphism `rightDerivedZeroIsoSelf : F.rightDerived 0 ≅ F`.
-/

section RightDerived

variable {C : Type*} [Category C] [Abelian C] [EnoughInjectives C]
variable {D : Type*} [Category D] [Abelian D]

-- Right derived functor of F at degree n
-- Note: requires F.Additive (additive functor), not just left exactness
example (F : C ⥤ D) [F.Additive] (n : ℕ) : C ⥤ D :=
  F.rightDerived n

-- R⁰F ≅ F for left exact F (derived functor at degree 0 recovers F)
-- This is `Functor.rightDerivedZeroIsoSelf` in mathlib

end RightDerived

/-! ## Ext Groups

Book: "The cohomology Ext^i(M, N) := Ker(d_{i+1})/Im(d_i) where
d_i : Hom(P_{i-1}, N) → Hom(P_i, N) and P• → M is a projective resolution."

Mathlib: `Ext R C n : Cᵒᵖ ⥤ C ⥤ ModuleCat R` defined in
`Mathlib.CategoryTheory.Abelian.Ext`.

The definition is:
  `Ext R C n := (linearYoneda R C).obj Y).rightOp.leftDerived n`

This left-derives the functor Hom(-, Y) in the first (contravariant) argument.

Key results in mathlib:
- `ProjectiveResolution.isoExt`: Ext can be computed using projective resolution
- `isZero_Ext_succ_of_projective`: Ext^{n+1}(P, Y) = 0 for P projective
-/

/-! ## Long Exact Sequence

Book: "If 0 → N₁ → N₂ → N₃ → 0 is a short exact sequence, then there is a
long exact sequence:
  · · · → Ext^i(M, N₁) → Ext^i(M, N₂) → Ext^i(M, N₃) → Ext^{i+1}(M, N₁) → · · ·"

Mathlib: This follows from the general theory of derived functors.
The connecting morphism comes from the snake lemma applied to the
diagram of Hom complexes.
-/

/-! ## Group Cohomology

Book: "The groups Ext^i_G(ℤ, A) in the category of G-modules are called
the cohomology groups of G with coefficients in A, denoted H^i(G, A)."

Mathlib: `groupCohomology` is defined in
`Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic`:
- `groupCohomology n : Rep k G ⥤ ModuleCat k`
- `groupCohomologyIsoExt`: H^n(G, A) ≅ Ext^n(k, A) as G-modules

The bar resolution and standard complex (explicit differential formulas)
are used in the implementation.
-/

/-! ## Summary

The key takeaways for TC 1.7.1 (derived functors setup):

1. **Projective resolutions** exist in any abelian category with enough projectives
   (`EnoughProjectives C` implies `ProjectiveResolution X` exists)

2. **Injective resolutions** exist in any abelian category with enough injectives
   (`EnoughInjectives C` implies `InjectiveResolution X` exists)

3. **Left derived functors** L_n F are defined for right exact functors F
   using projective resolutions

4. **Right derived functors** R^n F are defined for left exact functors F
   using injective resolutions

5. **Ext** is the left derived functor of Hom in the first argument

6. **Group cohomology** H^n(G, A) is a special case of Ext groups
-/

end LemmaFeld.TensorCategories.Chapter1
