/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Abelian.LeftDerived
import Mathlib.CategoryTheory.Abelian.RightDerived

import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.Resolutions

/-!
# Chapter 1, Section 1.7: Derived Functors, Ext, and Group Cohomology

This file covers derived functors, Ext groups, and group cohomology from §1.7.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.7

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Left derived functor | `Functor.leftDerived F n` | Requires `F.Additive` |
| Right derived functor | `Functor.rightDerived F n` | Requires `F.Additive` |
| Ext^n(X, Y) | `Ext R C n` | In `Mathlib.CategoryTheory.Abelian.Ext` |
| Group cohomology | `groupCohomology` | In `RepresentationTheory.Homological.GroupCohomology` |

**See also:** Resolutions.lean for projective/injective resolutions

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
