/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Chapter 1, Section 1.7.2: Ext^n(X, Y) Definition

This file formalizes Ext^n(X, Y) from Etingof et al. "Tensor Categories" §1.7.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.7

## §1.7.2 Summary

The book defines:
> "The cohomology Ext^i(M, N) := Ker(d_{i+1})/Im(d_i) where
> d_i : Hom(P_{i-1}, N) → Hom(P_i, N) and P• → M is a projective resolution."

Key properties:
- Ext^0(M, N) = Hom(M, N)
- Long exact sequence from 0 → N₁ → N₂ → N₃ → 0:
  ⋯ → Ext^i(M, N₁) → Ext^i(M, N₂) → Ext^i(M, N₃) → Ext^{i+1}(M, N₁) → ⋯
- Ext^{n+1}(P, Y) = 0 for P projective

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Ext^n(X, Y) (functor) | `Ext R C n` | Functor Cᵒᵖ ⥤ C ⥤ ModuleCat R |
| Ext^n(X, Y) (element) | `Abelian.Ext X Y n` | Via derived category |
| Ext^0 ≅ Hom | `Ext.homEquiv₀` | Equivalence |
| Long exact (covariant) | `covariantSequence_exact` | In second variable |
| Long exact (contravariant) | `contravariantSequence_exact` | In first variable |
| Ext^{n+1}(P, Y) = 0 | `isZero_Ext_succ_of_projective` | For projective P |

## Two Ext APIs in Mathlib

Mathlib provides two different Ext constructions:

1. **Functor-based** (`Mathlib.CategoryTheory.Abelian.Ext`):
   `Ext R C n : Cᵒᵖ ⥤ C ⥤ ModuleCat R`
   Defined by left-deriving the linear Yoneda functor.

2. **Element-based** (`Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`):
   `Abelian.Ext X Y n : Type`
   Defined via the derived category as `Dˢᵇ(C)((ι.obj X)⟦n⟧, ι.obj Y)`.

Both are equivalent; the element-based API is often more convenient for explicit computations.
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

/-! ## Functor-Based Ext

Book: "The cohomology Ext^i(M, N) := Ker(d_{i+1})/Im(d_i)"

Mathlib: `Ext R C n : Cᵒᵖ ⥤ C ⥤ ModuleCat R` is defined by left-deriving
the linear Yoneda functor `(linearYoneda R C).obj Y` in the contravariant argument.

This gives a bifunctor: contravariant in the first argument, covariant in the second.
-/

section FunctorExt

variable {R : Type*} [Ring R]
variable {C : Type*} [Category C] [Abelian C] [Linear R C] [EnoughProjectives C]

-- The Ext functor: Cᵒᵖ × C → ModuleCat R
example (n : ℕ) : Cᵒᵖ ⥤ C ⥤ ModuleCat R := Ext R C n

-- Apply Ext to specific objects
example (X Y : C) (n : ℕ) : ModuleCat R := ((Ext R C n).obj (Opposite.op X)).obj Y

-- Ext^{n+1}(P, Y) = 0 for P projective
-- Book: "It is easy to see that Ext^i(P, N) = 0 for i > 0 if P is projective"
example (P Y : C) [Projective P] (n : ℕ) :
    IsZero (((Ext R C (n + 1)).obj (Opposite.op P)).obj Y) :=
  isZero_Ext_succ_of_projective P Y n

-- Ext can be computed using any projective resolution
-- This is the computational definition from the book
example {X : C} (P : ProjectiveResolution X) (n : ℕ) (Y : C) :
    ((Ext R C n).obj (Opposite.op X)).obj Y ≅
      HomologicalComplex.homology (P.complex.linearYonedaObj R Y) n :=
  P.isoExt n Y

end FunctorExt

/-! ## Element-Based Ext (Derived Category)

Mathlib also provides an element-based definition via the derived category:
`Abelian.Ext X Y n` defined in `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`.

This is often more convenient for explicit calculations and provides:
- `Ext.homEquiv₀ : Ext X Y 0 ≃ (X ⟶ Y)` — the key isomorphism
- `Ext.mk₀ : (X ⟶ Y) → Ext X Y 0` — construct Ext^0 element from morphism
- Pre/post composition operations for functoriality
-/

section ElementExt

variable {C : Type*} [Category C] [Abelian C] [HasExt C]

-- The Ext type between objects
-- Note: `Abelian.Ext X Y n` is the type of Ext^n(X, Y)
example (X Y : C) (n : ℕ) : Type := Abelian.Ext X Y n

-- Ext^0(X, Y) ≅ Hom(X, Y)
-- Book: "it is easy to see that Ext^0(M, N) = Hom_R(M, N)"
example (X Y : C) : Abelian.Ext X Y 0 ≃ (X ⟶ Y) := Ext.homEquiv₀

-- As an additive equivalence
example (X Y : C) : Abelian.Ext X Y 0 ≃+ (X ⟶ Y) := Ext.addEquiv₀

-- Construct Ext^0 element from a morphism
example (X Y : C) (f : X ⟶ Y) : Abelian.Ext X Y 0 := Ext.mk₀ f

end ElementExt

/-! ## Long Exact Sequences

Book: "If 0 → N₁ → N₂ → N₃ → 0 is a short exact sequence, then there is a
long exact sequence:
  ⋯ → Ext^i(M, N₁) → Ext^i(M, N₂) → Ext^i(M, N₃) → Ext^{i+1}(M, N₁) → ⋯"

Mathlib provides this in both variables:
- Covariant (second variable): `Ext.covariantSequence_exact`
- Contravariant (first variable): `Ext.contravariantSequence_exact`
-/

section LongExact

variable {C : Type*} [Category C] [Abelian C] [HasExt C]

-- Covariant long exact sequence (in second variable)
-- For short exact S : X₁ → X₂ → X₃ and any M,
-- we get exactness of Ext(M, X₂) → Ext(M, X₁) → Ext(M, X₃)[+1]
example (X : C) {S : ShortComplex C} (hS : S.ShortExact) (n₀ n₁ : ℕ) (h : n₀ + 1 = n₁) :
    (Ext.covariantSequence X hS n₀ n₁ h).Exact :=
  Ext.covariantSequence_exact X hS n₀ n₁ h

-- Contravariant long exact sequence (in first variable)
-- For short exact S : X₁ → X₂ → X₃ and any Y,
-- we get exactness of Ext(X₂, Y) → Ext(X₁, Y) → Ext(X₃, Y)[+1]
example {S : ShortComplex C} (hS : S.ShortExact) (Y : C) (n₀ n₁ : ℕ) (h : 1 + n₀ = n₁) :
    (Ext.contravariantSequence hS Y n₀ n₁ h).Exact :=
  Ext.contravariantSequence_exact hS Y n₀ n₁ h

end LongExact

/-! ## Computing Ext with Projective Resolutions

Book: "Given such a resolution [P• → M → 0], we can define the sequence
  0 → Hom(P₀, N) → Hom(P₁, N) → Hom(P₂, N) → ⋯
which is a complex. [...] The cohomology of this complex [...] is denoted Ext^i(M, N)."

Mathlib: `ProjectiveResolution.isoExt` shows that Ext can be computed as the
homology of the complex `P.complex.linearYonedaObj R Y`.
-/

section Computation

variable {R : Type*} [Ring R]
variable {C : Type*} [Category C] [Abelian C] [Linear R C] [EnoughProjectives C]

-- Apply Hom(-, Y) to a projective resolution
-- This gives a cochain complex whose homology is Ext^n(X, Y)
example {X : C} (P : ProjectiveResolution X) (Y : C) :
    CochainComplex (ModuleCat R) ℕ :=
  P.complex.linearYonedaObj R Y

-- The isomorphism: Ext^n(X, Y) ≅ H^n(Hom(P•, Y))
-- This is the book's definition made precise
example {X : C} (P : ProjectiveResolution X) (n : ℕ) (Y : C) :
    ((Ext R C n).obj (Opposite.op X)).obj Y ≅
      HomologicalComplex.homology (P.complex.linearYonedaObj R Y) n :=
  P.isoExt n Y

end Computation

/-! ## Summary

The key correspondences for §1.7.2 Ext^n(X, Y):

1. **Definition**: Ext^n is the n-th left derived functor of Hom in the first argument.
   Mathlib: `Ext R C n : Cᵒᵖ ⥤ C ⥤ ModuleCat R`

2. **Ext^0 ≅ Hom**: The zeroth Ext is naturally isomorphic to Hom.
   Mathlib: `Ext.homEquiv₀ : Ext X Y 0 ≃ (X ⟶ Y)`

3. **Projective vanishing**: Ext^{n+1}(P, Y) = 0 for P projective.
   Mathlib: `isZero_Ext_succ_of_projective`

4. **Long exact sequence**: Short exact 0 → N₁ → N₂ → N₃ → 0 induces LES.
   Mathlib: `Ext.covariantSequence_exact` (second variable)
           `Ext.contravariantSequence_exact` (first variable)

5. **Computation**: Ext^n(X, Y) = H^n(Hom(P•, Y)) for projective resolution P• → X.
   Mathlib: `ProjectiveResolution.isoExt`
-/

end LemmaFeld.TensorCategories.Chapter1
