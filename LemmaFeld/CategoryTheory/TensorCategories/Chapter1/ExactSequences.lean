/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Algebra.Homology.ShortComplex.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Chapter 1, Section 1.4: Exact Sequences

This file establishes the correspondence between Etingof et al. "Tensor Categories"
§1.4 and mathlib's exact sequence infrastructure.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.4

## §1.4 Summary

The book defines:
- **Definition 1.4.1**: Exact sequence (Im(f_{i-1}) = Ker(f_i)), short exact sequence
- **Definition 1.4.2**: Ext¹(Y, X) as isomorphism classes of extensions
- **Exercise 1.4.3**: Baer sum defines addition on Ext¹(Y, X)

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Sequence X₁ → X₂ → X₃ | `ShortComplex C` | Three-term complex with g ∘ f = 0 |
| Exact at middle | `S.Exact` | Homology is zero |
| Short exact 0 → X → Y → Z → 0 | `S.ShortExact` | Exact + Mono f + Epi g |
| X subobject of Y | `ShortExact.fIsKernel` | f is kernel of g |
| Z ≅ Y/X | `ShortExact.gIsCokernel` | g is cokernel of f |
| Ext¹(Y, X) | `Ext R C 1` | Derived functor (not Yoneda Ext) |

## Note on Ext

Mathlib defines Ext via derived functors (`Mathlib.CategoryTheory.Abelian.Ext`),
not via isomorphism classes of extensions (Yoneda Ext). The two are equivalent
in abelian categories with enough projectives.

-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

/-! ## §1.4 Definition 1.4.1: Exact Sequences

Book: "A sequence of morphisms ⋯ → X_{i-1} →[f_{i-1}] X_i →[f_i] X_{i+1} → ⋯
in an abelian category is called *exact in degree i* if Im(f_{i-1}) = Ker(f_i).
It is called *exact* if it is exact in every degree."

Mathlib uses `ShortComplex C` for a three-term complex X₁ →[f] X₂ →[g] X₃ with g ∘ f = 0.
The condition `S.Exact` says the homology is zero, i.e., Im(f) = Ker(g).
-/

section ShortComplex

variable {C : Type*} [Category C] [Abelian C]

-- A ShortComplex is a three-term sequence X₁ →[f] X₂ →[g] X₃ with g ∘ f = 0
-- Book's "exact in degree i" = Mathlib's "homology is zero at X₂"

-- The composition condition g ∘ f = 0
example (S : ShortComplex C) : S.f ≫ S.g = 0 := S.zero

-- Book: "Exact in degree i means Im(f_{i-1}) = Ker(f_i)"
-- Mathlib: `S.Exact` means the homology at X₂ is zero

-- Exact means: the induced map cokernel(f) → kernel(g) or equivalently
-- the homology object is zero
example (S : ShortComplex C) (h : S.Exact) : S.Exact := h

end ShortComplex

/-! ## §1.4 Definition 1.4.1: Short Exact Sequences

Book: "An exact sequence 0 → X → Y → Z → 0 is called a short exact sequence."

Mathlib: `S.ShortExact` for a `ShortComplex C` means:
1. `S.Exact` (Im(f) = Ker(g))
2. `Mono S.f` (f is injective, i.e., 0 → X is exact)
3. `Epi S.g` (g is surjective, i.e., → Z → 0 is exact)
-/

section ShortExactSequence

variable {C : Type*} [Category C] [Abelian C]

-- Book: "In a short exact sequence 0 → X → Y → Z → 0,
-- X is a subobject of Y and Z ≅ Y/X is the corresponding quotient."

-- A short exact sequence has:
-- 1. Exactness at the middle term
-- 2. f is a mono (kernel inclusion)
-- 3. g is an epi (cokernel projection)

-- The structure `ShortExact` packages these conditions
example (S : ShortComplex C) (h : S.ShortExact) : S.Exact := h.exact
example (S : ShortComplex C) (h : S.ShortExact) : Mono S.f := h.mono_f
example (S : ShortComplex C) (h : S.ShortExact) : Epi S.g := h.epi_g

-- Book: "X is a subobject of Y" — f is the kernel of g
-- ShortExact.fIsKernel shows f is the kernel of g
example (S : ShortComplex C) (h : S.ShortExact) :
    IsLimit (KernelFork.ofι S.f S.zero) := h.fIsKernel

-- Book: "Z ≅ Y/X" — g is the cokernel of f
-- ShortExact.gIsCokernel shows g is the cokernel of f
example (S : ShortComplex C) (h : S.ShortExact) :
    IsColimit (CokernelCofork.ofπ S.g S.zero) := h.gIsCokernel

end ShortExactSequence

/-! ## Short Exact Sequence Properties

Key properties of short exact sequences in abelian categories:
-/

section Properties

variable {C : Type*} [Category C] [Abelian C]

-- If X₃ ≅ 0, then f is an isomorphism (X₁ ≅ X₂)
-- Book: in 0 → X → Y → 0 → 0, we have X ≅ Y
example (S : ShortComplex C) (h : S.ShortExact) (hz : IsZero S.X₃) : IsIso S.f :=
  h.isIso_f_iff.mpr hz

-- Dually, if X₁ ≅ 0, then g is an isomorphism (X₂ ≅ X₃)
-- Book: in 0 → 0 → Y → Z → 0, we have Y ≅ Z
example (S : ShortComplex C) (h : S.ShortExact) (hz : IsZero S.X₁) : IsIso S.g :=
  h.isIso_g_iff.mpr hz

end Properties

/-! ## §1.4 Definition 1.4.2: Extensions and Ext¹

Book: "Let S : 0 → X → Z → Y → 0 and S' : 0 → X → Z' → Y → 0 be short exact sequences.
A morphism from S to S' is a morphism f : Z → Z' that restricts to id_X and induces id_Y.
The set of exact sequences 0 → X → Z → Y → 0 up to isomorphism is denoted Ext¹(Y, X)
and is called the set of extensions of Y by X."

Mathlib uses derived functors for Ext, not the Yoneda extension construction.
However, the two are equivalent when the category has enough projectives.

Key insight: Mathlib's `ShortComplex.Splitting` represents split exact sequences,
which correspond to the zero element in Ext¹(Y, X).
-/

/-! ## §1.4 Exercise 1.4.3: Addition on Ext¹

Book describes Baer sum:
Given S : 0 → X → Z → Y → 0 and S' : 0 → X → Z' → Y → 0,
define S + S' using pullback and pushout.

Mathlib: Since Ext is defined via derived functors landing in `ModuleCat R`,
the addition structure comes automatically from the R-module structure.

The Baer sum construction is mathematically equivalent but not directly formalized
as explicit pullback/pushout in mathlib.
-/

/-! ## Constructing Short Exact Sequences

Mathlib provides ways to construct short exact sequences:
-/

section Construction

variable {C : Type*} [Category C] [Abelian C]

-- From a mono f : X → Y, we get a short exact sequence
-- 0 → X → Y → cokernel f → 0

-- From f and g with g ∘ f = 0, we can ask if this is short exact
example {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (w : f ≫ g = 0) :
    ShortComplex C := ShortComplex.mk f g w

end Construction

/-! ## Five Lemma

The five lemma is a key tool for working with exact sequences.
Mathlib has it as `isIso₂_of_shortExact_of_isIso₁₃`.
-/

section FiveLemma

-- The five lemma: given a morphism of short exact sequences where
-- the outer maps are isomorphisms, the middle map is an isomorphism.
-- This is in `Mathlib.Algebra.Homology.ShortComplex.ShortExact`

end FiveLemma

end LemmaFeld.TensorCategories.Chapter1
