/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.FreydMitchell
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Basic

/-!
# Chapter 1, Section 1.3: Abelian Category Properties

This file covers §1.3.4-1.3.8 of Etingof et al. "Tensor Categories":
- §1.3.4: Mono/epi characterizations via kernel/cokernel
- §1.3.5: Subobjects and quotient objects
- §1.3.7: Indecomposable abelian categories
- §1.3.8: Freyd-Mitchell embedding theorem

For the core definitions (§1.3.1-1.3.3), see `Abelian.lean`.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.3

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Mono (Ker = 0) | `Mono f` + `kernel.ι_of_mono` | `kernel.ι f = 0` |
| Epi (Coker = 0) | `Epi f` + `cokernel.π_of_epi` | `cokernel.π f = 0` |
| Normal mono | `IsNormalMonoCategory C` | Every mono is a kernel |
| Normal epi | `IsNormalEpiCategory C` | Every epi is a cokernel |
| Freyd-Mitchell | `FreydMitchell.functor C` | Full faithful embedding into R-Mod |

-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

/-! ## §1.3 Definition 1.3.4: Monomorphism and Epimorphism

Book: "A morphism f : X → Y is a monomorphism if Ker(f) = 0.
It is an epimorphism if Coker(f) = 0."

Mathlib: `Mono f` and `Epi f` are defined abstractly. In an abelian category,
these have equivalent characterizations via kernels and cokernels.

Key lemmas:
- `kernel.ι_of_mono f : kernel.ι f = 0` (when f is mono)
- `mono_of_kernel_zero h : Mono f` (when kernel.ι f = 0)
- `cokernel.π_of_epi f : cokernel.π f = 0` (when f is epi)
- `epi_of_cokernel_zero h : Epi f` (when cokernel.π f = 0)
-/

section MonoEpi

variable {C : Type*} [Category C] [Abelian C]

-- Book's "Ker(f) = 0" characterization for monomorphisms
-- Mathlib: Mono f ↔ kernel.ι f = 0

-- If f is mono, then kernel.ι f = 0
example {X Y : C} (f : X ⟶ Y) [Mono f] : kernel.ι f = 0 := kernel.ι_of_mono f

-- Conversely, if kernel.ι f = 0, then f is mono
example {X Y : C} (f : X ⟶ Y) (h : kernel.ι f = 0) : Mono f :=
  Preadditive.mono_of_kernel_zero h

-- Dual for epimorphisms: Epi f ↔ cokernel.π f = 0

-- If f is epi, then cokernel.π f = 0
example {X Y : C} (f : X ⟶ Y) [Epi f] : cokernel.π f = 0 := cokernel.π_of_epi f

-- Conversely, if cokernel.π f = 0, then f is epi
example {X Y : C} (f : X ⟶ Y) (h : cokernel.π f = 0) : Epi f :=
  Preadditive.epi_of_cokernel_zero h

-- Book: "a morphism is both mono and epi iff it is an isomorphism"
-- This is a key property of abelian categories

example {X Y : C} (f : X ⟶ Y) [Mono f] [Epi f] : IsIso f := isIso_of_mono_of_epi f

end MonoEpi

/-! ## §1.3 Definition 1.3.5: Subobjects and Quotient Objects

Book: "A subobject of Y is an object X together with a monomorphism i : X → Y.
A quotient object of Y is an object Z with an epimorphism p : Y → Z.
A subquotient is a quotient of a subobject."

Mathlib:
- `Subobject Y` — the poset of subobjects (mono classes)
- Quotients are handled via cokernels
- For a subobject X ⊂ Y (mono f : X → Y), the quotient Y/X = cokernel f
-/

section SubobjectQuotient

variable {C : Type*} [Category C] [Abelian C]

-- Subobject Y is the poset of monomorphisms into Y (up to iso)
-- Access via: `Subobject Y` in `Mathlib.CategoryTheory.Subobject.Basic`

-- For a mono f : X → Y, the quotient Y/X is the cokernel
example {X Y : C} (f : X ⟶ Y) [Mono f] : C := cokernel f

-- The quotient map Y → Y/X
example {X Y : C} (f : X ⟶ Y) [Mono f] : Y ⟶ cokernel f := cokernel.π f

-- This is an epi (Y → Y/X is surjective)
example {X Y : C} (f : X ⟶ Y) [Mono f] : Epi (cokernel.π f) := inferInstance

end SubobjectQuotient

/-! ## §1.3 Definition 1.3.7: Indecomposable Abelian Category

Book: "An abelian category C is indecomposable if it is not equivalent to a
direct sum of two nonzero categories."

This is related to the study of block decompositions. Mathlib doesn't have a
dedicated `Indecomposable` class for categories, but the concept can be expressed
using equivalences.
-/

/-! ## §1.3 Theorem 1.3.8: Freyd-Mitchell Embedding

Book: "Every abelian category is equivalent, as an additive category, to a full
subcategory of the category of left modules over an associative unital ring A."

Mathlib: `Mathlib.CategoryTheory.Abelian.FreydMitchell` has a complete formalization!

| Book Statement | Mathlib | Type |
|----------------|---------|------|
| Embedding ring A | `FreydMitchell.EmbeddingRing C` | Type |
| Embedding functor F : C → A-Mod | `FreydMitchell.functor C` | Functor |
| F is full | `FreydMitchell.instFullModuleCatEmbeddingRingFunctor` | Instance |
| F is faithful | `FreydMitchell.instFaithfulModuleCatEmbeddingRingFunctor` | Instance |
| F preserves finite limits | Part of `freyd_mitchell` theorem | Instance |
| F preserves finite colimits | Part of `freyd_mitchell` theorem | Instance |
-/

section FreydMitchellEmbedding

universe u v

variable (C : Type u) [Category.{v} C] [Abelian C]

-- The ring into whose module category we embed
-- `FreydMitchell.EmbeddingRing C` is a ring (in Type (max u v))
example : Ring (FreydMitchell.EmbeddingRing C) := inferInstance

-- The embedding functor: C → ModuleCat (EmbeddingRing C)
#check (FreydMitchell.functor C : C ⥤ ModuleCat (FreydMitchell.EmbeddingRing C))

-- The functor is full: every morphism in the image lifts to C
example : (FreydMitchell.functor C).Full := inferInstance

-- The functor is faithful: reflects equality of morphisms
example : (FreydMitchell.functor C).Faithful := inferInstance

-- The main theorem: full and faithful, preserves finite (co)limits
-- `freyd_mitchell` states the existence with all four properties
#check @freyd_mitchell C _ _

end FreydMitchellEmbedding

end LemmaFeld.TensorCategories.Chapter1
