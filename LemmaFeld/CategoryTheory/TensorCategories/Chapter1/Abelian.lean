/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Images
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.CategoryTheory.Abelian.FreydMitchell
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Basic

/-!
# Chapter 1, Section 1.3: Definition of Abelian Category

This file establishes the correspondence between Etingof et al. "Tensor Categories"
§1.3 and mathlib's abelian category infrastructure.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.3

## §1.3 Summary

The book defines:
- **Definition 1.3.1**: Abelian category via canonical decomposition K → X → I → Y → C
- **Remark 1.3.2**: Uniqueness of canonical decomposition
- **Example 1.3.3**: Vec, modules, comodules are abelian
- **Definition 1.3.4**: Mono (Ker = 0) and Epi (Coker = 0)
- **Definition 1.3.5**: Subobject, quotient object, subquotient
- **Definition 1.3.7**: Indecomposable abelian category
- **Theorem 1.3.8**: Mitchell embedding theorem

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Kernel | `kernel f` | `Mathlib.CategoryTheory.Limits.Shapes.Kernels` |
| Cokernel | `cokernel f` | Same file |
| Abelian category | `Abelian C` | `Mathlib.CategoryTheory.Abelian.Basic` |
| Coimage = Coker(Ker) | `Abelian.coimage f` | `Mathlib.CategoryTheory.Abelian.Images` |
| Image = Ker(Coker) | `Abelian.image f` | Same file |
| Coimage ≅ Image | `coimageImageComparison` is `IsIso` | Key property |
| Mono (Ker = 0) | `Mono f` + `kernel.ι_of_mono` | `kernel.ι f = 0` |
| Epi (Coker = 0) | `Epi f` + `cokernel.π_of_epi` | `cokernel.π f = 0` |
| Normal mono | `IsNormalMonoCategory C` | Every mono is a kernel |
| Normal epi | `IsNormalEpiCategory C` | Every epi is a cokernel |
| Freyd-Mitchell | `FreydMitchell.functor C` | Full faithful embedding into R-Mod |

-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

/-! ## §1.3 Preliminaries: Kernels and Cokernels

Before Definition 1.3.1, the book defines kernels and cokernels.

Book: "The kernel Ker(f) of f : X → Y is an object K with morphism k : K → X such that
fk = 0, and if k' : K' → X is such that fk' = 0 then there exists a unique ℓ : K' → K
such that kℓ = k'."

Mathlib: `kernel f` in `Mathlib.CategoryTheory.Limits.Shapes.Kernels`
-/

section KernelCokernel

variable {C : Type*} [Category C] [Abelian C]

-- Book's kernel definition maps to mathlib's kernel
-- k : K → X is `kernel.ι f : kernel f ⟶ X`
-- fk = 0 is `kernel.condition : kernel.ι f ≫ f = 0`
-- Universal property is `kernel.lift`

example {X Y : C} (f : X ⟶ Y) : (kernel.ι f) ≫ f = 0 := kernel.condition f

-- Universal property: any k' : W → X with k' ≫ f = 0 factors through kernel.ι f
example {X Y W : C} (f : X ⟶ Y) (k' : W ⟶ X) (h : k' ≫ f = 0) :
    (kernel.lift f k' h) ≫ kernel.ι f = k' := kernel.lift_ι f k' h

-- Dual: cokernel
-- c : Y → C is `cokernel.π f : Y ⟶ cokernel f`
-- cf = 0 is `cokernel.condition : f ≫ cokernel.π f = 0`
-- Universal property is `cokernel.desc`

example {X Y : C} (f : X ⟶ Y) : f ≫ cokernel.π f = 0 := cokernel.condition f

-- Universal property: any c' : Y → W with f ≫ c' = 0 factors through cokernel.π f
example {X Y W : C} (f : X ⟶ Y) (c' : Y ⟶ W) (h : f ≫ c' = 0) :
    cokernel.π f ≫ (cokernel.desc f c' h) = c' := cokernel.π_desc f c' h

end KernelCokernel

/-! ## §1.3 Definition 1.3.1: Abelian Category

Book: "An abelian category is an additive category C in which for every morphism
φ : X → Y there exists a sequence K →[k] X →[i] I →[j] Y →[c] C with:
1. ji = φ
2. (K, k) = Ker(φ), (C, c) = Coker(φ)
3. (I, i) = Coker(k), (I, j) = Ker(c)"

This says: Image = Coker(Ker(φ)) = Ker(Coker(φ)), and φ factors through it.

Mathlib: `CategoryTheory.Abelian` class combines:
- `Preadditive C` — additive structure on Hom sets
- `HasKernels C` — every morphism has a kernel
- `HasCokernels C` — every morphism has a cokernel
- `IsNormalMonoCategory C` — every mono is a kernel (of its cokernel)
- `IsNormalEpiCategory C` — every epi is a cokernel (of its kernel)
- `HasFiniteProducts C` — for additive category axiom (A3)

The key theorem is that in an abelian category, the comparison map
`Abelian.coimage f → Abelian.image f` is an isomorphism.
-/

section AbelianCategory

variable {C : Type*} [Category C] [Abelian C]

/-! ### The Canonical Decomposition

Book equation (1.2): K → X → I → Y → C

In mathlib:
- K = `kernel f`
- k = `kernel.ι f`
- I (as coimage) = `Abelian.coimage f` = `cokernel (kernel.ι f)`
- i = `Abelian.coimage.π f` : X → coimage f
- I (as image) = `Abelian.image f` = `kernel (cokernel.π f)`
- j = `Abelian.image.ι f` : image f → Y
- C = `cokernel f`
- c = `cokernel.π f`

The isomorphism between coimage and image is `coimageImageComparison f`.
-/

-- The factorization: f = coimage.π f ≫ coimageImageComparison f ≫ image.ι f
-- (Book's ji = φ, where the middle map is an isomorphism)
example {X Y : C} (f : X ⟶ Y) :
    Abelian.coimage.π f ≫ coimageImageComparison f ≫ Abelian.image.ι f = f :=
  coimage_image_factorisation f

-- In an abelian category, the comparison is an isomorphism
-- This is the key property that makes coimage = image
example {X Y : C} (f : X ⟶ Y) : IsIso (coimageImageComparison f) :=
  inferInstance

-- Therefore we get the book's canonical decomposition:
-- kernel f → X → (coimage f ≅ image f) → Y → cokernel f

end AbelianCategory

/-! ## §1.3 Remark 1.3.2: Uniqueness

Book: "The canonical decomposition of a morphism is unique up to a unique isomorphism."

In mathlib, this follows from:
1. Kernels and cokernels are unique up to unique isomorphism (limit/colimit property)
2. The coimage and image are defined via kernel/cokernel
3. The isomorphism coimageImageComparison is uniquely determined
-/

/-! ## §1.3 Example 1.3.3: Examples of Abelian Categories

Book lists:
- Category of abelian groups
- Category of modules over a ring
- Vec (vector spaces over k)
- Finite dimensional vector spaces
- Modules over an associative k-algebra
- Comodules over a coalgebra

Mathlib instances:
-/

section Examples

-- ModuleCat R is abelian (for any ring R)
-- instance : Abelian (ModuleCat R) — in Mathlib.Algebra.Category.ModuleCat.Abelian

-- Note: Vec = ModuleCat k for a field k
-- FdVec (finite dim) is also abelian but requires more setup

end Examples

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
