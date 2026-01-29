/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Images
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Chapter 1, Section 1.3: Definition of Abelian Category (Core)

This file establishes the correspondence between Etingof et al. "Tensor Categories"
§1.3 and mathlib's abelian category infrastructure. Covers §1.3.1-1.3.3.

For mono/epi characterizations (§1.3.4), subobjects (§1.3.5), and Freyd-Mitchell
embedding (§1.3.8), see `AbelianProperties.lean`.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.3

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Kernel | `kernel f` | `Mathlib.CategoryTheory.Limits.Shapes.Kernels` |
| Cokernel | `cokernel f` | Same file |
| Abelian category | `Abelian C` | `Mathlib.CategoryTheory.Abelian.Basic` |
| Coimage = Coker(Ker) | `Abelian.coimage f` | `Mathlib.CategoryTheory.Abelian.Images` |
| Image = Ker(Coker) | `Abelian.image f` | Same file |
| Coimage ≅ Image | `coimageImageComparison` is `IsIso` | Key property |

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

end LemmaFeld.TensorCategories.Chapter1
