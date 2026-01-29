# Chapter 1: Abelian Categories (§1.1-1.3)

## Critical Failure Record (2026-01-28)

**What happened:** An agent spent an entire session "verifying" mathlib coverage and writing documentation, but CREATED ZERO LEAN FILES.

**Why this is wrong:**
- The project goal is to FORMALIZE the book in Lean
- Every issue must produce a `.lean` file
- Documentation alone is NOT sufficient

**For future agents:** The mathlib research below is USEFUL as reference, but you still need to CREATE LEAN FILES that import the mathlib modules and add book reference comments.

---

## §1.1: Categorical Prerequisites

**Book notation → Mathlib:**

| Book | Mathlib |
|------|---------|
| `id_C` | `Functor.id C` or `𝟭 C` |
| `C^∨` | `Cᵒᵖ` |
| locally small | `LocallySmall` |
| essentially small | `EssentiallySmall` |
| `Hom_C(X,Y)` | `X ⟶ Y` |

**Mathlib definitions:**

```lean
-- LocallySmall: for all X Y, the hom-set is w-small
class LocallySmall (C : Type u) [Category.{v} C] : Prop where
  hom_small : ∀ (X Y : C), Small.{w} (X ⟶ Y)

-- EssentiallySmall: equivalent to a small category
class EssentiallySmall (C : Type u) [Category.{v} C] : Prop where
  equiv_smallCategory : ∃ S [SmallCategory S], Nonempty (C ≌ S)
```

**Lean files:** `Chapter1/Basic.lean`, `Chapter1/Notation.lean`, `Chapter1/SmallCategories.lean`

---

## §1.2: Preadditive and Additive Categories

**Book Definition 1.2.1** (Additive category):
- (A1) Every Hom(X,Y) is an abelian group, composition is biadditive
- (A2) Zero object exists
- (A3) Direct sums exist

**Key insight:** Mathlib doesn't have a single "Additive category" class. Use:
```lean
variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
```

**Mathlib definitions:**

```lean
-- Preadditive (A1)
class Preadditive where
  homGroup : ∀ P Q : C, AddCommGroup (P ⟶ Q)
  add_comp : ∀ (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R), (f + f') ≫ g = f ≫ g + f' ≫ g
  comp_add : ∀ (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R), f ≫ (g + g') = f ≫ g + f ≫ g'

-- Linear (k-linear)
class Linear (R : Type w) [Semiring R] (C : Type u) [Category C] [Preadditive C] where
  homModule : ∀ X Y : C, Module R (X ⟶ Y)
  smul_comp : ∀ (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g
  comp_smul : ∀ (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g
```

**Lean files:** `Chapter1/Additive.lean`, `Chapter1/DirectSum.lean`

---

## §1.3: Abelian Categories

**Book Definition 1.3.1:** Abelian = additive + canonical decomposition K → X → I → Y → C.

**Mathlib's definition:**

```lean
class Abelian extends Preadditive C, IsNormalMonoCategory C, IsNormalEpiCategory C where
  [has_finite_products : HasFiniteProducts C]
  [has_kernels : HasKernels C]
  [has_cokernels : HasCokernels C]
```

**Canonical decomposition APIs:**

| Book | Mathlib |
|------|---------|
| K | `kernel f` |
| k: K → X | `kernel.ι f` |
| Coimage = Coker(k) | `Abelian.coimage f` = `cokernel (kernel.ι f)` |
| Image = Ker(c) | `Abelian.image f` = `kernel (cokernel.π f)` |
| Coimage ≅ Image | `coimageImageComparison f` is `IsIso` |
| C | `cokernel f` |

**Key theorem:**
```lean
coimage_image_factorisation : coimage.π f ≫ coimageImageComparison f ≫ image.ι f = f
```

**Mono/Epi characterization:**

| Book | Mathlib |
|------|---------|
| Mono f ⟺ Ker(f) = 0 | `kernel.ι_of_mono`, `Preadditive.mono_of_kernel_zero` |
| Epi f ⟺ Coker(f) = 0 | `cokernel.π_of_epi`, `Preadditive.epi_of_cokernel_zero` |
| Mono + Epi → Iso | `isIso_of_mono_of_epi f` |

**Freyd-Mitchell embedding (Theorem 1.3.8):** IN MATHLIB at `Mathlib.CategoryTheory.Abelian.FreydMitchell`
- `FreydMitchell.EmbeddingRing C` — the ring
- `FreydMitchell.functor C` — the full faithful embedding C → R-Mod

**Lean file:** `Chapter1/Abelian.lean`
