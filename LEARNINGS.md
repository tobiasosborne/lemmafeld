# Learnings

## 2026-01-28: Session Orientation

**Observation:** `bd ready` returns issues from Chapters 4, 6, 7 first because they have no blockers set. However, the implementation plan requires starting with Chapter 1-2 (foundations) before later chapters.

**Action:** Always check issue numbering (TC X.Y.Z) and start with lowest chapter number, not just what `bd ready` returns.

## 2026-01-28: TC 1.1.1 - Mathlib Category Theory Review

**Task:** Review mathlib's category theory foundations for Chapter 1 topics.

### Mathlib Has (Chapter 1 Topics):

| Topic | Mathlib Location | Status |
|-------|------------------|--------|
| **Abelian categories** | `CategoryTheory.Abelian` | ✅ Complete - includes kernels, cokernels, image, normal mono/epi |
| **Preadditive categories** | `CategoryTheory.Preadditive.Basic` | ✅ Complete - `Preadditive` class with `homGroup`, `add_comp`, `comp_add` |
| **Exact sequences** | `CategoryTheory.ShortComplex` | ✅ Complete - `ShortComplex.Exact`, kernel/cokernel conditions |
| **Simple objects** | `CategoryTheory.Simple` | ✅ Complete - `Simple X` structure, Schur's lemma (`isIso_of_hom_simple`) |
| **Projective/Injective** | `CategoryTheory.Projective`, `CategoryTheory.Injective` | ✅ Complete - includes `EnoughProjectives`, `EnoughInjectives` |
| **Coalgebras** | `Coalgebra`, `CoalgebraCat` | ✅ Complete - R-coalgebras with comul/counit |
| **Comonoid objects** | `Comon_` | ✅ Complete - comonoid objects in monoidal categories |

### Mathlib Has (Chapter 2 Topics):

| Topic | Mathlib Location | Status |
|-------|------------------|--------|
| **Monoidal categories** | `CategoryTheory.MonoidalCategory` | ✅ Complete - tensor, associator, unitors, pentagon/triangle |
| **Braided categories** | `CategoryTheory.BraidedCategory` | ✅ Complete - braiding, hexagon identities |
| **Symmetric categories** | `CategoryTheory.SymmetricCategory` | ✅ Complete - symmetry condition |
| **Monoidal functors** | `CategoryTheory.Functor.Monoidal`, `LaxMonoidal` | ✅ Complete |
| **Duals (rigid)** | `CategoryTheory.HasLeftDual`, `HasRightDual` | ✅ Complete - exact pairings |

### Likely Gaps (Need Verification):

| Topic | Expected Location | Status |
|-------|-------------------|--------|
| Jordan-Hölder theorem | ? | ⚠️ May need implementation |
| Krull-Schmidt theorem | ? | ⚠️ May need implementation |
| Grothendieck group Gr(C) | ? | ⚠️ May need implementation |
| Ext groups | `CategoryTheory.Abelian.Ext` ? | ⚠️ Partial - check coverage |
| Deligne tensor product | ? | ⚠️ Likely needs implementation |
| Coradical filtration | ? | ⚠️ Likely needs implementation |

### Key Imports for Tensor Categories Work:

```lean
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Algebra.Category.CoalgebraCat.Basic
```

**Recommendation:** Most Chapter 1-2 foundations exist in mathlib. Focus implementation on:
1. Verifying mathlib APIs match book definitions
2. Adding any missing notation/convenience lemmas
3. Implementing genuinely missing concepts (Jordan-Hölder, Deligne tensor product, etc.)

## 2026-01-28: TC 1.1.2 - Notation Conventions

**Task:** Define any missing notation conventions from §1.1.

**Book §1.1 Notation:**
- `id_C` - identity endofunctor
- `C^∨` - opposite/dual category
- Locally small / essentially small
- `Hom_C(X,Y)` - morphism sets
- Fields algebraically closed by default

**Mathlib Equivalents:**
| Book | Mathlib |
|------|---------|
| `id_C` | `𝟭 C` or `Functor.id C` |
| `C^∨` | `Cᵒᵖ` |
| locally small | `LocallySmall` |
| essentially small | `EssentiallySmall` |
| `Hom_C(X,Y)` | `X ⟶ Y` |

**Conclusion:** No notation gaps - mathlib covers all §1.1 conventions. No code needed.

## 2026-01-28: TC 1.1.3 - Locally Small and Essentially Small APIs

**Task:** Establish locally small and essentially small category APIs.

**Book §1.1 says:**
> "A category is called *locally small* if for any objects X, Y, Hom_C(X, Y) is a set, and is called *essentially small* if in addition its isomorphism classes of objects form a set. In other words, an essentially small category is a category equivalent to a small category."

**Mathlib has:**

| Concept | Mathlib | Import |
|---------|---------|--------|
| Locally small | `CategoryTheory.LocallySmall` | `Mathlib.CategoryTheory.Category.Basic` |
| Essentially small | `CategoryTheory.EssentiallySmall` | `Mathlib.CategoryTheory.EssentiallySmall` |

**Mathlib definitions (verified):**

```lean
-- LocallySmall: for all X Y, the hom-set is w-small
class LocallySmall (C : Type u) [Category.{v} C] : Prop where
  hom_small : ∀ (X Y : C), Small.{w} (X ⟶ Y)

-- EssentiallySmall: equivalent to a small category
class EssentiallySmall (C : Type u) [Category.{v} C] : Prop where
  equiv_smallCategory : ∃ S [SmallCategory S], Nonempty (C ≌ S)
```

**Book ↔ Mathlib mapping:**
- Book "Hom_C(X,Y) is a set" = Mathlib `Small (X ⟶ Y)` (hom-set fits in universe w)
- Book "equivalent to a small category" = Mathlib `∃ S, Nonempty (C ≌ S)`

**Conclusion:** Mathlib APIs match book definitions exactly. No code needed.
