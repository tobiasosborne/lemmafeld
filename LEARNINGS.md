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

## 2026-01-28: TC 1.2.1 - Preadditive and Additive Categories

**Task:** Verify mathlib's Preadditive and Additive category definitions match §1.2.

**Book §1.2 defines:**

**Definition 1.2.1** (Additive category): A category C satisfying:
- (A1) Every Hom(X,Y) is an abelian group, composition is biadditive
- (A2) Zero object exists with Hom(0,0) = 0
- (A3) Direct sums exist (with p₁i₁ = id, p₂i₂ = id, i₁p₁ + i₂p₂ = id)

**Definition 1.2.2** (k-linear category): Additive category where Hom(X,Y) are k-vector spaces and composition is k-linear.

**Definition 1.2.3** (Additive functor): Functor where Hom maps are group homomorphisms.

**Proposition 1.2.4**: Additive functor F satisfies F(X⊕Y) ≅ F(X)⊕F(Y).

**Mathlib equivalents:**

| Book Concept | Mathlib | Import |
|-------------|---------|--------|
| (A1) Hom groups + biadditive | `Preadditive` class | `Mathlib.CategoryTheory.Preadditive.Basic` |
| (A2) Zero object | `HasZeroObject` class | `Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects` |
| (A3) Direct sums | `HasBinaryBiproducts` class | `Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts` |
| k-linear category | `Linear R C` | `Mathlib.CategoryTheory.Linear.Basic` |
| Additive functor | `Functor.Additive` | `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` |
| k-linear functor | `Functor.Linear R` | `Mathlib.CategoryTheory.Linear.LinearFunctor` |
| Prop 1.2.4 | `PreservesBinaryBiproducts` | `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts` |

**Key insight:** Mathlib doesn't have a single "Additive category" class. Instead, an "additive category" in the book's sense requires three typeclasses:
```lean
variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
```

**Mathlib definitions (verified):**

```lean
-- Preadditive (A1): Hom groups with biadditive composition
class Preadditive where
  homGroup : ∀ P Q : C, AddCommGroup (P ⟶ Q)
  add_comp : ∀ (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R), (f + f') ≫ g = f ≫ g + f' ≫ g
  comp_add : ∀ (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R), f ≫ (g + g') = f ≫ g + f ≫ g'

-- Linear (k-linear): R-module structure on Hom
class Linear (R : Type w) [Semiring R] (C : Type u) [Category C] [Preadditive C] where
  homModule : ∀ X Y : C, Module R (X ⟶ Y)
  smul_comp : ∀ (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g
  comp_smul : ∀ (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g

-- Additive functor: preserves addition
class Functor.Additive (F : C ⥤ D) : Prop where
  map_add : ∀ {X Y : C} {f g : X ⟶ Y}, F.map (f + g) = F.map f + F.map g
```

**Conclusion:** Mathlib has complete coverage of §1.2. No code needed.
