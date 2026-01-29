# Chapter 1: External Tensor Product (§1.11-1.12)

## §1.11.1: Deligne Tensor Product

**Book Definition 1.11.1:** C ⊠ D is the abelian k-linear category universal for right exact bifunctors C × D → A.

### Mathlib Status — SIGNIFICANT GAP

| Concept | Mathlib | Notes |
|---------|---------|-------|
| External product of diagrams | `CategoryTheory.MonoidalCategory.ExternalProduct` | For F₁ : J₁ ⥤ C, F₂ : J₂ ⥤ C |
| Deligne tensor product | **NOT IN MATHLIB** | Universal category for bifunctors |
| Locally finite abelian | **NOT IN MATHLIB** | Finite length + finite dim Hom |

**Key distinction:**
- Mathlib's `ExternalProduct` is for diagrams INTO a monoidal category C
- Book's C ⊠ D is the tensor product OF two categories C and D

---

## Our Definitions

### Locally Finite Abelian Category

```lean
class LocallyFiniteAbelian (k : Type*) [Field k] (C : Type*) [Category C]
    [Abelian C] [Linear k C] : Prop where
  finite_length : ∀ X : C, IsFiniteLengthObject X
  finite_dim_hom : ∀ (X Y : C), Module.Finite k (X ⟶ Y)
```

### Right Exact Bifunctors

```lean
class IsRightExactFirst (F : C × D ⥤ E) : Prop where
  preserves_colimits_first : ∀ Y : D, PreservesFiniteColimits ((Prod.currying C D E).obj F Y)

class IsRightExactSecond (F : C × D ⥤ E) : Prop where
  preserves_colimits_second : ∀ X : C, PreservesFiniteColimits (F.flip.obj X)

class IsRightExactBifunctor (F : C × D ⥤ E) extends IsRightExactFirst F, IsRightExactSecond F
```

### Deligne Tensor Product Data

```lean
structure DeligneTensorProductData (C D E : Type*) [Category C] [Category D] [Category E]
    [Abelian C] [Abelian D] [Abelian E] where
  boxtimes : C × D ⥤ E
  right_exact : IsRightExactBifunctor boxtimes
```

---

## Gaps for Full Implementation

1. **Constructing C ⊠ D category** — via coalgebra comodules (Theorem 1.9.15)
2. **Universal property** — existence + uniqueness of extension
3. **Functoriality** — F ⊠ G for right exact functors
4. **Hom tensor isomorphism** — Hom(X₁ ⊠ Y₁, X₂ ⊠ Y₂) ≅ Hom(X₁, X₂) ⊗ Hom(Y₁, Y₂)

---

## Prerequisites

Before full implementation, need:
- TC 1.9 Coalgebras (partial in `Coalgebras.lean`)
- TC 1.9.15 Comodule category reconstruction theorem
- `Module.Finite k (X ⟶ Y)` for finite dimensional Hom condition

**Lean file:** `Chapter1/ExternalTensorProduct.lean`
