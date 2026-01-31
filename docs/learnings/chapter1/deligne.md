# Chapter 1: External Tensor Product & Finite Dual (§1.11-1.12)

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

---

## §1.12: The Finite Dual of an Algebra

**Definition 1.12.1:** The finite dual A*_fin of A is the collection of all f ∈ A*
that vanish on a (two-sided) ideal of finite codimension.

**Proposition 1.12.2:** The maps Δ := m* and ε := u* (dual of multiplication
and unit) define a coalgebra structure on A*_fin.

**Remark 1.12.3:** If A has no finite dimensional modules, then A*_fin = 0.

### Mathlib Status — PARTIAL GAP

| Concept | Mathlib | Notes |
|---------|---------|-------|
| Two-sided ideal | `TwoSidedIdeal R` | `Mathlib.RingTheory.TwoSidedIdeal.Basic` |
| Quotient A/I | `I.ringCon.Quotient` | Has ring structure via RingCon |
| Dual space A* | `Module.Dual k A` | `Mathlib.LinearAlgebra.Dual.Defs` |
| Finite dual | `IsFiniteDualElem` | **NEW**: predicate in `FiniteDual.lean` |
| Coalgebra | `Coalgebra R A` | `Mathlib.RingTheory.Coalgebra.Basic` |

### Key Challenge: Module Structure on Quotients

The quotient `I.ringCon.Quotient` inherits a ring structure, but for it to be a
k-vector space, we need to show the k-algebra structure descends. Mathlib's
`TwoSidedIdeal` doesn't directly provide this.

### Our Definitions

```lean
/-- f is in the finite dual if it vanishes on some ideal with finite quotient -/
def IsFiniteDualElem (f : Module.Dual k A) : Prop :=
  ∃ I : TwoSidedIdeal A, (∃ _ : Fintype I.ringCon.Quotient, True)
    ∧ ∀ x ∈ I, f x = 0

/-- The counit on A*: ε(f) = f(1) -/
def dualCounit : Module.Dual k A →ₗ[k] k
```

---

### Pre-Comultiplication

```lean
/-- Multiplication as a linear map A ⊗ A → A -/
noncomputable def mulLinear : A ⊗[k] A →ₗ[k] A

/-- Pre-comultiplication Δ : A* → (A ⊗ A)* defined by Δ(f)(a ⊗ b) = f(ab) -/
noncomputable def dualComulAux : Module.Dual k A →ₗ[k] Module.Dual k (A ⊗[k] A)

/-- Δ(f) vanishes on I ⊗ A when f vanishes on I -/
lemma dualComulAux_vanishes_left
lemma dualComulAux_vanishes_right

/-- Coalgebra axioms (counit and coassociativity) -/
lemma dualComulAux_one_left (f) (b) : dualComulAux f (1 ⊗ₜ b) = f b
lemma dualComulAux_one_right (f) (a) : dualComulAux f (a ⊗ₜ 1) = f a
lemma dualComulAux_assoc (f) (a b c) : dualComulAux f ((a*b) ⊗ₜ c) = dualComulAux f (a ⊗ₜ (b*c))
```

**Lean file:** `Chapter1/FiniteDualCoalgebra.lean`

---

## Gaps for §1.12 Full Implementation

1. **Module structure on quotients** — show k-algebra structure descends
2. ~~**Finite codimension intersection**~~ — **RESOLVED**: `fintypeQuotientInf` proved
3. **Coalgebra structure** — **IN PROGRESS** (lemmafeld-oedl): Pre-comul defined, need to show Δ restricts to A*_fin ⊗ A*_fin
4. ~~**FiniteDual submodule**~~ — **RESOLVED**: `FiniteDual` submodule with closure proofs

**Lean files:** `Chapter1/FiniteDual.lean`, `Chapter1/FiniteDualCoalgebra.lean`
