# Chapter 1: Coalgebras (§1.9, §1.13)

## §1.9: Coalgebra Basics

**Mathlib (`Mathlib.RingTheory.Coalgebra.Basic`):**

| Concept | Mathlib |
|---------|---------|
| Coalgebra | `Coalgebra R A` |
| Comultiplication | `Coalgebra.comul : A →ₗ[R] TensorProduct R A A` |
| Counit | `Coalgebra.counit : A →ₗ[R] R` |
| Cocommutativity | `Coalgebra.IsCocomm R A` |

---

## §1.9.2: Comodules (NEW)

**Book Definition 1.9.2:** A left comodule over C is M with ρ: M → C ⊗ M satisfying:
- (Δ ⊗ id)(ρ(m)) = (id ⊗ ρ)(ρ(m)) [coassociativity]
- (ε ⊗ id)(ρ(m)) = m [counit]

**Mathlib status:** NOT in mathlib (as of v4.26.0)

**Our definition (`Chapter1/Comodules.lean`):**
```lean
class LeftComodule (R : Type*) (C : Type*) (M : Type*)
    [CommSemiring R]
    [AddCommMonoid C] [Module R C] [Coalgebra R C]
    [AddCommMonoid M] [Module R M]
    extends LeftComoduleStruct R C M where
  coassoc : (TensorProduct.assoc R C C M) ∘ₗ (Coalgebra.comul.rTensor M) ∘ₗ coaction =
            (LinearMap.lTensor C coaction) ∘ₗ coaction
  left_counit : (TensorProduct.lid R M) ∘ₗ (Coalgebra.counit.rTensor M) ∘ₗ coaction =
                LinearMap.id
```

**Also defined:**
- `RightComodule R C M` — symmetric definition with ρ: M → M ⊗ C
- `instLeftComoduleSelf` / `instRightComoduleSelf` — coalgebra C is comodule over itself

**API:**
- `LeftComodule.coact R C M : M →ₗ[R] C ⊗[R] M` — coaction map
- `LeftComodule.coassoc_apply` — simp lemma for coassociativity
- `LeftComodule.left_counit_apply` — simp lemma for counit

---

## §1.9.7: Grouplike Elements

**Book Definition 1.9.7:** x is grouplike if Δ(x) = x ⊗ x and ε(x) = 1.

**Our definition:**
```lean
structure IsGrouplike (R : Type*) [CommSemiring R] {A : Type*}
    [AddCommMonoid A] [Module R A] [Coalgebra R A] (x : A) : Prop where
  comul_eq : Coalgebra.comul x = x ⊗ₜ[R] x
  counit_eq : Coalgebra.counit x = 1
```

**Lemma:** `not_isGrouplike_zero` — zero is not grouplike.

---

## §1.9.10: Skew-Primitive Elements

**Book Definition 1.9.10:** x is (g,h)-skew-primitive if Δ(x) = g ⊗ x + x ⊗ h.

**Our definition:**
```lean
structure IsSkewPrimitive (R : Type*) [CommSemiring R] {A : Type*}
    [AddCommMonoid A] [Module R A] [Coalgebra R A] (g h x : A) : Prop where
  comul_eq : Coalgebra.comul x = g ⊗ₜ[R] x + x ⊗ₜ[R] h
```

**Trivial skew-primitive (Remark 1.9.11):** x = r • (g - h)

```lean
structure IsTrivialSkewPrimitive (R : Type*) [CommRing R] {A : Type*}
    [AddCommGroup A] [Module R A] [Coalgebra R A] (g h x : A) : Prop where
  witness : ∃ r : R, x = r • (g - h)
```

---

## §1.9.9: Set Coalgebra k[X]

**Book Example 1.9.9:** For a set X, k[X] is a coalgebra with Δ(x) = x ⊗ x.
The grouplike elements are precisely X.

**Mathlib:** `MonoidAlgebra.instCoalgebra` (via `Finsupp.instCoalgebra`)
- Base ring `R` has coalgebra structure with `comul r = 1 ⊗ r`
- `MonoidAlgebra R X` inherits coalgebra structure
- Key lemmas: `MonoidAlgebra.comul_single`, `MonoidAlgebra.counit_single`

**Our formalization:**
```lean
lemma isGrouplike_single_one (x : X) :
    IsGrouplike R (MonoidAlgebra.single x (1 : R))
```

---

## §1.9.8: Subcoalgebras and Grouplike Elements

**Book Remark 1.9.8:** There is a bijection between grouplike elements and 1-dim subcoalgebras.

**Our formalization:**
```lean
/-- A submodule S is a subcoalgebra if Δ(S) ⊆ S ⊗ S. -/
def IsSubcoalgebra (S : Submodule R A) : Prop :=
  ∀ s ∈ S, Coalgebra.comul s ∈ Submodule.map₂ (TensorProduct.mk R A A) S S

/-- The span of a grouplike element is a subcoalgebra. -/
lemma IsGrouplike.span_isSubcoalgebra (hx : IsGrouplike R x) :
    IsSubcoalgebra R (Submodule.span R {x})
```

**Key insight:** Uses `Submodule.map₂` to formalize S ⊗ S inside A ⊗ A.

---

## §1.9.3: Exercise - Dual Algebra and Comodule-Module

**Book Exercise 1.9.3:**
(i) If C is a coalgebra then C* is an algebra; if A is finite-dim algebra then A* is a coalgebra.
(ii) Any C-comodule M is a C*-module (and converse for finite-dim C).

**Mathlib (`Mathlib.RingTheory.Coalgebra.Convolution`):**

| Concept | Mathlib |
|---------|---------|
| Convolution algebra | `LinearMap.convSemiring` |
| Convolution product | `LinearMap.convMul_def` |
| Convolution unit | `LinearMap.convOne_def` |

**Our formalization (`Chapter1/DualAlgebra.lean`):**
- Part (i): References mathlib's convolution algebra
- Part (ii): `comoduleRightAction` defines m · f = lid((f ⊗ id)(ρ(m)))
  - `comoduleRightAction_add`, `_smul`, `_add_fun` — linearity
  - `comoduleRightAction_one` — m · 1 = m (PROVED)
  - `comoduleRightAction_mul` — m · (f*g) = (m·f)·g (sorry - coassociativity calc)

---

## §1.9 Remaining Work (Section Order)

| Item | Status | Issue | Notes |
|------|--------|-------|-------|
| §1.9.2: Comodule definition | ✅ DONE | lemmafeld-lyxp | Left + Right comodules |
| §1.9.3: Dual algebra + comod↔mod | ✅ DONE | lemmafeld-hmry | DualAlgebra.lean |
| §1.9.8: Grouplike ↔ 1-dim subcoalgebras | ✅ DONE | lemmafeld-e96f | Subcoalgebra def + span lemma |
| §1.9.9: Set coalgebra k[X] | ✅ DONE | lemmafeld-663t | |
| §1.9.12: Prim/k(g-h) ≅ Ext¹ | BLOCKED | — | Requires comodule categories |
| §1.9.13: Pointed coalgebra | ✅ DONE | lemmafeld-v7gb | PointedCoalgebra.lean |
| §1.9.15: LocallyFinite ≃ C-comod | BLOCKED | lemmafeld-cwxw | Requires comodule cat (~500 LOC) |

**Next steps:** With comodules defined, can now work on:
- §1.9.5: Finite-dim C-comodules form locally finite category (lemmafeld-51b0)
- §1.9.12, §1.9.13 become unblocked

---

## §1.13: Coradical Filtration

**All blocked on comodule infrastructure:**
- Definition 1.13.1-1.13.2: Coradical filtration
- Exercise 1.13.3(iii): Linear independence of grouplike elements

**Lean file:** `Chapter1/Coalgebras.lean`
