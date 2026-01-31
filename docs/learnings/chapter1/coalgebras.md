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

## §1.9 Remaining Work (Section Order)

| Item | Status | Issue | Notes |
|------|--------|-------|-------|
| §1.9.8: Grouplike ↔ 1-dim subcoalgebras | TODO | lemmafeld-e96f | Needs subcoalgebra def |
| §1.9.9: Set coalgebra k[X] | ✅ DONE | lemmafeld-663t | |
| §1.9.12: Prim/k(g-h) ≅ Ext¹ | BLOCKED | — | Requires comodule categories |
| §1.9.13: Pointed coalgebra | BLOCKED | — | Requires "simple comodule" |
| §1.9.15: LocallyFinite ≃ C-comod | BLOCKED | lemmafeld-cwxw | Requires comodule cat (~500 LOC) |

**Recommendation:** Work on §1.9.8 next — requires subcoalgebra definition.

---

## §1.13: Coradical Filtration

**All blocked on comodule infrastructure:**
- Definition 1.13.1-1.13.2: Coradical filtration
- Exercise 1.13.3(iii): Linear independence of grouplike elements

**Lean file:** `Chapter1/Coalgebras.lean`
