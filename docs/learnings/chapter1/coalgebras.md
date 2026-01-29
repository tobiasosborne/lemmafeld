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

## §1.13: Coradical Filtration

**Remaining work:**
- Proposition 1.9.12: Prim_{g,h}(C)/k(g-h) ≅ Ext¹(h,g) (requires comodule categories)
- Bijection: grouplike ↔ 1-dim subcoalgebras
- Definition 1.13.1-1.13.2: Coradical filtration
- Exercise 1.13.3(iii): Linear independence of grouplike elements

**Lean file:** `Chapter1/Coalgebras.lean`
