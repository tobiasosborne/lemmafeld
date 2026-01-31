# Chapter 1: Locally Finite and Finite Abelian Categories (§1.8)

## §1.8.1: Locally Finite Abelian Category

**Lean file:** `Chapter1/LocallyFinite.lean`

**Book Definition 1.8.1:** A k-linear abelian category C is locally finite if:
- (i) Hom_C(X, Y) is finite dimensional for all X, Y
- (ii) Every object has finite length

**Mathlib:**
- Finite length = `IsArtinianObject X ∧ IsNoetherianObject X`
- Finite dimensional Hom = `Module.Finite k (X ⟶ Y)`

**Our definition:** `IsLocallyFinite k C` class with both conditions.

---

## §1.8.2: Artinian Categories

**Remark 1.8.2:** Locally finite = artinian categories.

**Our formalization:** `IsArtinianCategory k C` is an alias for `IsLocallyFinite k C`.

---

## §1.8.3: Injective and Surjective Functors

**Book Definition 1.8.3:**
- Injective = fully faithful (bijective on Hom sets)
- Surjective = every simple in target is subquotient of some F(X)

**Our formalization:**
- `Functor.IsInjective F := Nonempty F.FullyFaithful`
- `Functor.IsSurjective F` = simples in D iso to simple subobjects of F(X)

**Gap:** Full subquotient notion not formalized.

---

## §1.8.4: Schur's Lemma for Locally Finite Categories

**Book Proposition 1.8.4:** For k algebraically closed:
- Hom(X, Y) = 0 if X, Y simple and X ≇ Y
- Hom(X, X) = k for simple X

**Mathlib:** `isIso_of_hom_simple` and `finrank_endomorphism_simple_eq_one` in `CategoryTheory.Preadditive.Schur`

**Our formalization:**
- `hom_simple_eq_zero_of_not_iso` — proved
- `end_simple_eq_one_dim` — proved via `CategoryTheory.finrank_endomorphism_simple_eq_one`

---

## §1.8.5/1.8.6: Finite Abelian Categories

**Book Definition 1.8.5:** C is finite if equivalent to A-mod for fin dim algebra A.

**Book Definition 1.8.6 (intrinsic):**
- (i) Finite dim Hom spaces
- (ii) Finite length objects
- (iii) Enough projectives
- (iv) Finitely many simple iso classes

**Our formalization:**
- `SimpleClasses C` — quotient of simple objects by isomorphism
- `IsFiniteAbelian k C` — LocallyFinite + `[EnoughProjectives C]` + `Finite (SimpleClasses C)`

---

## §1.8.8-1.8.10: Representable Functors

**Lean file:** `Chapter1/RepresentableFunctors.lean`

**Book Definition 1.8.8:** F: A-mod → B-mod is (⊗-)representable if F ≅ V ⊗_A - for some (B,A)-bimodule V.

**Book Proposition 1.8.10:** F is representable iff F is right exact (Eilenberg-Watts theorem).

**Mathlib correspondence:**
- `ModuleCat A` — category of left A-modules
- `TensorProduct` — tensor product of modules

**Status:** Documentation file created. Full Eilenberg-Watts proof requires:
1. Tensor functor V ⊗_A - as functor on ModuleCat
2. Bimodule structure on F(A)
3. Natural isomorphism F(X) ≅ F(A) ⊗_A X

---

## Gaps Identified

| Gap | Description | Issue |
|-----|-------------|-------|
| ~~Division algebra~~ | ~~fin dim over alg closed k = k~~ | **RESOLVED** via mathlib |
| Subquotients | Proper subquotient formalization | lemmafeld-qr9k |
| Duality | Finite category duality C ↔ A^op-mod | lemmafeld-z5db |
| Eilenberg-Watts | Full proof of Prop 1.8.10 | Future work |

**Resolved 2026-01-29:** Division algebra classification is handled by mathlib's
`CategoryTheory.finrank_endomorphism_simple_eq_one` which proves finrank = 1 directly
without explicitly constructing the algebra isomorphism. The proof uses that End(X)
is a finite-dimensional division algebra over an algebraically closed field.
