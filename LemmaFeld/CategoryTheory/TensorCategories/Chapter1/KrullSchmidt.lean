/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.FittingLemma

/-!
# Chapter 1, Theorem 1.5.7: Krull-Schmidt Theorem

This file documents the Krull-Schmidt theorem from Etingof et al. "Tensor Categories" §1.5.

## Book Statement

**Theorem 1.5.7 (Krull-Schmidt)**: Any object of finite length admits a unique (up to an
isomorphism) decomposition into a direct sum of indecomposable objects.

More precisely: if X has finite length and X ≅ ⨁ᵢ Yᵢ ≅ ⨁ⱼ Zⱼ where all Yᵢ, Zⱼ are
indecomposable, then the index sets have the same cardinality and there is a bijection
σ such that Yᵢ ≅ Z_{σ(i)}.

## Mathematical Context

The Krull-Schmidt theorem is a fundamental result for finite length objects in abelian
categories. It generalizes the decomposition of finite abelian groups as direct sums
of cyclic groups of prime power order.

**Ingredients:**
1. Indecomposable objects (Def 1.5.6): X is indecomposable if X ≅ Y ⊕ Z implies Y = 0 or Z = 0
2. Finite length (Def 1.5.3): X has a Jordan-Hölder series
3. Local endomorphism ring: For indecomposable X of finite length, End(X) is local

**Key lemma:** Fitting's Lemma (see `FittingLemma.lean`).

## Mathlib Status

### What Mathlib Has

| Concept | Mathlib | Import |
|---------|---------|--------|
| Indecomposable X | `Indecomposable X` | `Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts` |
| Simple ⟹ Indecomposable | `indecomposable_of_simple` | `Mathlib.CategoryTheory.Simple` |
| Finite biproducts | `HasFiniteBiproducts C` | `Mathlib.CategoryTheory.Limits.Shapes.Biproducts` |
| IsFiniteLength (modules) | `IsFiniteLength R M` | `Mathlib.RingTheory.FiniteLength` |

### What Mathlib Lacks (Gaps)

1. **Categorical Krull-Schmidt theorem**: No theorem stating existence and uniqueness of
   indecomposable decompositions for finite length objects in abelian categories
2. **Local endomorphism ring**: No proof that End(X) is local for indecomposable finite
   length objects

## References

- Etingof et al. "Tensor Categories" (AMS 2015), §1.5, Theorem 1.5.7
- Krause "Krull-Schmidt categories and projective covers" (Expo. Math. 2015)
- Bass "Algebraic K-theory" (1968), original proof

-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

/-! ## Definition 1.5.6: Indecomposable Objects (recap)

Mathlib's definition: `Indecomposable X := ¬IsZero X ∧ ∀ Y Z, X ≅ Y ⊞ Z → IsZero Y ∨ IsZero Z`
-/

section IndecomposableRecap

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

-- The definition is in mathlib
#check @Indecomposable

-- Indecomposable means: nonzero and any biproduct decomposition has a zero summand
example (X : C) : Indecomposable X ↔
    (¬IsZero X ∧ ∀ Y Z : C, (X ≅ Y ⊞ Z) → IsZero Y ∨ IsZero Z) := Iff.rfl

-- Simple objects are indecomposable
example [HasKernels C] (X : C) [Simple X] : Indecomposable X := indecomposable_of_simple X

end IndecomposableRecap

/-! ## Theorem 1.5.7: Krull-Schmidt (Statement)

**Existence**: Any object of finite length is isomorphic to a finite biproduct of
indecomposable objects.

**Uniqueness**: If X ≅ ⨁ᵢ Yᵢ ≅ ⨁ⱼ Zⱼ with all Yᵢ, Zⱼ indecomposable, then the
decompositions are equivalent up to permutation and isomorphism.

We state these as propositions. The proofs require significant development
(local rings, Fitting's lemma) that is beyond current mathlib coverage.
-/

section KrullSchmidtStatement

universe u v
variable (C : Type u) [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]

/-- An indecomposable decomposition of X is a finite family of indecomposable objects
whose biproduct is isomorphic to X. -/
structure IndecomposableDecomposition (X : C) where
  /-- Number of indecomposable summands -/
  n : ℕ
  /-- The family of indecomposable objects -/
  components : Fin n → C
  /-- Each component is indecomposable -/
  indecomposable : ∀ i, Indecomposable (components i)
  /-- The biproduct is isomorphic to X -/
  iso : X ≅ ⨁ components

/-- Two indecomposable decompositions are equivalent if they have the same length
and there is a permutation such that corresponding components are isomorphic. -/
def DecompositionsEquivalent {X : C}
    (d₁ d₂ : IndecomposableDecomposition C X) : Prop :=
  ∃ (h : d₁.n = d₂.n) (σ : Equiv.Perm (Fin d₁.n)),
    ∀ i, Nonempty (d₁.components i ≅ d₂.components ⟨σ i, h ▸ (σ i).isLt⟩)

/-- **Krull-Schmidt Existence** (Theorem 1.5.7, part 1):
Any object of finite length admits an indecomposable decomposition.

This is stated as a proposition; the proof requires showing that finite length objects
can be iteratively decomposed until all summands are indecomposable. -/
def KrullSchmidt_Existence : Prop :=
  ∀ X : C, IsFiniteLengthObject X → Nonempty (IndecomposableDecomposition C X)

/-- **Krull-Schmidt Uniqueness** (Theorem 1.5.7, part 2):
Any two indecomposable decompositions of the same object are equivalent.

This requires proving that End(Y) is local for indecomposable Y of finite length,
which uses Fitting's lemma. -/
def KrullSchmidt_Uniqueness : Prop :=
  ∀ X : C, ∀ d₁ d₂ : IndecomposableDecomposition C X, DecompositionsEquivalent C d₁ d₂

/-- The full Krull-Schmidt theorem: existence and uniqueness of indecomposable
decompositions for finite length objects. -/
def KrullSchmidt_Theorem : Prop :=
  KrullSchmidt_Existence C ∧ KrullSchmidt_Uniqueness C

end KrullSchmidtStatement

/-! ## Summary

**Theorem 1.5.7 (Krull-Schmidt)**: Any object of finite length admits a unique
decomposition into indecomposables.

**Structure:**
- `KrullSchmidt.lean` - Theorem statements and indecomposable recap
- `FittingLemma.lean` - Chain stabilization lemmas and Fitting's Lemma

**Mathlib status**: The definition of `Indecomposable` exists, but the theorem itself
(existence and uniqueness of decompositions) is not formalized.
-/

end LemmaFeld.TensorCategories.Chapter1
