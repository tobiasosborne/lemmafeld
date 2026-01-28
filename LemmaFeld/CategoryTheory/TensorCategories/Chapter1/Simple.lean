/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Chapter 1, Section 1.5: Simple Objects and Length

This file establishes the correspondence between Etingof et al. "Tensor Categories"
§1.5 and mathlib's simple object infrastructure.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.5

## §1.5 Summary

The book defines:
- **Definition 1.5.1**: Simple object (only subobjects are 0 and X)
- **Definition 1.5.1**: Semisimple object/category
- **Lemma 1.5.2**: Schur's Lemma
- **Definition 1.5.3**: Finite length, Jordan-Hölder series
- **Theorem 1.5.4**: Jordan-Hölder theorem
- **Definition 1.5.5**: Length of an object
- **Definition 1.5.6**: Indecomposable object
- **Theorem 1.5.7**: Krull-Schmidt theorem
- **Definition 1.5.8**: Grothendieck group Gr(C)

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Simple object | `Simple X` | `Mathlib.CategoryTheory.Simple` |
| Semisimple object | — | Not in mathlib for general categories |
| Schur's Lemma | `isIso_of_hom_simple` | `Mathlib.CategoryTheory.Preadditive.Schur` |
| Indecomposable | `Indecomposable X` | `Mathlib.CategoryTheory.Simple` |
| Jordan-Hölder | — | Not in mathlib |
| Krull-Schmidt | — | Not in mathlib |
| Grothendieck group | `K₀` (for rings) | Different approach |

-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

/-! ## §1.5 Definition 1.5.1: Simple Objects

Book: "A nonzero object X in C is called simple if 0 and X are its only subobjects."

Mathlib: `Simple X` in `Mathlib.CategoryTheory.Simple`
-/

section SimpleObjects

variable {C : Type*} [Category C] [HasZeroMorphisms C]

-- Book: "A nonzero object X is simple if 0 and X are its only subobjects"
-- Mathlib formulation: a mono into X is either zero or an isomorphism
-- class Simple (X : C) : Prop where
--   mono_isIso_iff_nonzero : ∀ {Y : C} (f : Y ⟶ X) [Mono f], IsIso f ↔ f ≠ 0

-- Simple objects are nonzero
example (X : C) [Simple X] : ¬IsZero X := Simple.not_isZero X

-- Simple is preserved by isomorphism
example {X Y : C} [Simple Y] (i : X ≅ Y) : Simple X := Simple.of_iso i

end SimpleObjects

/-! ## §1.5 Definition 1.5.1: Subobject Characterization

In a category with zero object, `Simple X` is equivalent to
`Subobject X` having exactly two elements: 0 and X.
-/

section SubobjectCharacterization

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]

-- For simple X, Subobject X has exactly two elements (simple order)
example {X : C} [Simple X] : IsSimpleOrder (Subobject X) := inferInstance

-- Conversely, if Subobject X is a simple order, X is simple
example (X : C) [IsSimpleOrder (Subobject X)] : Simple X :=
  simple_of_isSimpleOrder_subobject X

end SubobjectCharacterization

/-! ## §1.5 Definition 1.5.1: Semisimple Objects

Book: "An object X in C is called semisimple if it is a direct sum of simple objects,
and C is called semisimple if every object of C is semisimple."

**Gap:** Mathlib does not have `Semisimple X` for objects in general abelian categories.
It has `IsSemisimpleModule` for modules, but not the categorical generalization.
-/

/-! ## §1.5 Lemma 1.5.2: Schur's Lemma

Book: "Let X, Y be two simple objects in C. Then any nonzero morphism f : X → Y
is an isomorphism. In particular, if X is not isomorphic to Y then Hom(X, Y) = 0,
and Hom(X, X) is a division algebra."

Mathlib: `Mathlib.CategoryTheory.Preadditive.Schur`
-/

section SchursLemma

variable {C : Type*} [Category C] [Preadditive C] [HasKernels C]

-- Core Schur's lemma: nonzero morphism between simple objects is an iso
example {X Y : C} [Simple X] [Simple Y] {f : X ⟶ Y} (w : f ≠ 0) : IsIso f :=
  isIso_of_hom_simple w

-- Equivalently: morphism is iso iff nonzero
example {X Y : C} [Simple X] [Simple Y] (f : X ⟶ Y) : IsIso f ↔ f ≠ 0 :=
  isIso_iff_nonzero f

-- If X ≇ Y then Hom(X, Y) = 0 (finite-dimensional case)
-- In k-linear categories with finite-dimensional hom spaces:
-- finrank_hom_simple_simple_eq_zero_of_not_iso

-- End(X) is a division algebra (dim = 1 in finite case)
-- finrank_endomorphism_simple_eq_one

end SchursLemma

/-! ## §1.5 Definition 1.5.6: Indecomposable Objects

Book: "An indecomposable object X ∈ C is an object which does not admit a
non-trivial decomposition into a direct sum of its subobjects."

Mathlib: `Indecomposable X` in `Mathlib.CategoryTheory.Simple`
-/

section Indecomposable

variable {C : Type*} [Category C] [Abelian C]

-- Simple implies indecomposable
example (X : C) [Simple X] : Indecomposable X := indecomposable_of_simple X

end Indecomposable

/-! ## §1.5 Gaps: Jordan-Hölder, Krull-Schmidt, Grothendieck Group

**Jordan-Hölder theorem (Theorem 1.5.4):**
Not in mathlib for general abelian categories. Would require:
- Definition of composition series / Jordan-Hölder series
- Proof that multiplicities are independent of series choice

**Krull-Schmidt theorem (Theorem 1.5.7):**
Not in mathlib for general abelian categories. Related work exists for
specific algebraic structures.

**Grothendieck group (Definition 1.5.8):**
Mathlib has `K₀` for rings via `AlgebraicKTheory.K₀`. The categorical
Grothendieck group (free abelian group on simple isomorphism classes
with [Y] = [X] + [Z] for short exact sequences) is not directly formalized.
-/

end LemmaFeld.TensorCategories.Chapter1
