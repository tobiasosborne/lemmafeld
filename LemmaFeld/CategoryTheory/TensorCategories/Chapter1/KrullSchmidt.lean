/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/

import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.Defs
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.Auxiliary
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.SubobjectBiprod
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.BiproductHelpers
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.Existence
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.LocalRing
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.Exchange
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.BiproductCancellation
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.UniquenessHelpers
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.Uniqueness

/-!
# Chapter 1, Theorem 1.5.7: Krull-Schmidt Theorem

This file re-exports the Krull-Schmidt theorem from its submodules.

## Book Statement

**Theorem 1.5.7 (Krull-Schmidt)**: Any object of finite length admits a unique (up to an
isomorphism) decomposition into a direct sum of indecomposable objects.

## Module Structure

- `KrullSchmidt/Defs.lean` — Core definitions (`IndecomposableDecomposition`, etc.)
- `KrullSchmidt/Auxiliary.lean` — Basic lemmas (finite length preservation)
- `KrullSchmidt/SubobjectBiprod.lean` — Subobject infrastructure for well-founded recursion
- `KrullSchmidt/BiproductHelpers.lean` — Biproduct concatenation lemmas
- `KrullSchmidt/Existence.lean` — Existence proof (`krullSchmidt_existence`)
- `KrullSchmidt/LocalRing.lean` — Local ring lemmas
- `KrullSchmidt/Exchange.lean` — Exchange lemma (`exchangeLemma`)
- `KrullSchmidt/BiproductCancellation.lean` — Head-tail split infrastructure
- `KrullSchmidt/UniquenessHelpers.lean` — Helper lemmas for uniqueness
- `KrullSchmidt/Uniqueness.lean` — Uniqueness proof (`krullSchmidt_uniqueness`)

## References

- Etingof et al. "Tensor Categories" (AMS 2015), §1.5, Theorem 1.5.7
- Krause "Krull-Schmidt categories and projective covers" (Expo. Math. 2015)
-/
