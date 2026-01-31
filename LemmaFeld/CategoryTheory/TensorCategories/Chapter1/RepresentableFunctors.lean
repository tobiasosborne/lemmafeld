/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Chapter 1, §1.8.8-1.8.10: Representable Functors

This file documents the correspondence between Etingof et al. "Tensor Categories"
§1.8.8-1.8.10 on representable functors and mathlib's infrastructure.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.8

## Key Results

- **Definition 1.8.8**: A functor F: A-mod → B-mod is (⊗-)representable if F ≅ V ⊗_A -
  for some (B,A)-bimodule V.

- **Remark 1.8.9**: F: A-mod → k-Vec is representable iff it has a right adjoint.

- **Proposition 1.8.10**: F: A-mod → B-mod is representable iff it is right exact.
  This is essentially the Eilenberg-Watts theorem for finite dimensional algebras.

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| A-mod | `ModuleCat A` | Category of left A-modules |
| (B,A)-bimodule | `Module B (Module A V)` | Two-sided module structure |
| V ⊗_A - functor | `TensorProduct.Functor` | Module tensor product functor |
| Right exact functor | `Functor.RightExact F` | Preserves cokernels |

## Current Status

The full Eilenberg-Watts theorem requires significant infrastructure:
1. Defining the tensor functor V ⊗_A - as a functor on ModuleCat
2. Proving the natural isomorphism F ≅ F(A) ⊗_A - when F is right exact
3. Handling the bimodule structure on F(A)

This file documents the book definitions. Full formalization is tracked separately.
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

/-! ## §1.8.8: Tensor-Representable Functors

Book Definition 1.8.8: "An additive k-linear functor F: A-mod → B-mod is
(⊗-)representable if there exists a (B,A)-bimodule V such that F is naturally
isomorphic to (V ⊗_A -)."
-/

section RepresentableFunctors

variable (k : Type*) [Field k]
variable (A B : Type*) [Ring A] [Ring B] [Algebra k A] [Algebra k B]

/-- A functor F: A-mod → B-mod is tensor-representable if it is naturally
isomorphic to V ⊗_A - for some (B,A)-bimodule V.

Book: Definition 1.8.8

Note: Full formalization requires setting up the tensor functor V ⊗_A - as a
functor between module categories. This is tracked in a separate issue. -/
structure IsTensorRepresentable (F : ModuleCat.{0} A ⥤ ModuleCat.{0} B) : Prop where
  /-- The representing bimodule V -/
  witness_exists : ∃ (V : Type*), Nonempty V  -- Placeholder for actual bimodule

/-! ## §1.8.10: Characterization via Right Exactness

Book Proposition 1.8.10: "An additive k-linear functor F: A-mod → B-mod is
representable if and only if it is right exact."

Proof outline:
- (⇒) The tensor product functor V ⊗_A - is right exact.
- (⇐) If F is right exact, let V = F(A). Then V has a (B,A)-bimodule structure,
      and F(X) ≅ V ⊗_A X naturally in X.
-/

/-- The "only if" direction: tensor product functors are right exact.

This follows from the general fact that tensor products preserve cokernels.
Mathlib: `TensorProduct.Algebra.rightExact` and related results. -/
lemma tensorProduct_rightExact {V : Type*} [AddCommGroup V] [Module A V] :
    True := -- Placeholder: full statement needs tensor functor setup
  trivial

/-
The "if" direction is the substantive content of Eilenberg-Watts:
a right exact functor on module categories is represented by tensoring.

This requires showing F(X) ≅ F(A) ⊗_A X naturally.

Book: "Let V = F(A). Then V is a B-module which has a commuting right action of A"

Full formalization is tracked in a separate issue.
-/

end RepresentableFunctors

/-! ## §1.8.11: Corollary for Left Exact Functors

Book Corollary 1.8.11: "Let C be a finite abelian k-linear category, and let
F: C → Vec be an additive k-linear left exact functor. Then F = Hom_C(V, -)
for some object V ∈ C."

This is the dual of 1.8.10, using that left exact functors on C correspond to
right exact functors on C^op, and the Yoneda embedding.
-/

end LemmaFeld.TensorCategories.Chapter1
