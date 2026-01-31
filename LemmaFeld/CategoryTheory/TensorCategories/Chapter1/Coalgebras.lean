/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Chapter 1, Section 1.9: Coalgebras — Grouplike and Skew-Primitive Elements

This file establishes grouplike and skew-primitive elements for coalgebras,
following Etingof et al. "Tensor Categories" §1.9.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.9

## Main Definitions

* `IsGrouplike`: A nonzero element x is grouplike if Δ(x) = x ⊗ x (Definition 1.9.7)
* `IsSkewPrimitive`: x is (g,h)-skew-primitive if Δ(x) = g⊗x + x⊗h (Def 1.9.10)

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Coalgebra | `Coalgebra R A` | `Mathlib.RingTheory.Coalgebra.Basic` |
| Comultiplication Δ | `Coalgebra.comul` | Linear map A →ₗ[R] A ⊗[R] A |
| Counit ε | `Coalgebra.counit` | Linear map A →ₗ[R] R |
| Grouplike | `IsGrouplike` | NEW: defined below |
| Skew-primitive | `IsSkewPrimitive` | NEW: defined below |

-/

namespace LemmaFeld.TensorCategories.Chapter1

open scoped TensorProduct

variable {R : Type*} [CommSemiring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [Coalgebra R A]

/-! ## §1.9 Definition 1.9.7: Grouplike Elements

Book: "Let C be a coalgebra. A nonzero element x ∈ C is called grouplike if Δ(x) = x ⊗ x."

Note: The book requires nonzero; we separate this into the predicate `IsGrouplike`
(the comultiplication condition) and require nonzero when needed.
-/

/-- An element x of a coalgebra is grouplike if Δ(x) = x ⊗ x and ε(x) = 1.

Book Definition 1.9.7 only states Δ(x) = x ⊗ x, but the counit condition ε(x) = 1
follows from the coalgebra axioms when x ≠ 0. We include it for completeness.
-/
structure IsGrouplike (R : Type*) [CommSemiring R] {A : Type*} [AddCommMonoid A]
    [Module R A] [Coalgebra R A] (x : A) : Prop where
  /-- Comultiplication condition: Δ(x) = x ⊗ x -/
  comul_eq : Coalgebra.comul x = x ⊗ₜ[R] x
  /-- Counit condition: ε(x) = 1 -/
  counit_eq : Coalgebra.counit x = (1 : R)

/-! ## §1.9 Remark 1.9.8: One-Dimensional Subcoalgebras

Book: "There is a bijection between grouplike elements of a coalgebra C and its
one-dimensional subcoalgebras, given by x ↦ k·x."

A subcoalgebra is a submodule S such that Δ(S) ⊆ S ⊗ S.
-/

/-- A submodule S is a subcoalgebra if comultiplication maps S into S ⊗ S.

Book Remark 1.9.8: One-dimensional subcoalgebras correspond to grouplike elements.
The condition Δ(S) ⊆ S ⊗ S is formalized using `Submodule.map₂`. -/
def IsSubcoalgebra (R : Type*) [CommSemiring R] {A : Type*} [AddCommMonoid A]
    [Module R A] [Coalgebra R A] (S : Submodule R A) : Prop :=
  ∀ s ∈ S, Coalgebra.comul s ∈ Submodule.map₂ (TensorProduct.mk R A A) S S

/-- The span of a grouplike element is a subcoalgebra.

Book Remark 1.9.8: x ↦ k·x gives a map from grouplike elements to 1-dim subcoalgebras. -/
lemma IsGrouplike.span_isSubcoalgebra {R : Type*} [CommSemiring R] {A : Type*}
    [AddCommMonoid A] [Module R A] [Coalgebra R A] {x : A} (hx : IsGrouplike R x) :
    IsSubcoalgebra R (Submodule.span R {x}) := by
  intro s hs
  rw [Submodule.mem_span_singleton] at hs
  obtain ⟨r, rfl⟩ := hs
  simp only [LinearMap.map_smul, hx.comul_eq, TensorProduct.smul_tmul']
  exact Submodule.apply_mem_map₂ _
    (Submodule.mem_span_singleton.mpr ⟨r, rfl⟩)
    (Submodule.mem_span_singleton.mpr ⟨1, one_smul R x⟩)

/-! ## §1.9 Example 1.9.9: Set Coalgebra

Book: "Let X be a set. Then k[X], the set of formal linear combinations of elements of X,
is a coalgebra, with Δ(x) = x ⊗ x for x ∈ X. The grouplike elements of k[X] are
precisely elements x ∈ X."

Mathlib: `MonoidAlgebra R X` (denoted `R[X]`) inherits a coalgebra structure from
`Finsupp.instCoalgebra`. The base ring `R` is a coalgebra over itself with
`comul r = 1 ⊗ r`, so `R[X]` gets `comul (single x r) = single x 1 ⊗ single x 1 · comul r`.
-/

section SetCoalgebra

noncomputable section

variable (R : Type*) [CommSemiring R] (X : Type*)

/-- The set coalgebra k[X] is a coalgebra via the MonoidAlgebra instance.

Book Example 1.9.9: For a set X, the free R-module R[X] = MonoidAlgebra R X
is a coalgebra with Δ(x) = x ⊗ x for x ∈ X.

Mathlib provides this via `MonoidAlgebra.instCoalgebra`, which comes from
`Finsupp.instCoalgebra` using the base coalgebra structure on R. -/
example : Coalgebra R (MonoidAlgebra R X) := inferInstance

/-- Each basis element of the set coalgebra is grouplike.

Book Example 1.9.9: "The grouplike elements of k[X] are precisely elements x ∈ X."
Here we prove one direction: every x ∈ X gives a grouplike element. -/
lemma isGrouplike_single_one (x : X) :
    IsGrouplike R (MonoidAlgebra.single x (1 : R)) where
  comul_eq := by
    simp only [MonoidAlgebra.comul_single, CommSemiring.comul_apply]
    simp only [TensorProduct.map_tmul, MonoidAlgebra.lsingle_apply]
  counit_eq := by
    simp only [MonoidAlgebra.counit_single, CommSemiring.counit_apply]

end

end SetCoalgebra

/-! ## §1.9 Definition 1.9.10: Skew-Primitive Elements

Book: "Let C be a coalgebra and let g, h be grouplike elements in C. An element x ∈ C
is called skew-primitive (or (g, h)-skew-primitive) if Δ(x) = g ⊗ x + x ⊗ h."
-/

/-- An element x is (g, h)-skew-primitive if Δ(x) = g ⊗ x + x ⊗ h.

Book Definition 1.9.10: For grouplike elements g, h, an element x is (g,h)-skew-primitive
if its comultiplication satisfies Δ(x) = g ⊗ x + x ⊗ h.

When g = h = 1 (the unit), this gives primitive elements: Δ(x) = 1 ⊗ x + x ⊗ 1.
-/
def IsSkewPrimitive (R : Type*) [CommSemiring R] {A : Type*} [AddCommMonoid A]
    [Module R A] [Coalgebra R A] (g h x : A) : Prop :=
  Coalgebra.comul x = g ⊗ₜ[R] x + x ⊗ₜ[R] h

/-! ## §1.9 Remark 1.9.11: Trivial Skew-Primitives

Book: "Let g, h be grouplike elements of a coalgebra C. A multiple of g − h is always
a (g, h)-skew-primitive element. Such a skew-primitive element is called trivial."
-/

/-- A multiple of g - h is a trivial (g, h)-skew-primitive element.

Book Remark 1.9.11: When g and h are grouplike, any element of the form r • (g - h)
for r : R is (g, h)-skew-primitive. Such elements are called trivial. -/
def IsTrivialSkewPrimitive (R : Type*) [CommSemiring R] {A : Type*} [AddCommGroup A]
    [Module R A] [Coalgebra R A] (g h x : A) : Prop :=
  ∃ r : R, x = r • (g - h)

section Properties

variable {R : Type*} [CommSemiring R]
variable {A : Type*} [AddCommMonoid A] [Module R A] [Coalgebra R A]
variable (x : A)

/-- Zero is not grouplike (implicit from book's "nonzero" requirement). -/
lemma not_isGrouplike_zero [Nontrivial R] : ¬IsGrouplike R (0 : A) := by
  intro ⟨_, hcounit⟩
  simp only [map_zero] at hcounit
  exact one_ne_zero hcounit.symm

/-- The counit of a grouplike element is 1. -/
lemma IsGrouplike.counit_eq_one (h : IsGrouplike R x) : Coalgebra.counit x = (1 : R) :=
  h.counit_eq

/-- The comultiplication of a grouplike element is x ⊗ x. -/
lemma IsGrouplike.comul_eq_tmul (h : IsGrouplike R x) :
    Coalgebra.comul x = x ⊗ₜ[R] x :=
  h.comul_eq

end Properties

/-! ## §1.9 Proposition 1.9.12: Skew-Primitives and Ext¹

Book: "Let g and h be grouplike elements of a coalgebra C. The space
Prim_{g,h}(C)/k(g − h) is naturally isomorphic to Ext¹(h, g), where g, h are
regarded as 1-dimensional right C-comodules."

This deep result connects skew-primitive elements to extension theory.
Full formalization would require comodule categories and Ext functors.
-/

end LemmaFeld.TensorCategories.Chapter1
