/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Logic.Relation

/-!
# Chapter 1, Exercise 1.5.10: Block Decomposition

This file formalizes Exercise 1.5.10 from Etingof et al. "Tensor Categories" §1.5.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.5

## Exercise 1.5.10 Summary

(i) Let C be an abelian category where objects have finite length. Show that C admits
    a unique decomposition C = ⊕_{α ∈ I} C_α such that C_α are indecomposable.
    (The categories C_α are called the *blocks* of C.)

(ii) Show that C is indecomposable if and only if any two simple objects X, Y of C
     are *linked*, i.e., there exists a chain X = X_0, X_1, ..., X_n = Y of simple
     objects of C such that Ext¹(X_i, X_{i+1}) ≠ 0 or Ext¹(X_{i+1}, X_i) ≠ 0 for all i.

(iii) Let A be a finite dimensional algebra over an algebraically closed field k,
      and let C be the category of finite dimensional A-modules. Show that blocks
      of C are labeled by characters of the center of A.

## This File

We formalize Part (ii) by:
1. Defining `DirectlyLinked X Y` for simple objects: Ext¹(X,Y) ≠ 0 or Ext¹(Y,X) ≠ 0
2. Defining `Linked X Y` as the reflexive-transitive closure of DirectlyLinked
3. Showing `Linked` is an equivalence relation on simple objects

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Simple object | `Simple X` | `Mathlib.CategoryTheory.Simple` |
| Ext¹(X, Y) | `Abelian.Ext X Y 1` | `Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic` |
| Refl-trans closure | `Relation.ReflTransGen` | `Mathlib.Logic.Relation` |
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

/-! ## §1.5.10 Part (ii): Linked Simple Objects

Book: "Two simple objects X, Y are linked if there exists a chain
X = X_0, X_1, ..., X_n = Y of simple objects such that
Ext¹(X_i, X_{i+1}) ≠ 0 or Ext¹(X_{i+1}, X_i) ≠ 0 for all i."
-/

section LinkedSimpleObjects

variable {C : Type*} [Category C] [Abelian C] [HasExt C]

/-- Two objects are directly linked if Ext¹ is nonzero in either direction.

Book: "Ext¹(X_i, X_{i+1}) ≠ 0 or Ext¹(X_{i+1}, X_i) ≠ 0"

Note: We define this for all objects, not just simple ones, for generality.
The book's definition restricts to simple objects. -/
def DirectlyLinked (X Y : C) : Prop :=
  ¬IsEmpty (Abelian.Ext X Y 1) ∨ ¬IsEmpty (Abelian.Ext Y X 1)

/-- DirectlyLinked is symmetric by definition. -/
lemma directlyLinked_symm {X Y : C} : DirectlyLinked X Y ↔ DirectlyLinked Y X := by
  unfold DirectlyLinked
  exact Or.comm

/-- Two objects are linked if they are connected by a chain of directly linked objects.

Book: "there exists a chain X = X_0, X_1, ..., X_n = Y"

This is the reflexive-transitive closure of DirectlyLinked. -/
def Linked (X Y : C) : Prop :=
  Relation.ReflTransGen (fun A B => DirectlyLinked A B) X Y

/-- Linked is reflexive. -/
lemma linked_refl (X : C) : Linked X X :=
  Relation.ReflTransGen.refl

/-- Linked is transitive. -/
lemma linked_trans {X Y Z : C} (hXY : Linked X Y) (hYZ : Linked Y Z) : Linked X Z :=
  Relation.ReflTransGen.trans hXY hYZ

/-- Linked is symmetric (since DirectlyLinked is symmetric). -/
lemma linked_symm {X Y : C} (h : Linked X Y) : Linked Y X := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih =>
    apply Relation.ReflTransGen.trans
    · exact Relation.ReflTransGen.single (directlyLinked_symm.mp hab)
    · exact ih

/-- Linked defines an equivalence relation on objects.

This is the equivalence relation whose equivalence classes correspond to blocks. -/
lemma linked_equivalence : Equivalence (Linked (C := C)) :=
  ⟨linked_refl, linked_symm, linked_trans⟩

/-- The setoid of linked objects. -/
def linkedSetoid (C : Type*) [Category C] [Abelian C] [HasExt C] : Setoid C :=
  ⟨Linked, linked_equivalence⟩

/-- If X and Y are directly linked, they are linked. -/
lemma directlyLinked_imp_linked {X Y : C} (h : DirectlyLinked X Y) : Linked X Y :=
  Relation.ReflTransGen.single h

end LinkedSimpleObjects

/-! ## Characterization via Simple Objects

The book restricts the linking relation to simple objects. We define a version
that requires all objects in the chain to be simple. -/

section LinkedSimple

variable {C : Type*} [Category C] [Abelian C] [HasExt C]

/-- Two simple objects are directly linked if Ext¹ is nonzero in either direction. -/
def DirectlyLinkedSimple (X Y : C) [Simple X] [Simple Y] : Prop :=
  DirectlyLinked X Y

-- Two simple objects X, Y are linked (via simples) if there exists a chain
-- of simple objects connecting them with nonzero Ext¹.
-- Note: This is harder to state in Lean since we need to track the Simple instances
-- for each intermediate object. The general `Linked` relation is often more convenient.

end LinkedSimple

/-! ## Block Decomposition (Sketch)

Part (i) of Exercise 1.5.10 states that C = ⊕ C_α where C_α are indecomposable blocks.

A full formalization would require:
1. Definition of "direct sum of categories" (not in mathlib for abelian categories)
2. Definition of "indecomposable category" (cannot be written as nontrivial direct sum)
3. Proof that the linked equivalence classes give the block decomposition

For now, we record the key definitions and leave full formalization as future work.
-/

/-! ## Notes on Part (iii)

Part (iii) states that for A-mod (finite dimensional A-modules), blocks are labeled
by characters of Z(A) (center of A).

This requires:
- `Algebra.center A` — the center of an algebra
- Characters χ : Z(A) → k
- The correspondence: block C_χ = {M : M ⊗_Z(A) k_χ ≠ 0}

This is more specific to module categories and would build on the general theory. -/

end LemmaFeld.TensorCategories.Chapter1
