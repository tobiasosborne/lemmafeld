/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import Mathlib.Data.Fin.Basic

/-!
# The Domain Omega

This file defines the domain Ω(n,k,m) = Fin(6 + n + k + m) on which our
permutation group acts.

## Main Definitions

* `Omega n k m` - The type `Fin (6 + n + k + m)`
* `isCore` - Predicate for core points {0,1,2,3,4,5} (= {1,...,6} in 1-indexed)
* `isTailA`, `isTailB`, `isTailC` - Predicates for tail points

## Index Convention

AF proofs use 1-indexed elements. Lean's `Fin n` is 0-indexed.
- AF element k → Lean `Fin.mk (k-1)`
- Core elements {1,2,3,4,5,6} in AF → {0,1,2,3,4,5} in Lean
-/

/-- The domain Ω for parameters n, k, m is Fin (6 + n + k + m) -/
abbrev Omega (n k m : ℕ) := Fin (6 + n + k + m)

/-- The size of Ω -/
def Omega.card (n k m : ℕ) : ℕ := 6 + n + k + m

/-- Core points are {0,1,2,3,4,5} (representing {1,2,3,4,5,6} in 1-indexed) -/
def isCore {n k m : ℕ} (x : Omega n k m) : Prop := x.val < 6

/-- Tail A points are {6, ..., 6+n-1} (representing a₁, ..., aₙ) -/
def isTailA {n k m : ℕ} (x : Omega n k m) : Prop := 6 ≤ x.val ∧ x.val < 6 + n

/-- Tail B points are {6+n, ..., 6+n+k-1} (representing b₁, ..., bₖ) -/
def isTailB {n k m : ℕ} (x : Omega n k m) : Prop := 6 + n ≤ x.val ∧ x.val < 6 + n + k

/-- Tail C points are {6+n+k, ..., 6+n+k+m-1} (representing c₁, ..., cₘ) -/
def isTailC {n k m : ℕ} (x : Omega n k m) : Prop :=
  6 + n + k ≤ x.val ∧ x.val < 6 + n + k + m

/-- Every point is either in core or one of the tails -/
theorem Omega.partition {n k m : ℕ} (x : Omega n k m) :
    isCore x ∨ isTailA x ∨ isTailB x ∨ isTailC x := by
  simp only [isCore, isTailA, isTailB, isTailC]
  omega

/-- The size of Omega is at least 6 -/
theorem Omega.card_ge_six (n k m : ℕ) : Omega.card n k m ≥ 6 := by
  unfold Omega.card
  omega

/-! ## Decidability -/

instance : DecidablePred (@isCore n k m) := fun x =>
  decidable_of_iff (x.val < 6) Iff.rfl

instance : DecidablePred (@isTailA n k m) := fun x =>
  decidable_of_iff (6 ≤ x.val ∧ x.val < 6 + n) Iff.rfl

instance : DecidablePred (@isTailB n k m) := fun x =>
  decidable_of_iff (6 + n ≤ x.val ∧ x.val < 6 + n + k) Iff.rfl

instance : DecidablePred (@isTailC n k m) := fun x =>
  decidable_of_iff (6 + n + k ≤ x.val ∧ x.val < 6 + n + k + m) Iff.rfl

/-! ## Exclusivity -/

/-- Core and TailA are disjoint -/
theorem isCore_not_isTailA {n k m : ℕ} {x : Omega n k m} (h : isCore x) : ¬isTailA x := by
  simp only [isCore, isTailA] at *; omega

/-- Core and TailB are disjoint -/
theorem isCore_not_isTailB {n k m : ℕ} {x : Omega n k m} (h : isCore x) : ¬isTailB x := by
  simp only [isCore, isTailB] at *; omega

/-- Core and TailC are disjoint -/
theorem isCore_not_isTailC {n k m : ℕ} {x : Omega n k m} (h : isCore x) : ¬isTailC x := by
  simp only [isCore, isTailC] at *; omega

/-! ## Core element constructors -/

/-- Core element 0 (AF element 1) -/
def Omega.core0 (n k m : ℕ) : Omega n k m := ⟨0, by omega⟩

/-- Core element 1 (AF element 2) -/
def Omega.core1 (n k m : ℕ) : Omega n k m := ⟨1, by omega⟩

/-- Core element 2 (AF element 3) -/
def Omega.core2 (n k m : ℕ) : Omega n k m := ⟨2, by omega⟩

/-- Core element 3 (AF element 4) -/
def Omega.core3 (n k m : ℕ) : Omega n k m := ⟨3, by omega⟩

/-- Core element 4 (AF element 5) -/
def Omega.core4 (n k m : ℕ) : Omega n k m := ⟨4, by omega⟩

/-- Core element 5 (AF element 6) -/
def Omega.core5 (n k m : ℕ) : Omega n k m := ⟨5, by omega⟩
