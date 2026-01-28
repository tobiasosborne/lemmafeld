/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_2
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Lemma 11.4: Block Orbit - Definitions

Basic definitions for block system invariance and block orbits.

## Main Definitions

* `BlockSystemInvariant`: A block system is σ-invariant if σ permutes the blocks
* `blockOrbit`: The orbit of a block under ⟨σ⟩
* `blockOrbitSize`: Number of distinct blocks in an orbit
* `cycleLength`: The support size of a permutation
-/

open Equiv Equiv.Perm Set MulAction
open scoped Pointwise

variable {α : Type*} [DecidableEq α] [Fintype α]

-- ============================================
-- BLOCK SYSTEM INVARIANCE
-- ============================================

/-- A block system (as a set of sets) is σ-invariant if σ permutes the blocks -/
def BlockSystemInvariant (σ : Perm α) (B : Set (Set α)) : Prop :=
  ∀ b ∈ B, σ '' b ∈ B

/-- σ induces a permutation on an invariant block system -/
theorem induced_block_perm {σ : Perm α} {B : Set (Set α)} (hInv : BlockSystemInvariant σ B) :
    ∀ b ∈ B, σ '' b ∈ B := hInv

-- ============================================
-- ORBIT OF A BLOCK
-- ============================================

/-- The orbit of a block B under ⟨σ⟩ acting on blocks -/
def blockOrbit (σ : Perm α) (B : Set α) : Set (Set α) :=
  { C | ∃ k : ℤ, C = (σ ^ k) '' B }

/-- The orbit size (number of distinct blocks in the orbit) -/
noncomputable def blockOrbitSize (σ : Perm α) (B : Set α) : ℕ :=
  (blockOrbit σ B).ncard

/-- Orbit is closed under σ -/
theorem blockOrbit_closed {σ : Perm α} {B : Set α} {C : Set α}
    (hC : C ∈ blockOrbit σ B) : σ '' C ∈ blockOrbit σ B := by
  obtain ⟨k, rfl⟩ := hC
  use k + 1
  rw [show k + 1 = 1 + k from add_comm k 1, zpow_add, zpow_one, ← Set.image_comp]
  rfl

-- ============================================
-- CYCLE LENGTH
-- ============================================

/-- The cycle length of an ℓ-cycle -/
noncomputable def cycleLength (σ : Perm α) : ℕ := σ.support.card
