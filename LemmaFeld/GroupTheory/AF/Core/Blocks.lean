/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Block System B₀

This file defines the block system B₀ = {{1,4}, {2,5}, {3,6}} for the base case.

In 0-indexed Lean notation:
- Block1 = {0, 3} (representing {1, 4})
- Block2 = {1, 4} (representing {2, 5})
- Block3 = {2, 5} (representing {3, 6})

## Main Definitions

* `Block1`, `Block2`, `Block3` - The three blocks as Finsets
* `B₀` - The block system as a Finset of Finsets

## Index Convention

AF element k → Lean index (k-1)
- {1, 4} in AF → {0, 3} in Lean
- {2, 5} in AF → {1, 4} in Lean
- {3, 6} in AF → {2, 5} in Lean
-/

/-- Block 1: {0, 3} representing {1, 4} in 1-indexed -/
def Block1 : Finset (Fin 6) := {0, 3}

/-- Block 2: {1, 4} representing {2, 5} in 1-indexed -/
def Block2 : Finset (Fin 6) := {1, 4}

/-- Block 3: {2, 5} representing {3, 6} in 1-indexed -/
def Block3 : Finset (Fin 6) := {2, 5}

/-- The block system B₀ = {Block1, Block2, Block3} -/
def B₀ : Finset (Finset (Fin 6)) := {Block1, Block2, Block3}

/-- Each block has exactly 2 elements -/
theorem Block1_card : Block1.card = 2 := by decide

theorem Block2_card : Block2.card = 2 := by decide

theorem Block3_card : Block3.card = 2 := by decide

/-- The blocks are pairwise disjoint -/
theorem Block1_Block2_disjoint : Disjoint Block1 Block2 := by
  decide

theorem Block1_Block3_disjoint : Disjoint Block1 Block3 := by
  decide

theorem Block2_Block3_disjoint : Disjoint Block2 Block3 := by
  decide

/-- The union of all blocks is Fin 6 -/
theorem blocks_cover : Block1 ∪ Block2 ∪ Block3 = Finset.univ := by
  decide

/-- B₀ has exactly 3 blocks -/
theorem B₀_card : B₀.card = 3 := by decide

/-- Block1 is in B₀ -/
theorem Block1_mem_B₀ : Block1 ∈ B₀ := by decide

/-- Block2 is in B₀ -/
theorem Block2_mem_B₀ : Block2 ∈ B₀ := by decide

/-- Block3 is in B₀ -/
theorem Block3_mem_B₀ : Block3 ∈ B₀ := by decide

/-- Given a point in Fin 6, return which block it belongs to (0, 1, or 2) -/
def blockIndex (x : Fin 6) : Fin 3 :=
  if x ∈ Block1 then 0
  else if x ∈ Block2 then 1
  else 2
