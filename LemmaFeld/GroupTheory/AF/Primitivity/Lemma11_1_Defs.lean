/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.BaseCase.Lemma03
import Mathlib.GroupTheory.GroupAction.Blocks

/-!
# Lemma 11.1 Definitions: Block System Structures

Core definitions for block systems on Fin 6, extracted for modularity.

## Main Definitions

* `Partition6`: A partition of Fin 6 into sets of equal size
* `IsBlockSystem`: A partition where H₆ acts on the blocks
* `IsNontrivialBlockSystem`: A block system with 1 < blockSize < 6
-/

open MulAction Equiv.Perm

/-- A partition of Fin 6 into sets of equal size -/
structure Partition6 where
  blocks : Finset (Finset (Fin 6))
  blockSize : ℕ
  size_divides : blockSize ∣ 6
  all_same_size : ∀ B ∈ blocks, B.card = blockSize
  pairwise_disjoint : (blocks : Set (Finset (Fin 6))).PairwiseDisjoint id
  covers_all : blocks.sup id = Finset.univ

/-- A block system for H₆ is a partition where H₆ acts on the blocks -/
def IsBlockSystem (P : Partition6) : Prop :=
  ∀ g ∈ H₆, ∀ B ∈ P.blocks, (B.image g) ∈ P.blocks

/-- A block system is non-trivial if blocks have size > 1 and < 6 -/
def IsNontrivialBlockSystem (P : Partition6) : Prop :=
  IsBlockSystem P ∧ 1 < P.blockSize ∧ P.blockSize < 6
