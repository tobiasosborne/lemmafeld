/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core

-- native_decide is appropriate for computational proofs in this project
set_option linter.style.nativeDecide false

/-!
# Lemma 1: Block Preservation in Base Case

The partition B₀ = {{1,4}, {2,5}, {3,6}} (= {{0,3}, {1,4}, {2,5}} in 0-indexed)
is preserved setwise by each generator h_i.

## Main Results

* `g₁_preserves_B₀` - g₁ permutes the blocks of B₀
* `g₂_preserves_B₀` - g₂ permutes the blocks of B₀
* `g₃_preserves_B₀` - g₃ permutes the blocks of B₀

## Proof Strategy

Direct computation using `native_decide` for the base case n=k=m=0.

## Reference

See `examples/lemmas/lemma01_block_preservation.md` for the natural language proof.
-/

/-- g₁ maps Block1 to Block3: {0,3} → {2,5} -/
theorem g₁_Block1_eq_Block3 : Block1.image (g₁ 0 0 0) = Block3 := by
  native_decide

/-- g₁ fixes Block2: {1,4} → {1,4} -/
theorem g₁_Block2_eq_Block2 : Block2.image (g₁ 0 0 0) = Block2 := by
  native_decide

/-- g₁ maps Block3 to Block1: {2,5} → {0,3} -/
theorem g₁_Block3_eq_Block1 : Block3.image (g₁ 0 0 0) = Block1 := by
  native_decide

/-- g₂ maps Block1 to Block2: {0,3} → {1,4} -/
theorem g₂_Block1_eq_Block2 : Block1.image (g₂ 0 0 0) = Block2 := by
  native_decide

/-- g₂ maps Block2 to Block1: {1,4} → {0,3} -/
theorem g₂_Block2_eq_Block1 : Block2.image (g₂ 0 0 0) = Block1 := by
  native_decide

/-- g₂ fixes Block3: {2,5} → {2,5} -/
theorem g₂_Block3_eq_Block3 : Block3.image (g₂ 0 0 0) = Block3 := by
  native_decide

/-- g₃ fixes Block1: {0,3} → {0,3} -/
theorem g₃_Block1_eq_Block1 : Block1.image (g₃ 0 0 0) = Block1 := by
  native_decide

/-- g₃ maps Block2 to Block3: {1,4} → {2,5} -/
theorem g₃_Block2_eq_Block3 : Block2.image (g₃ 0 0 0) = Block3 := by
  native_decide

/-- g₃ maps Block3 to Block2: {2,5} → {1,4} -/
theorem g₃_Block3_eq_Block2 : Block3.image (g₃ 0 0 0) = Block2 := by
  native_decide

/-- g₁ permutes B₀: each block maps to another block in B₀ -/
theorem g₁_preserves_B₀ : ∀ B ∈ B₀, B.image (g₁ 0 0 0) ∈ B₀ := by
  intro B hB
  simp only [B₀, Finset.mem_insert, Finset.mem_singleton] at hB ⊢
  rcases hB with rfl | rfl | rfl
  · -- Block1 → Block3
    right; right; exact g₁_Block1_eq_Block3
  · -- Block2 → Block2
    right; left; exact g₁_Block2_eq_Block2
  · -- Block3 → Block1
    left; exact g₁_Block3_eq_Block1

/-- g₂ permutes B₀: each block maps to another block in B₀ -/
theorem g₂_preserves_B₀ : ∀ B ∈ B₀, B.image (g₂ 0 0 0) ∈ B₀ := by
  intro B hB
  simp only [B₀, Finset.mem_insert, Finset.mem_singleton] at hB ⊢
  rcases hB with rfl | rfl | rfl
  · -- Block1 → Block2
    right; left; exact g₂_Block1_eq_Block2
  · -- Block2 → Block1
    left; exact g₂_Block2_eq_Block1
  · -- Block3 → Block3
    right; right; exact g₂_Block3_eq_Block3

/-- g₃ permutes B₀: each block maps to another block in B₀ -/
theorem g₃_preserves_B₀ : ∀ B ∈ B₀, B.image (g₃ 0 0 0) ∈ B₀ := by
  intro B hB
  simp only [B₀, Finset.mem_insert, Finset.mem_singleton] at hB ⊢
  rcases hB with rfl | rfl | rfl
  · -- Block1 → Block1
    left; exact g₃_Block1_eq_Block1
  · -- Block2 → Block3
    right; right; exact g₃_Block2_eq_Block3
  · -- Block3 → Block2
    right; left; exact g₃_Block3_eq_Block2
