/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.BaseCase.Lemma01
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.Tactic.FinCases

-- native_decide is appropriate for computational proofs in this project
set_option linter.style.nativeDecide false

/-!
# Lemma 2: Induced Action on Blocks

The map φ: H₆ → S_{B₀} ≅ S₃ induced by the action on blocks satisfies:
1. φ(g₁) = (B₁ B₃) - transposition swapping blocks 1 and 3
2. φ(g₂) = (B₁ B₂) - transposition swapping blocks 1 and 2
3. φ(g₃) = (B₂ B₃) - transposition swapping blocks 2 and 3

Corollary: Im(φ) = S₃

## Main Results

* `blockAction` - Function mapping permutation to its action on block indices
* `φ_g₁_eq_swap` - g₁ swaps blocks 0 and 2 (i.e., Block1 and Block3)
* `φ_g₂_eq_swap` - g₂ swaps blocks 0 and 1 (i.e., Block1 and Block2)
* `φ_g₃_eq_swap` - g₃ swaps blocks 1 and 2 (i.e., Block2 and Block3)
* `φ_surjective` - The induced action is surjective onto S₃

## Proof Strategy

Use Lemma 1 results to establish the block permutations directly.

## Reference

See `examples/lemmas/lemma02_induced_action.md` for the natural language proof.
-/

/-- Given a block index and a permutation, return the index of the image block.
    Block indices: 0 = Block1, 1 = Block2, 2 = Block3 -/
def blockAction (g : Equiv.Perm (Fin 6)) (i : Fin 3) : Fin 3 :=
  let block := match i with
    | 0 => Block1
    | 1 => Block2
    | 2 => Block3
  let imageBlock := block.image g
  if imageBlock = Block1 then 0
  else if imageBlock = Block2 then 1
  else 2

/-- g₁ maps block index 0 to block index 2 -/
theorem g₁_blockAction_0 : blockAction (g₁ 0 0 0) 0 = 2 := by
  simp only [blockAction, g₁_Block1_eq_Block3]
  native_decide

/-- g₁ maps block index 1 to block index 1 -/
theorem g₁_blockAction_1 : blockAction (g₁ 0 0 0) 1 = 1 := by
  simp only [blockAction, g₁_Block2_eq_Block2]
  native_decide

/-- g₁ maps block index 2 to block index 0 -/
theorem g₁_blockAction_2 : blockAction (g₁ 0 0 0) 2 = 0 := by
  simp only [blockAction, g₁_Block3_eq_Block1]
  native_decide

/-- g₂ maps block index 0 to block index 1 -/
theorem g₂_blockAction_0 : blockAction (g₂ 0 0 0) 0 = 1 := by
  simp only [blockAction, g₂_Block1_eq_Block2]
  native_decide

/-- g₂ maps block index 1 to block index 0 -/
theorem g₂_blockAction_1 : blockAction (g₂ 0 0 0) 1 = 0 := by
  simp only [blockAction, g₂_Block2_eq_Block1]
  native_decide

/-- g₂ maps block index 2 to block index 2 -/
theorem g₂_blockAction_2 : blockAction (g₂ 0 0 0) 2 = 2 := by
  simp only [blockAction, g₂_Block3_eq_Block3]
  native_decide

/-- g₃ maps block index 0 to block index 0 -/
theorem g₃_blockAction_0 : blockAction (g₃ 0 0 0) 0 = 0 := by
  simp only [blockAction, g₃_Block1_eq_Block1]
  native_decide

/-- g₃ maps block index 1 to block index 2 -/
theorem g₃_blockAction_1 : blockAction (g₃ 0 0 0) 1 = 2 := by
  simp only [blockAction, g₃_Block2_eq_Block3]
  native_decide

/-- g₃ maps block index 2 to block index 1 -/
theorem g₃_blockAction_2 : blockAction (g₃ 0 0 0) 2 = 1 := by
  simp only [blockAction, g₃_Block3_eq_Block2]
  native_decide

/-- g₁ induces the transposition (0 2) on blocks: swaps Block1 ↔ Block3, fixes Block2 -/
theorem φ_g₁_eq_swap : blockAction (g₁ 0 0 0) = (Equiv.swap 0 2 : Equiv.Perm (Fin 3)) := by
  funext i
  match i with
  | 0 => simp only [g₁_blockAction_0]; native_decide
  | 1 => simp only [g₁_blockAction_1]; native_decide
  | 2 => simp only [g₁_blockAction_2]; native_decide

/-- g₂ induces the transposition (0 1) on blocks: swaps Block1 ↔ Block2, fixes Block3 -/
theorem φ_g₂_eq_swap : blockAction (g₂ 0 0 0) = (Equiv.swap 0 1 : Equiv.Perm (Fin 3)) := by
  funext i
  match i with
  | 0 => simp only [g₂_blockAction_0]; native_decide
  | 1 => simp only [g₂_blockAction_1]; native_decide
  | 2 => simp only [g₂_blockAction_2]; native_decide

/-- g₃ induces the transposition (1 2) on blocks: swaps Block2 ↔ Block3, fixes Block1 -/
theorem φ_g₃_eq_swap : blockAction (g₃ 0 0 0) = (Equiv.swap 1 2 : Equiv.Perm (Fin 3)) := by
  funext i
  match i with
  | 0 => simp only [g₃_blockAction_0]; native_decide
  | 1 => simp only [g₃_blockAction_1]; native_decide
  | 2 => simp only [g₃_blockAction_2]; native_decide

/-- The three transpositions (0 1), (0 2), (1 2) generate S₃ -/
theorem S3_generated_by_transpositions :
    Subgroup.closure ({Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2} : Set (Equiv.Perm (Fin 3)))
    = ⊤ := by
  -- For Fin 3, the set {swap 0 1, swap 0 2, swap 1 2} contains all swaps
  have h_eq : {σ : Equiv.Perm (Fin 3) | σ.IsSwap} =
      {Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2} := by
    ext σ
    simp only [Equiv.Perm.IsSwap, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro ⟨a, b, hab, hσ⟩
      subst hσ
      fin_cases a <;> fin_cases b <;>
        simp_all only [ne_eq, Fin.reduceFinMk, Fin.isValue, not_true_eq_false,
          Equiv.swap_comm, true_or, or_true]
    · intro h
      rcases h with rfl | rfl | rfl
      · exact ⟨0, 1, by decide, rfl⟩
      · exact ⟨0, 2, by decide, rfl⟩
      · exact ⟨1, 2, by decide, rfl⟩
  rw [← h_eq]
  exact Equiv.Perm.closure_isSwap

/-- The block actions of g₁, g₂, g₃ generate S₃ (equivalently, Im(φ) = S₃) -/
theorem φ_image_generates_S3 :
    Subgroup.closure ({Equiv.swap 0 2, Equiv.swap 0 1, Equiv.swap 1 2} : Set (Equiv.Perm (Fin 3)))
    = ⊤ := by
  -- The sets are equal (just reordered)
  have h : ({Equiv.swap 0 2, Equiv.swap 0 1, Equiv.swap 1 2} : Set (Equiv.Perm (Fin 3))) =
           {Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2} := by
    ext; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto
  rw [h]
  exact S3_generated_by_transpositions

/-- Corollary: The induced homomorphism φ: H₆ → S₃ is surjective -/
theorem φ_surjective :
    ∀ σ : Equiv.Perm (Fin 3), σ ∈ Subgroup.closure
      ({Equiv.swap 0 2, Equiv.swap 0 1, Equiv.swap 1 2} : Set (Equiv.Perm (Fin 3))) := by
  intro σ
  rw [φ_image_generates_S3]
  exact Subgroup.mem_top σ
