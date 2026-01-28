/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_1_Defs

/-!
# Lemma 11.1: Size-2 Block Systems

Proves that the only size-2 partition of Fin 6 that is H₆-invariant is B₀.

## Main Results

* `size2_unique_block_system`: If P is a size-2 block system for H₆, then P.blocks = B₀
-/

open MulAction Equiv.Perm

/-- g₂ maps {0,1} to {1,3}, which overlaps {0,1} -/
theorem g₂_image_01 : ({0, 1} : Finset (Fin 6)).image (g₂ 0 0 0) = {1, 3} := by native_decide

/-- g₁ maps {0,2} to {5,0}, which overlaps {0,2} -/
theorem g₁_image_02 : ({0, 2} : Finset (Fin 6)).image (g₁ 0 0 0) = {5, 0} := by native_decide

/-- g₂ maps {0,4} to {1,0}, which overlaps {0,4} -/
theorem g₂_image_04 : ({0, 4} : Finset (Fin 6)).image (g₂ 0 0 0) = {1, 0} := by native_decide

/-- g₁ maps {0,5} to {5,3} -/
theorem g₁_image_05 : ({0, 5} : Finset (Fin 6)).image (g₁ 0 0 0) = {5, 3} := by native_decide

/-- g₁ maps {5,3} to {3,2}, which overlaps {5,3} -/
theorem g₁_image_53 : ({5, 3} : Finset (Fin 6)).image (g₁ 0 0 0) = {3, 2} := by native_decide

/-- g₂ maps Block1 to Block2 -/
theorem g₂_image_Block1 : Block1.image (g₂ 0 0 0) = Block2 := by native_decide

/-- g₁ maps Block1 to Block3 -/
theorem g₁_image_Block1 : Block1.image (g₁ 0 0 0) = Block3 := by native_decide

/-- The complement of B₀ in Fin 6 is empty -/
theorem B₀_complement_empty : Finset.univ \ (Block1 ∪ Block2 ∪ Block3) = (∅ : Finset (Fin 6)) := by
  native_decide

/-- {0,1} and {1,3} are not disjoint -/
theorem not_disjoint_01_13 : ¬Disjoint ({0,1} : Finset (Fin 6)) {1,3} := by native_decide

/-- {0,2} and {5,0} are not disjoint -/
theorem not_disjoint_02_50 : ¬Disjoint ({0,2} : Finset (Fin 6)) {5,0} := by native_decide

/-- {0,4} and {1,0} are not disjoint -/
theorem not_disjoint_04_10 : ¬Disjoint ({0,4} : Finset (Fin 6)) {1,0} := by native_decide

/-- {5,3} and {3,2} are not disjoint -/
theorem not_disjoint_53_32 : ¬Disjoint ({5,3} : Finset (Fin 6)) {3,2} := by native_decide

/-- {0,1} ≠ {1,3} -/
theorem ne_01_13 : ({0,1} : Finset (Fin 6)) ≠ {1,3} := by native_decide

/-- {0,2} ≠ {5,0} -/
theorem ne_02_50 : ({0,2} : Finset (Fin 6)) ≠ {5,0} := by native_decide

/-- {0,4} ≠ {1,0} -/
theorem ne_04_10 : ({0,4} : Finset (Fin 6)) ≠ {1,0} := by native_decide

/-- {5,3} ≠ {3,2} -/
theorem ne_53_32 : ({5,3} : Finset (Fin 6)) ≠ {3,2} := by native_decide

/-- {0,3} = Block1 -/
theorem eq_03_Block1 : ({0, 3} : Finset (Fin 6)) = Block1 := rfl

/-- Any size-2 subset containing 0 is in this list -/
theorem size2_with_0_cases (B : Finset (Fin 6)) (hCard : B.card = 2) (h0 : (0 : Fin 6) ∈ B) :
    B = {0,1} ∨ B = {0,2} ∨ B = {0,3} ∨ B = {0,4} ∨ B = {0,5} := by
  have hTwo := Finset.card_eq_two.mp hCard
  obtain ⟨a, b, hab, hB_eq⟩ := hTwo
  subst hB_eq
  simp only [Finset.mem_insert, Finset.mem_singleton] at h0
  rcases h0 with rfl | rfl
  · -- a = 0, so B = {0, b} with b ≠ 0
    fin_cases b <;> first | exact absurd rfl hab | decide
  · -- b = 0, so B = {a, 0} with a ≠ 0
    fin_cases a <;> first | exact absurd rfl hab.symm | decide

/-- For any size-2 block system P, P.blocks = B₀ -/
theorem size2_unique_block_system (P : Partition6) (hBS : IsBlockSystem P)
    (hSize2 : P.blockSize = 2) : P.blocks = B₀ := by
  -- Find a block containing 0
  have h0 : ∃ B ∈ P.blocks, (0 : Fin 6) ∈ B := by
    have hCover := P.covers_all
    have h0_univ : (0 : Fin 6) ∈ Finset.univ := Finset.mem_univ 0
    rw [← hCover] at h0_univ
    simp only [Finset.mem_sup, id_eq] at h0_univ
    exact h0_univ
  obtain ⟨B, hB_mem, h0_in_B⟩ := h0
  have hBcard : B.card = 2 := P.all_same_size B hB_mem ▸ hSize2
  -- B must be one of the 5 size-2 subsets containing 0
  have hB_cases := size2_with_0_cases B hBcard h0_in_B
  -- Only {0,3} = Block1 is compatible with being a block system
  have hB_eq_Block1 : B = Block1 := by
    rcases hB_cases with hB | hB | hB | hB | hB
    -- B = {0, 1}: g₂({0,1}) = {1,3} overlaps {0,1}
    · exfalso
      rw [hB] at hB_mem
      have hImg := hBS (g₂ 0 0 0) (g₂_mem_H 0 0 0) _ hB_mem
      rw [g₂_image_01] at hImg
      exact not_disjoint_01_13 (P.pairwise_disjoint hB_mem hImg ne_01_13)
    -- B = {0, 2}: g₁({0,2}) = {5,0} overlaps {0,2}
    · exfalso
      rw [hB] at hB_mem
      have hImg := hBS (g₁ 0 0 0) (g₁_mem_H 0 0 0) _ hB_mem
      rw [g₁_image_02] at hImg
      exact not_disjoint_02_50 (P.pairwise_disjoint hB_mem hImg ne_02_50)
    -- B = {0, 3} = Block1
    · exact hB.trans eq_03_Block1
    -- B = {0, 4}: g₂({0,4}) = {1,0} overlaps {0,4}
    · exfalso
      rw [hB] at hB_mem
      have hImg := hBS (g₂ 0 0 0) (g₂_mem_H 0 0 0) _ hB_mem
      rw [g₂_image_04] at hImg
      exact not_disjoint_04_10 (P.pairwise_disjoint hB_mem hImg ne_04_10)
    -- B = {0, 5}: g₁ maps to {5,3}, then to {3,2} which overlaps {5,3}
    · exfalso
      rw [hB] at hB_mem
      have hImg1 := hBS (g₁ 0 0 0) (g₁_mem_H 0 0 0) _ hB_mem
      rw [g₁_image_05] at hImg1
      have hImg2 := hBS (g₁ 0 0 0) (g₁_mem_H 0 0 0) _ hImg1
      rw [g₁_image_53] at hImg2
      exact not_disjoint_53_32 (P.pairwise_disjoint hImg1 hImg2 ne_53_32)
  -- B = Block1 is in P.blocks
  rw [hB_eq_Block1] at hB_mem
  -- Block2 = g₂(Block1) is in P.blocks
  have hBlock2_mem : Block2 ∈ P.blocks := by
    have hImg := hBS (g₂ 0 0 0) (g₂_mem_H 0 0 0) Block1 hB_mem
    rw [g₂_image_Block1] at hImg
    exact hImg
  -- Block3 = g₁(Block1) is in P.blocks
  have hBlock3_mem : Block3 ∈ P.blocks := by
    have hImg := hBS (g₁ 0 0 0) (g₁_mem_H 0 0 0) Block1 hB_mem
    rw [g₁_image_Block1] at hImg
    exact hImg
  -- P.blocks = B₀ since both have cardinality 3 and B₀ ⊆ P.blocks
  ext X
  constructor
  · intro hX
    simp only [B₀, Finset.mem_insert, Finset.mem_singleton]
    by_contra hNot
    push_neg at hNot
    obtain ⟨h1, h2, h3⟩ := hNot
    have hDisj1 : Disjoint Block1 X := P.pairwise_disjoint hB_mem hX h1.symm
    have hDisj2 : Disjoint Block2 X := P.pairwise_disjoint hBlock2_mem hX h2.symm
    have hDisj3 : Disjoint Block3 X := P.pairwise_disjoint hBlock3_mem hX h3.symm
    have hXsub : X ⊆ Finset.univ \ (Block1 ∪ Block2 ∪ Block3) := by
      intro x hx
      simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_union, true_and]
      intro hOr
      rcases hOr with (h | h) | h
      · exact Finset.disjoint_right.mp hDisj1 hx h
      · exact Finset.disjoint_right.mp hDisj2 hx h
      · exact Finset.disjoint_right.mp hDisj3 hx h
    rw [B₀_complement_empty] at hXsub
    have hXcard : X.card = 2 := P.all_same_size X hX ▸ hSize2
    have hXempty : X = ∅ := Finset.subset_empty.mp hXsub
    simp only [hXempty, Finset.card_empty] at hXcard
    exact absurd hXcard (by decide : (0 : ℕ) ≠ 2)
  · intro hX
    simp only [B₀, Finset.mem_insert, Finset.mem_singleton] at hX
    rcases hX with rfl | rfl | rfl
    · exact hB_mem
    · exact hBlock2_mem
    · exact hBlock3_mem
