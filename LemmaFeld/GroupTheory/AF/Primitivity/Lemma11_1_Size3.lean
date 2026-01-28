/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_1_Defs

/-!
# Lemma 11.1: Size-3 Block Systems

Proves that no size-3 partition of Fin 6 is H₆-invariant.

## Main Results

* `no_size3_block_system`: No size-3 partition is a block system for H₆

## Proof Outline

1. There are 10 size-3 partitions (each determined by choosing 3 elements)
2. For each, some generator maps a block outside {B, Bᶜ}
3. Thus no size-3 partition is H₆-invariant
-/

open MulAction Equiv.Perm

/-- Number of size-3 partitions of Fin 6 into 2 blocks -/
theorem size3_partition_count : ∃ n : ℕ, n = 10 ∧
    n = Nat.choose 6 3 / 2 := by
  use 10
  constructor
  · rfl
  · native_decide

/-- Helper: check if a generator breaks a 2-block partition {B, Bᶜ} -/
def generatorBreaksPartition (g : Equiv.Perm (Fin 6)) (B : Finset (Fin 6)) : Bool :=
  let imgB := B.image g
  imgB ≠ B ∧ imgB ≠ (Finset.univ \ B)

/-- All 10 size-3 blocks (each determines a unique partition with its complement) -/
def allSize3Blocks : List (Finset (Fin 6)) := [
  {0, 1, 2}, {0, 1, 3}, {0, 1, 4}, {0, 1, 5},
  {0, 2, 3}, {0, 2, 4}, {0, 2, 5},
  {0, 3, 4}, {0, 3, 5}, {0, 4, 5}
]

/-- For every size-3 block B, some generator maps B outside {B, Bᶜ} -/
theorem all_size3_broken : ∀ B ∈ allSize3Blocks,
    generatorBreaksPartition (g₁ 0 0 0) B ∨
    generatorBreaksPartition (g₂ 0 0 0) B ∨
    generatorBreaksPartition (g₃ 0 0 0) B := by
  native_decide

/-- The complete list of all size-3 subsets of Fin 6 containing 0 -/
theorem allSize3Blocks_complete : ∀ B : Finset (Fin 6), B.card = 3 → (0 : Fin 6) ∈ B →
    B ∈ allSize3Blocks := by native_decide

/-- Any size-3 subset of Fin 6 containing 0 is in allSize3Blocks -/
theorem size3_block_in_list (B : Finset (Fin 6)) (hCard : B.card = 3) (h0 : (0 : Fin 6) ∈ B) :
    B ∈ allSize3Blocks := allSize3Blocks_complete B hCard h0

/-- For a size-3 partition, if B is a block, then the only other block is the complement -/
theorem size3_partition_complement (P : Partition6) (hSize : P.blockSize = 3)
    (B : Finset (Fin 6)) (hB : B ∈ P.blocks) :
    ∀ C ∈ P.blocks, C = B ∨ C = Finset.univ \ B := by
  intro C hC
  have hBcard : B.card = 3 := P.all_same_size B hB ▸ hSize
  have hCcard : C.card = 3 := P.all_same_size C hC ▸ hSize
  by_cases hBC : B = C
  · left; exact hBC.symm
  · right
    have hDisj : Disjoint B C := P.pairwise_disjoint hB hC hBC
    ext x
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · intro hx hxB
      exact Finset.disjoint_left.mp hDisj hxB hx
    · intro hx
      have hCover := P.covers_all
      have hx_univ : x ∈ Finset.univ := Finset.mem_univ x
      rw [← hCover] at hx_univ
      simp only [Finset.mem_sup, id_eq] at hx_univ
      obtain ⟨D, hD, hxD⟩ := hx_univ
      by_cases hDB : D = B
      · subst hDB; exact absurd hxD hx
      · by_cases hDC : D = C
        · subst hDC; exact hxD
        · have hDcard : D.card = 3 := P.all_same_size D hD ▸ hSize
          have hDisjBD : Disjoint B D := P.pairwise_disjoint hB hD (Ne.symm hDB)
          have hDisjCD : Disjoint C D := P.pairwise_disjoint hC hD (Ne.symm hDC)
          have hBCD_disjoint : Disjoint (B ∪ C) D := by
            rw [Finset.disjoint_union_left]
            exact ⟨hDisjBD, hDisjCD⟩
          have hBCD_card : (B ∪ C ∪ D).card = 9 := by
            rw [Finset.card_union_of_disjoint hBCD_disjoint]
            rw [Finset.card_union_of_disjoint hDisj]
            omega
          have hLe : (B ∪ C ∪ D).card ≤ 6 := by
            calc (B ∪ C ∪ D).card ≤ Finset.univ.card := Finset.card_le_card (Finset.subset_univ _)
              _ = 6 := Fintype.card_fin 6
          omega

/-- No size-3 partition is H₆-invariant -/
theorem no_size3_block_system :
    ∀ P : Partition6, P.blockSize = 3 → ¬IsBlockSystem P := by
  intro P hSize hInv
  have h0 : ∃ B ∈ P.blocks, (0 : Fin 6) ∈ B := by
    have hCover := P.covers_all
    have h0_univ : (0 : Fin 6) ∈ Finset.univ := Finset.mem_univ 0
    rw [← hCover] at h0_univ
    simp only [Finset.mem_sup, id_eq] at h0_univ
    exact h0_univ
  obtain ⟨B, hB_mem, h0_in_B⟩ := h0
  have hBcard : B.card = 3 := P.all_same_size B hB_mem ▸ hSize
  have hB_in_list : B ∈ allSize3Blocks := size3_block_in_list B hBcard h0_in_B
  obtain hg₁ | hg₂ | hg₃ := all_size3_broken B hB_in_list
  · simp only [generatorBreaksPartition, ne_eq, decide_eq_true_eq] at hg₁
    obtain ⟨hne1, hne2⟩ := hg₁
    have hg₁_mem : g₁ 0 0 0 ∈ H₆ := g₁_mem_H 0 0 0
    have hImg := hInv (g₁ 0 0 0) hg₁_mem B hB_mem
    have hOpts := size3_partition_complement P hSize B hB_mem (B.image (g₁ 0 0 0)) hImg
    rcases hOpts with hEqB | hEqCompl
    · exact hne1 hEqB
    · exact hne2 hEqCompl
  · simp only [generatorBreaksPartition, ne_eq, decide_eq_true_eq] at hg₂
    obtain ⟨hne1, hne2⟩ := hg₂
    have hg₂_mem : g₂ 0 0 0 ∈ H₆ := g₂_mem_H 0 0 0
    have hImg := hInv (g₂ 0 0 0) hg₂_mem B hB_mem
    have hOpts := size3_partition_complement P hSize B hB_mem (B.image (g₂ 0 0 0)) hImg
    rcases hOpts with hEqB | hEqCompl
    · exact hne1 hEqB
    · exact hne2 hEqCompl
  · simp only [generatorBreaksPartition, ne_eq, decide_eq_true_eq] at hg₃
    obtain ⟨hne1, hne2⟩ := hg₃
    have hg₃_mem : g₃ 0 0 0 ∈ H₆ := g₃_mem_H 0 0 0
    have hImg := hInv (g₃ 0 0 0) hg₃_mem B hB_mem
    have hOpts := size3_partition_complement P hSize B hB_mem (B.image (g₃ 0 0 0)) hImg
    rcases hOpts with hEqB | hEqCompl
    · exact hne1 hEqB
    · exact hne2 hEqCompl
