/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_4_Helpers

/-!
# Lemma 11.4: Block Orbit

For an ℓ-cycle σ and a σ-invariant block system, the orbit size r of any block
meeting supp(σ) divides ℓ, and each such block contains exactly ℓ/r support elements.

## Main Results

* `lemma11_4_block_orbit`: Combined statement: r | ℓ and |B ∩ supp(σ)| = ℓ/r

## Reference

See `examples/lemmas/lemma11_4_block_orbit.md` for the natural language proof.
-/

open Equiv Equiv.Perm Set MulAction
open scoped Pointwise

variable {α : Type*} [DecidableEq α] [Fintype α]

-- ============================================
-- SUPPORT DISTRIBUTION
-- ============================================

/-- Blocks in the orbit are exactly those meeting the support -/
theorem orbit_blocks_meet_support {σ : Perm α} (hσ : σ.IsCycle)
    {B : Set α} (hMeet : (B ∩ (σ.support : Set α)).Nonempty)
    {C : Set α} (hC : C ∈ blockOrbit σ B) :
    (C ∩ (σ.support : Set α)).Nonempty := by
  obtain ⟨x, hxB, hxSupp⟩ := hMeet
  obtain ⟨k, rfl⟩ := hC
  refine ⟨(σ ^ k) x, mem_image_of_mem _ hxB, ?_⟩
  exact zpow_apply_mem_support.mpr hxSupp

/-- The orbit blocks partition the support -/
theorem orbit_blocks_partition_support {σ : Perm α} (hσ : σ.IsCycle)
    {B : Set α} {Blocks : Set (Set α)} (_hInv : BlockSystemInvariant σ Blocks)
    (_hB : B ∈ Blocks) (hMeet : (B ∩ (σ.support : Set α)).Nonempty)
    (_hDisj : Blocks.PairwiseDisjoint id) :
    (σ.support : Set α) = ⋃ C ∈ blockOrbit σ B, (C ∩ (σ.support : Set α)) := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_inter_iff]
  constructor
  · intro hx
    obtain ⟨y, hyB, hySupp⟩ := hMeet
    have hy_ne : σ y ≠ y := Perm.mem_support.mp hySupp
    have hx_ne : σ x ≠ x := Perm.mem_support.mp hx
    obtain ⟨k, hk⟩ := hσ.sameCycle hy_ne hx_ne
    refine ⟨(σ ^ k) '' B, ⟨k, rfl⟩, ?_, ?_⟩
    · rw [← hk]; exact mem_image_of_mem _ hyB
    · rw [← hk]; exact zpow_apply_mem_support.mpr hySupp
  · intro ⟨_, _, _, hxSupp⟩
    exact hxSupp

/-- σ maps B ∩ support to (σ B) ∩ support bijectively -/
theorem sigma_preserves_intersection_card (σ : Perm α) (B : Set α) :
    (σ '' B ∩ (σ.support : Set α)).ncard = (B ∩ (σ.support : Set α)).ncard := by
  have heq : σ '' B ∩ (σ.support : Set α) = σ '' (B ∩ σ.support) := by
    ext y
    constructor
    · rintro ⟨⟨x, hxB, rfl⟩, hyS⟩
      exact ⟨x, ⟨hxB, Perm.apply_mem_support.mp hyS⟩, rfl⟩
    · rintro ⟨x, ⟨hxB, hxS⟩, rfl⟩
      exact ⟨⟨x, hxB, rfl⟩, Perm.apply_mem_support.mpr hxS⟩
  rw [heq]
  exact Set.ncard_image_of_injective _ σ.injective

/-- All blocks in the orbit have the same intersection size with support -/
theorem orbit_blocks_same_card (σ : Perm α) (B : Set α) (k : ℤ) :
    ((σ ^ k) '' B ∩ (σ.support : Set α)).ncard = (B ∩ (σ.support : Set α)).ncard := by
  have heq : (σ ^ k) '' B ∩ (σ.support : Set α) = (σ ^ k) '' (B ∩ σ.support) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_image]
    constructor
    · rintro ⟨⟨x, hxB, rfl⟩, hyS⟩
      refine ⟨x, ⟨hxB, ?_⟩, rfl⟩
      exact zpow_apply_mem_support.mp hyS
    · rintro ⟨x, ⟨hxB, hxS⟩, rfl⟩
      exact ⟨⟨x, hxB, rfl⟩, zpow_apply_mem_support.mpr hxS⟩
  rw [heq]
  exact Set.ncard_image_of_injective _ (σ ^ k).injective

-- ============================================
-- INTERSECTION CARDINALITY
-- ============================================

/-- **Support intersection cardinality**

    Each block in the orbit contains exactly ℓ/r elements of supp(σ).

    Proof: All orbit blocks have equal intersection size with support,
    orbit blocks partition the support, so cycleLength = blockOrbitSize × size.  -/
theorem block_support_intersection_card {σ : Perm α} (hσ : σ.IsCycle)
    {B : Set α} {Blocks : Set (Set α)} (hInv : BlockSystemInvariant σ Blocks)
    (hB : B ∈ Blocks) (hMeet : (B ∩ (σ.support : Set α)).Nonempty)
    (hDisj : Blocks.PairwiseDisjoint id) :
    (B ∩ (σ.support : Set α)).ncard = cycleLength σ / blockOrbitSize σ B := by
  have heq_card : ∀ C ∈ blockOrbit σ B, (C ∩ ↑σ.support).ncard = (B ∩ ↑σ.support).ncard := by
    intro C hC
    obtain ⟨k, rfl⟩ := hC
    exact orbit_blocks_same_card σ B k
  have hdiv := block_orbit_divides_cycle_length hσ hInv hB hMeet
  -- Finiteness
  have hFin : Blocks.Finite := Set.Finite.subset Set.finite_univ (Set.subset_univ _)
  have hOrbitFin : (blockOrbit σ B).Finite := Set.Finite.subset Set.finite_univ (Set.subset_univ _)
  -- Positivity
  have hpos : 0 < blockOrbitSize σ B := by
    unfold blockOrbitSize; rw [Set.ncard_pos]
    exact ⟨B, ⟨0, by simp⟩⟩
  have hne : blockOrbitSize σ B ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
  -- Get the partition and disjointness
  have hpart := orbit_blocks_partition_support hσ hInv hB hMeet hDisj
  have hDisjOrbit := orbit_intersections_pairwise_disjoint hInv hFin hB hDisj
  have hFinInter : ∀ C ∈ blockOrbit σ B, (C ∩ ↑σ.support).Finite := by
    intro C _; exact Set.Finite.subset (Set.toFinite σ.support) Set.inter_subset_right
  -- Key: cycleLength = blockOrbitSize * (B ∩ support).ncard
  have hprod : cycleLength σ = blockOrbitSize σ B * (B ∩ ↑σ.support).ncard := by
    -- First show: (⋃ C ∈ orbit, C ∩ support).ncard = blockOrbitSize * (B ∩ support).ncard
    have hunion_ncard : (⋃ C ∈ blockOrbit σ B, C ∩ ↑σ.support).ncard =
        blockOrbitSize σ B * (B ∩ ↑σ.support).ncard := by
      rw [Set.Finite.ncard_biUnion hOrbitFin hFinInter hDisjOrbit]
      rw [finsum_mem_eq_finite_toFinset_sum _ hOrbitFin]
      rw [Finset.sum_eq_card_nsmul (b := (B ∩ ↑σ.support).ncard)]
      · simp only [smul_eq_mul]
        unfold blockOrbitSize
        rw [Set.ncard_eq_toFinset_card _ hOrbitFin]
      · intro C hC
        simp only [Set.Finite.mem_toFinset] at hC
        exact heq_card C hC
    -- Now use: support = ⋃ C ∈ orbit, C ∩ support
    unfold cycleLength
    rw [← Set.ncard_coe_Finset]
    conv_lhs => rw [hpart]
    exact hunion_ncard
  -- Conclude using eq_div_iff
  rw [Nat.eq_div_iff_mul_eq_left hne hdiv, mul_comm]
  exact hprod

-- ============================================
-- MAIN LEMMA
-- ============================================

/-- **Lemma 11.4: Block Orbit**

    Let σ be an ℓ-cycle and B a σ-invariant block system.
    Let B ∈ B with B ∩ supp(σ) ≠ ∅, and let r be the orbit size of B.
    Then:
    1. r divides ℓ
    2. |B ∩ supp(σ)| = ℓ/r -/
theorem lemma11_4_block_orbit {σ : Perm α} (hσ : σ.IsCycle)
    {B : Set α} {Blocks : Set (Set α)} (hInv : BlockSystemInvariant σ Blocks)
    (hB : B ∈ Blocks) (hMeet : (B ∩ (σ.support : Set α)).Nonempty)
    (hDisj : Blocks.PairwiseDisjoint id) :
    blockOrbitSize σ B ∣ cycleLength σ ∧
    (B ∩ (σ.support : Set α)).ncard = cycleLength σ / blockOrbitSize σ B := by
  constructor
  · exact block_orbit_divides_cycle_length hσ hInv hB hMeet
  · exact block_support_intersection_card hσ hInv hB hMeet hDisj
