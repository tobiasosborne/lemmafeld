/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_1_Defs
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_1_Size2
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_1_Size3

/-!
# Lemma 11.1: Unique Block System

The only non-trivial block system for H₆ on {1,...,6} is B₀ = {{1,4}, {2,5}, {3,6}}.

## Main Results

* `lemma11_1_unique_block_system`: B₀ is the unique non-trivial block system for H₆

## Proof Outline

1. Block sizes must divide 6, giving |B| ∈ {2, 3}
2. For size 2: There are 15 partitions, only B₀ is H₆-invariant
3. For size 3: There are 10 partitions, none are H₆-invariant (see Lemma11_1_Size3)

## Reference

See `examples/lemmas/lemma11_1_unique_block_system.md` for the natural language proof.
-/

open MulAction Equiv.Perm

-- ============================================
-- SECTION 1: THE BLOCK SYSTEM B₀
-- ============================================

/-- B₀ as a Partition6 structure -/
def B₀_partition : Partition6 where
  blocks := B₀
  blockSize := 2
  size_divides := ⟨3, rfl⟩
  all_same_size := by
    intro B hB
    simp only [B₀, Finset.mem_insert, Finset.mem_singleton] at hB
    rcases hB with rfl | rfl | rfl
    · exact Block1_card
    · exact Block2_card
    · exact Block3_card
  pairwise_disjoint := by
    intro B₁ hB₁ B₂ hB₂ hne
    simp only [B₀, Finset.coe_insert, Finset.coe_singleton,
               Set.mem_insert_iff, Set.mem_singleton_iff] at hB₁ hB₂
    rcases hB₁ with rfl | rfl | rfl <;> rcases hB₂ with rfl | rfl | rfl
    all_goals first
      | exact absurd rfl hne
      | exact Block1_Block2_disjoint
      | exact Block1_Block2_disjoint.symm
      | exact Block1_Block3_disjoint
      | exact Block1_Block3_disjoint.symm
      | exact Block2_Block3_disjoint
      | exact Block2_Block3_disjoint.symm
  covers_all := by
    ext x
    simp only [Finset.mem_sup, B₀, Finset.mem_insert, Finset.mem_singleton,
               id_eq, Finset.mem_univ, iff_true]
    fin_cases x <;> simp [Block1, Block2, Block3]

-- ============================================
-- SECTION 2: SIZE-2 PARTITIONS
-- ============================================

/-- Number of size-2 partitions of Fin 6 into 3 blocks -/
theorem size2_partition_count : ∃ n : ℕ, n = 15 ∧
    n = Nat.choose 6 2 * Nat.choose 4 2 / Nat.factorial 3 := by
  use 15
  constructor
  · rfl
  · native_decide

/-- B₀ is invariant under g₁ (restricted to Fin 6) -/
theorem B₀_invariant_g₁ : ∀ B ∈ B₀, (B.image (g₁ 0 0 0)) ∈ B₀ := by decide

/-- B₀ is invariant under g₂ (restricted to Fin 6) -/
theorem B₀_invariant_g₂ : ∀ B ∈ B₀, (B.image (g₂ 0 0 0)) ∈ B₀ := by decide

/-- B₀ is invariant under g₃ (restricted to Fin 6) -/
theorem B₀_invariant_g₃ : ∀ B ∈ B₀, (B.image (g₃ 0 0 0)) ∈ B₀ := by decide

-- ============================================
-- SECTION 3: MAIN THEOREM
-- ============================================

/-- Helper: g preserves B₀ if all blocks map to blocks -/
def preservesB₀ (g : Equiv.Perm (Fin 6)) : Prop :=
  ∀ B ∈ B₀, (B.image g) ∈ B₀

/-- preservesB₀ is decidable -/
instance : DecidablePred preservesB₀ := fun g =>
  inferInstanceAs (Decidable (∀ B ∈ B₀, (B.image g) ∈ B₀))

/-- 1 preserves B₀ -/
theorem one_preservesB₀ : preservesB₀ 1 := by decide

/-- If g preserves B₀, so does g⁻¹ -/
theorem inv_preservesB₀ (g : Equiv.Perm (Fin 6)) (h : preservesB₀ g) : preservesB₀ g⁻¹ :=
  LemmaFeld.GroupTheory.AF.BaseCase.inv_preserves_B₀ g h

/-- If g and h preserve B₀, so does g * h -/
theorem mul_preservesB₀ (g h : Equiv.Perm (Fin 6))
    (hg : preservesB₀ g) (hh : preservesB₀ h) : preservesB₀ (g * h) := by
  intro B hB
  have hB' := hh B hB
  have := hg (B.image h) hB'
  simp only [Equiv.Perm.coe_mul, Finset.image_image] at this ⊢
  exact this

/-- All elements of H₆ preserve B₀ -/
theorem H₆_preservesB₀ : ∀ g ∈ H₆, preservesB₀ g := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact B₀_invariant_g₁
    · exact B₀_invariant_g₂
    · exact B₀_invariant_g₃
  | one => exact one_preservesB₀
  | mul _ _ _ _ ihx ihy => exact mul_preservesB₀ _ _ ihx ihy
  | inv _ _ ih => exact inv_preservesB₀ _ ih

/-- B₀ is a block system for H₆ -/
theorem B₀_is_block_system : IsBlockSystem B₀_partition := by
  intro g hg B hB
  exact H₆_preservesB₀ g hg B hB

/-- B₀ is a non-trivial block system -/
theorem B₀_nontrivial : IsNontrivialBlockSystem B₀_partition := by
  constructor
  · exact B₀_is_block_system
  · constructor <;> decide

/-- **Lemma 11.1: Unique Block System**

    The only non-trivial block system for H₆ on Fin 6 is B₀.
    Any non-trivial partition preserved by H₆ must be B₀. -/
theorem lemma11_1_unique_block_system (P : Partition6) :
    IsNontrivialBlockSystem P → P.blocks = B₀ := by
  intro ⟨hBS, hLower, hUpper⟩
  -- P.blockSize ∈ {2, 3} since it divides 6 and 1 < size < 6
  have hSize : P.blockSize = 2 ∨ P.blockSize = 3 := by
    have hdiv := P.size_divides
    interval_cases P.blockSize <;> simp_all
  rcases hSize with hSize2 | hSize3
  · -- Size 2 case: only B₀ works
    exact size2_unique_block_system P hBS hSize2
  · -- Size 3 case: contradiction, no such block system exists
    exact absurd hBS (no_size3_block_system P hSize3)
