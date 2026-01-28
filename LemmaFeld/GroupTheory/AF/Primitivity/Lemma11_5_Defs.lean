/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_3
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_4_Defs
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_FixedPoints
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_CycleSupport

/-!
# Lemma 11.5: Block System Definitions

Defines block systems and their properties for the primitivity proof.

## Main Definitions

* `BlockSystemOn`: A block system on Ω with fixed block size
* `IsHInvariant`: Block system preserved by all generators
* `IsNontrivial`: Block system has 1 < blockSize < |Ω|

## Main Results

* `fixed_point_blocks_intersect`: Fixed point creates intersection
* `case1b_impossible`: Case 1b contradiction
* `case2_forces_stabilization`: Case 2 forces g₂, g₃ to preserve B
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

-- ============================================
-- SECTION 1: BLOCK SYSTEM DEFINITIONS
-- ============================================

/-- A block system on Ω with block size d -/
structure BlockSystemOn (n k m : ℕ) where
  blocks : Set (Set (Omega n k m))
  blockSize : ℕ
  isPartition : blocks.PairwiseDisjoint id ∧ ⋃₀ blocks = Set.univ
  allSameSize : ∀ B ∈ blocks, B.ncard = blockSize

/-- A block system is H-invariant if all generators preserve it -/
def IsHInvariant (BS : BlockSystemOn n k m) : Prop :=
  BlockSystemInvariant (g₁ n k m) BS.blocks ∧
  BlockSystemInvariant (g₂ n k m) BS.blocks ∧
  BlockSystemInvariant (g₃ n k m) BS.blocks

/-- A block system is non-trivial if 1 < blockSize < |Ω| -/
def IsNontrivial (BS : BlockSystemOn n k m) : Prop :=
  1 < BS.blockSize ∧ BS.blockSize < 6 + n + k + m

-- ============================================
-- SECTION 2: FIXED POINT INTERSECTION
-- ============================================

/-- If σ fixes x ∈ B and σ(B) ≠ B, then σ(B) ∩ B ≠ ∅ (contradiction) -/
theorem fixed_point_blocks_intersect {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (B : Set α) (x : α) (hx : x ∈ B) (hFix : σ x = x) :
    x ∈ σ '' B ∩ B := by
  refine ⟨?_, hx⟩
  rw [Set.mem_image]
  exact ⟨x, hx, hFix⟩

-- ============================================
-- SECTION 3: CASE 1b IMPOSSIBILITY
-- ============================================

/-- Case 1b impossibility: g₂(B) ≠ B is impossible when supp(g₁) ⊆ B and n ≥ 1 -/
theorem case1b_impossible (hn : n ≥ 1) (B : Set (Omega n k m))
    (hSupp : ((g₁ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₂ n k m '' B) B) : False := by
  -- Element 2 (= "3" in 1-indexed) is in supp(g₁), hence in B
  have h2_in_supp : (⟨2, by omega⟩ : Omega n k m) ∈ (g₁ n k m).support :=
    elem2_in_support_g₁ hn
  have h2_in_B : (⟨2, by omega⟩ : Omega n k m) ∈ B := hSupp h2_in_supp
  -- Element 2 is not in supp(g₂), so g₂(2) = 2
  have hFix : g₂ n k m (⟨2, by omega⟩ : Omega n k m) = ⟨2, by omega⟩ := g₂_fixes_elem2
  -- Therefore 2 ∈ g₂(B) ∩ B
  have h2_in_both := fixed_point_blocks_intersect (g₂ n k m) B _ h2_in_B hFix
  -- This contradicts disjointness
  exact Set.disjoint_iff.mp hDisj h2_in_both

-- ============================================
-- SECTION 4: CASE 2 STABILIZATION
-- ============================================

/-- Case 2: g₁(B) ≠ B forces g₂(B) = B and g₃(B) = B

    Given that B is part of a block system (so non-preservation implies disjointness),
    we show g₂ and g₃ must preserve B by fixed-point arguments. -/
theorem case2_forces_stabilization (hn : n ≥ 1) (B : Set (Omega n k m))
    (hA : a₁ n k m hn ∈ B)
    (h₂Disj : ¬PreservesSet (g₂ n k m) B → Disjoint (g₂ n k m '' B) B)
    (h₃Disj : ¬PreservesSet (g₃ n k m) B → Disjoint (g₃ n k m '' B) B) :
    PreservesSet (g₂ n k m) B ∧ PreservesSet (g₃ n k m) B := by
  constructor
  · -- Prove g₂(B) = B
    by_contra hNotPres
    have hDisj := h₂Disj hNotPres
    -- g₂ fixes a₁ (since a₁ is in tail A, not in supp(g₂))
    have hFix : g₂ n k m (a₁ n k m hn) = a₁ n k m hn := by
      unfold a₁
      exact g₂_fixes_tailA hn ⟨0, hn⟩
    -- Therefore a₁ ∈ g₂(B) ∩ B
    have h_in_both := fixed_point_blocks_intersect (g₂ n k m) B (a₁ n k m hn) hA hFix
    -- This contradicts disjointness
    exact Set.disjoint_iff.mp hDisj h_in_both
  · -- Prove g₃(B) = B (analogous argument)
    by_contra hNotPres
    have hDisj := h₃Disj hNotPres
    -- g₃ fixes a₁ (since a₁ is in tail A, not in supp(g₃))
    have hFix : g₃ n k m (a₁ n k m hn) = a₁ n k m hn := by
      unfold a₁
      exact g₃_fixes_tailA hn ⟨0, hn⟩
    -- Therefore a₁ ∈ g₃(B) ∩ B
    have h_in_both := fixed_point_blocks_intersect (g₃ n k m) B (a₁ n k m hn) hA hFix
    -- This contradicts disjointness
    exact Set.disjoint_iff.mp hDisj h_in_both
