/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_2
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_3
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_FixedPoints
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_CycleSupport

/-!
# Lemma 11.5: Case Analysis Helpers

Helper lemmas for the case analysis in Lemma 11.5, proving that H admits
no non-trivial block system.

## Main Results

* `perm_image_preserves_or_disjoint`: In a pairwise disjoint block system,
  σ '' B either equals B or is disjoint from B
* `case1a_ii_impossible`: Case 1a-ii leads to contradiction

## Reference

See `examples/lemmas/lemma11_5_no_nontrivial_blocks.md` for the full proof.
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

-- ============================================
-- SECTION 1: BLOCK SYSTEM BRIDGE LEMMAS
-- ============================================

/-- In a pairwise disjoint block system, if B and σ '' B are both blocks,
    then either σ '' B = B or they are disjoint -/
theorem perm_image_preserves_or_disjoint {α : Type*}
    (σ : Perm α) (B : Set α) (Blocks : Set (Set α))
    (hDisj : Blocks.PairwiseDisjoint id) (hB : B ∈ Blocks) (hσB : σ '' B ∈ Blocks) :
    σ '' B = B ∨ Disjoint (σ '' B) B := by
  by_cases h : σ '' B = B
  · left; exact h
  · right
    apply hDisj hσB hB h

/-- Contrapositive: if σ '' B ∩ B is nonempty, then σ '' B = B -/
theorem perm_image_eq_of_meet_nonempty {α : Type*}
    (σ : Perm α) (B : Set α) (Blocks : Set (Set α))
    (hDisj : Blocks.PairwiseDisjoint id) (hB : B ∈ Blocks) (hσB : σ '' B ∈ Blocks)
    (hMeet : (σ '' B ∩ B).Nonempty) : σ '' B = B := by
  rcases perm_image_preserves_or_disjoint σ B Blocks hDisj hB hσB with h | h
  · exact h
  · exfalso
    obtain ⟨x, hx⟩ := hMeet
    exact Set.disjoint_iff.mp h hx

/-- Block system invariance extends to powers -/
theorem blockSystemInvariant_pow {α : Type*} (σ : Perm α) (Blocks : Set (Set α))
    (hInv : ∀ B ∈ Blocks, σ '' B ∈ Blocks) (j : ℕ) (B : Set α) (hB : B ∈ Blocks) :
    (σ ^ j) '' B ∈ Blocks := by
  induction j with
  | zero => simp [hB]
  | succ j' ih =>
    rw [pow_succ', Equiv.Perm.coe_mul, Set.image_comp]
    exact hInv _ ih

/-- Block dichotomy extends to powers -/
theorem perm_pow_image_preserves_or_disjoint {α : Type*}
    (σ : Perm α) (B : Set α) (Blocks : Set (Set α))
    (hDisj : Blocks.PairwiseDisjoint id) (hB : B ∈ Blocks)
    (hInv : ∀ B ∈ Blocks, σ '' B ∈ Blocks) (j : ℕ) :
    (σ ^ j) '' B = B ∨ Disjoint ((σ ^ j) '' B) B := by
  have h := blockSystemInvariant_pow σ Blocks hInv j B hB
  exact perm_image_preserves_or_disjoint (σ ^ j) B Blocks hDisj hB h

/-- Convert between PreservesSet and set equality -/
theorem preservesSet_iff_image_eq {α : Type*} [Fintype α]
    (σ : Perm α) (B : Set α) : PreservesSet σ B ↔ σ '' B = B := Iff.rfl

/-- If σ fixes x ∈ B, then x ∈ σ '' B ∩ B -/
theorem fixed_point_in_image_inter {α : Type*}
    (σ : Perm α) (B : Set α) (x : α) (hx : x ∈ B) (hFix : σ x = x) :
    x ∈ σ '' B ∩ B := by
  refine ⟨?_, hx⟩
  rw [Set.mem_image]
  exact ⟨x, hx, hFix⟩

-- ============================================
-- SECTION 2: CASE 1a-ii IMPOSSIBILITY
-- ============================================

/-- Case 1a-ii impossibility: g₃(B) ≠ B is impossible when element 0 ∈ B
    because g₃ fixes element 0 (not in supp(g₃)), creating intersection -/
theorem case1a_ii_impossible (B : Set (Omega n k m))
    (h0_in_B : (⟨0, by omega⟩ : Omega n k m) ∈ B)
    (hDisj : Disjoint (g₃ n k m '' B) B) : False := by
  -- Element 0 is fixed by g₃ (not in supp(g₃))
  have hFix : g₃ n k m (⟨0, by omega⟩ : Omega n k m) = ⟨0, by omega⟩ := g₃_fixes_elem0
  -- Therefore 0 ∈ g₃(B) ∩ B
  have h0_in_both := fixed_point_in_image_inter (g₃ n k m) B _ h0_in_B hFix
  -- This contradicts disjointness
  exact Set.disjoint_iff.mp hDisj h0_in_both
