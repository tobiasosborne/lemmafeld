/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.ThreeCycle.Case2ProductLemmas
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma06

/-!
# Commutator Lemmas for Case 2: k ≥ 1

This file contains c₁₂ action lemmas and iterated commutator lemmas for k ≥ 1.

## Key Discovery

The specific 3-cycle produced by (iteratedComm_g₂')² depends on n:
- For n = 0: the 3-cycle is (1, 2, 3)
- For n ≥ 1: the 3-cycle is (1, 3, 5+n) where 5+n is the last tailA element

This file provides the lemmas needed for the n = 0 case.
-/

open Equiv Perm

namespace LemmaFeld.GroupTheory.AF.Case2CommutatorLemmas

open Case2ProductLemmas

-- ============================================
-- SECTION 1: c₁₂ actions on {1, 3, 5} (valid for all n, k)
-- ============================================

/-- c₁₂(1) = 3: g₂(1)=3, g₁(3)=2, g₂⁻¹(2)=2, g₁⁻¹(2)=3 -/
theorem c₁₂_1_eq_3 (n k m : ℕ) : commutator_g₁_g₂ n k m ⟨1, by omega⟩ = ⟨3, by omega⟩ := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  rw [g₂_1_eq_3, g₁_3_eq_2, g₂_inv_fixes_2, g₁_inv_2_eq_3]

/-- c₁₂(3) = 5: g₂(3)=4, g₁(4)=4, g₂⁻¹(4)=3, g₁⁻¹(3)=5 -/
theorem c₁₂_3_eq_5 (n k m : ℕ) : commutator_g₁_g₂ n k m ⟨3, by omega⟩ = ⟨5, by omega⟩ := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  rw [g₂_3_eq_4, g₁_fixes_4, g₂_inv_4_eq_3, g₁_inv_3_eq_5]

/-- c₁₂(5) = 1: g₂(5)=5, g₁(5)=3, g₂⁻¹(3)=1, g₁⁻¹(1)=1 -/
theorem c₁₂_5_eq_1 (n k m : ℕ) : commutator_g₁_g₂ n k m ⟨5, by omega⟩ = ⟨1, by omega⟩ := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  rw [g₂_fixes_5, g₁_5_eq_3, g₂_inv_3_eq_1, g₁_inv_fixes_1]

-- c₁₂⁻¹ lemmas
theorem c₁₂_inv_3_eq_1 (n k m : ℕ) : (commutator_g₁_g₂ n k m)⁻¹ ⟨3, by omega⟩ = ⟨1, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (c₁₂_1_eq_3 n k m).symm

theorem c₁₂_inv_5_eq_3 (n k m : ℕ) : (commutator_g₁_g₂ n k m)⁻¹ ⟨5, by omega⟩ = ⟨3, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (c₁₂_3_eq_5 n k m).symm

theorem c₁₂_inv_1_eq_5 (n k m : ℕ) : (commutator_g₁_g₂ n k m)⁻¹ ⟨1, by omega⟩ = ⟨5, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (c₁₂_5_eq_1 n k m).symm

-- ============================================
-- SECTION 2: c₁₂(4) = 0 (valid for all n, k)
-- ============================================

/-- c₁₂(4) = 0: g₂(4)=0, g₁(0)=5, g₂⁻¹(5)=5, g₁⁻¹(5)=0 -/
theorem c₁₂_4_eq_0 (n k m : ℕ) : commutator_g₁_g₂ n k m ⟨4, by omega⟩ = ⟨0, by omega⟩ := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  rw [g₂_4_eq_0, g₁_0_eq_5, g₂_inv_fixes_5, g₁_inv_5_eq_0]

theorem c₁₂_inv_0_eq_4 (n k m : ℕ) : (commutator_g₁_g₂ n k m)⁻¹ ⟨0, by omega⟩ = ⟨4, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (c₁₂_4_eq_0 n k m).symm

-- ============================================
-- SECTION 3: iter(1) = 3 (valid for all n, k ≥ 1)
-- ============================================

/-- iter(1) = 3: g₂(1)=3, c₁₂(3)=5, g₂⁻¹(5)=5, c₁₂⁻¹(5)=3 -/
theorem iter_1_eq_3 (n k m : ℕ) :
    SymmetricCase2.iteratedComm_g₂' n k m ⟨1, by omega⟩ = ⟨3, by omega⟩ := by
  unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
  rw [g₂_1_eq_3, c₁₂_3_eq_5, g₂_inv_fixes_5, c₁₂_inv_5_eq_3]

-- ============================================
-- SECTION 4: Additional lemmas for n = 0 case
-- ============================================

-- When n = 0, g₁ has no tailA, so g₁(2) = 0
-- This affects c₁₂(2) and the cycle structure

/-- g₁(2) = 0 when n = 0 (cycle wraps from 2 back to 0) -/
theorem g₁_2_eq_0_n0 (k m : ℕ) : g₁ 0 k m ⟨2, by omega⟩ = ⟨0, by omega⟩ := by
  unfold g₁
  have hnd := g₁_list_nodup 0 k m
  have hlen := g₁_cycle_length 0 k m
  -- For n = 0, tailA is empty, so the list is just [0, 5, 3, 2]
  have htail_empty : tailAList 0 k m = [] := by
    unfold tailAList List.finRange; rfl
  simp only [htail_empty, List.append_nil]
  -- Position 3 (element 2) maps to position 0 (element 0)
  have h_fp := List.formPerm_apply_getElem _ (g₁CoreList_nodup 0 k m) 3 (by simp [g₁CoreList])
  simp only [g₁CoreList, List.length_cons, List.length_nil, Nat.reduceAdd,
    show (3 + 1) % 4 = 0 by native_decide,
    List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  exact h_fp

theorem g₁_inv_0_eq_2_n0 (k m : ℕ) : (g₁ 0 k m)⁻¹ ⟨0, by omega⟩ = ⟨2, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₁_2_eq_0_n0 k m).symm

/-- c₁₂(2) = 4 when n = 0: g₂(2)=2, g₁(2)=0, g₂⁻¹(0)=4, g₁⁻¹(4)=4 -/
theorem c₁₂_2_eq_4_n0 (k m : ℕ) : commutator_g₁_g₂ 0 k m ⟨2, by omega⟩ = ⟨4, by omega⟩ := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  rw [g₂_fixes_2, g₁_2_eq_0_n0, g₂_inv_0_eq_4, g₁_inv_fixes_4]

theorem c₁₂_inv_4_eq_2_n0 (k m : ℕ) : (commutator_g₁_g₂ 0 k m)⁻¹ ⟨4, by omega⟩ = ⟨2, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (c₁₂_2_eq_4_n0 k m).symm

/-- iter(3) = 2 when n = 0: g₂(3)=4, c₁₂(4)=0, g₂⁻¹(0)=4, c₁₂⁻¹(4)=2 -/
theorem iter_3_eq_2_n0 (k m : ℕ) :
    SymmetricCase2.iteratedComm_g₂' 0 k m ⟨3, by omega⟩ = ⟨2, by omega⟩ := by
  unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
  rw [g₂_3_eq_4, c₁₂_4_eq_0, g₂_inv_0_eq_4, c₁₂_inv_4_eq_2_n0]

/-- iter(2) = 1 when n = 0: g₂(2)=2, c₁₂(2)=4, g₂⁻¹(4)=3, c₁₂⁻¹(3)=1 -/
theorem iter_2_eq_1_n0 (k m : ℕ) :
    SymmetricCase2.iteratedComm_g₂' 0 k m ⟨2, by omega⟩ = ⟨1, by omega⟩ := by
  unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
  rw [g₂_fixes_2, c₁₂_2_eq_4_n0, g₂_inv_4_eq_3, c₁₂_inv_3_eq_1]

-- ============================================
-- SECTION 5: Squared action lemmas for n = 0
-- ============================================

/-- sq(1) = 2 when n = 0: iter(iter(1)) = iter(3) = 2 -/
theorem sq_1_eq_2_n0 (k m : ℕ) :
    (SymmetricCase2.iteratedComm_g₂' 0 k m ^ 2) ⟨1, by omega⟩ = ⟨2, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [iter_1_eq_3, iter_3_eq_2_n0]

/-- sq(2) = 3 when n = 0: iter(iter(2)) = iter(1) = 3 -/
theorem sq_2_eq_3_n0 (k m : ℕ) :
    (SymmetricCase2.iteratedComm_g₂' 0 k m ^ 2) ⟨2, by omega⟩ = ⟨3, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [iter_2_eq_1_n0, iter_1_eq_3]

/-- sq(3) = 1 when n = 0: iter(iter(3)) = iter(2) = 1 -/
theorem sq_3_eq_1_n0 (k m : ℕ) :
    (SymmetricCase2.iteratedComm_g₂' 0 k m ^ 2) ⟨3, by omega⟩ = ⟨1, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [iter_3_eq_2_n0, iter_2_eq_1_n0]

-- ============================================
-- SECTION 6: Lemmas for n ≥ 1 case
-- ============================================

/-- g₁(5+n) = 0 for n ≥ 1: last tailA element wraps to start of cycle -/
theorem g₁_5plusn_eq_0 (n k m : ℕ) (hn : n ≥ 1) :
    g₁ n k m ⟨5 + n, by omega⟩ = ⟨0, by omega⟩ := by
  unfold g₁
  have h := List.formPerm_apply_getLast (⟨0, by omega⟩ : Omega n k m)
              (⟨5, by omega⟩ :: ⟨3, by omega⟩ :: ⟨2, by omega⟩ ::
               (tailAList n k m : List (Omega n k m)))
  simp only [g₁CoreList, List.cons_append, List.nil_append] at h ⊢
  convert h using 2
  have hne : tailAList n k m ≠ [] := by unfold tailAList; simp [List.map_eq_nil_iff]; omega
  rw [List.getLast_cons_cons, List.getLast_cons_cons, List.getLast_cons_cons,
      List.getLast_cons hne]
  unfold tailAList
  rw [List.getLast_map (by simp; omega)]
  have hlen : (List.finRange n).length = n := List.length_finRange
  have hidx : n - 1 < (List.finRange n).length := by rw [hlen]; omega
  have hlast : ∀ h, (List.finRange n).getLast h = (List.finRange n)[n - 1]'hidx := by
    intro h; rw [List.getLast_eq_getElem]; congr 1; rw [hlen]
  rw [hlast, List.getElem_finRange]; simp only [Fin.ext_iff, Fin.coe_cast]; omega

theorem g₁_inv_0_eq_5plusn (n k m : ℕ) (hn : n ≥ 1) :
    (g₁ n k m)⁻¹ ⟨0, by omega⟩ = ⟨5 + n, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₁_5plusn_eq_0 n k m hn).symm

/-- c₁₂(5+n) = 4 for n ≥ 1: g₂(5+n)=5+n, g₁(5+n)=0, g₂⁻¹(0)=4, g₁⁻¹(4)=4 -/
theorem c₁₂_5plusn_eq_4 (n k m : ℕ) (hn : n ≥ 1) :
    commutator_g₁_g₂ n k m ⟨5 + n, by omega⟩ = ⟨4, by omega⟩ := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  -- g₂ fixes 5+n (it's in tailA, not in g₂'s cycle)
  have hg₂_fix : g₂ n k m ⟨5 + n, by omega⟩ = ⟨5 + n, by omega⟩ := by
    unfold g₂; apply List.formPerm_apply_of_notMem
    simp only [g₂CoreList, tailBList, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map, List.mem_finRange, not_or]
    constructor
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
    · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega
  rw [hg₂_fix, g₁_5plusn_eq_0 n k m hn, g₂_inv_0_eq_4, g₁_inv_fixes_4]

theorem c₁₂_inv_4_eq_5plusn (n k m : ℕ) (hn : n ≥ 1) :
    (commutator_g₁_g₂ n k m)⁻¹ ⟨4, by omega⟩ = ⟨5 + n, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (c₁₂_5plusn_eq_4 n k m hn).symm

/-- iter(3) = 5+n for n ≥ 1: g₂(3)=4, c₁₂(4)=0, g₂⁻¹(0)=4, c₁₂⁻¹(4)=5+n -/
theorem iter_3_eq_5plusn (n k m : ℕ) (hn : n ≥ 1) :
    SymmetricCase2.iteratedComm_g₂' n k m ⟨3, by omega⟩ = ⟨5 + n, by omega⟩ := by
  unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
  rw [g₂_3_eq_4, c₁₂_4_eq_0, g₂_inv_0_eq_4, c₁₂_inv_4_eq_5plusn n k m hn]

/-- iter(5+n) = 1 for n ≥ 1: g₂(5+n)=5+n, c₁₂(5+n)=4, g₂⁻¹(4)=3, c₁₂⁻¹(3)=1 -/
theorem iter_5plusn_eq_1 (n k m : ℕ) (hn : n ≥ 1) :
    SymmetricCase2.iteratedComm_g₂' n k m ⟨5 + n, by omega⟩ = ⟨1, by omega⟩ := by
  unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
  have hg₂_fix : g₂ n k m ⟨5 + n, by omega⟩ = ⟨5 + n, by omega⟩ := by
    unfold g₂; apply List.formPerm_apply_of_notMem
    simp only [g₂CoreList, tailBList, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map, List.mem_finRange, not_or]
    constructor
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
    · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega
  rw [hg₂_fix, c₁₂_5plusn_eq_4 n k m hn, g₂_inv_4_eq_3, c₁₂_inv_3_eq_1]

-- Squared action lemmas for n ≥ 1
-- The 3-cycle is (1, 5+n, 3): 1→5+n→3→1
theorem sq_1_eq_5plusn_n_ge1 (n k m : ℕ) (hn : n ≥ 1) :
    (SymmetricCase2.iteratedComm_g₂' n k m ^ 2) ⟨1, by omega⟩ = ⟨5 + n, by omega⟩ := by
  simp only [sq, Perm.mul_apply]; rw [iter_1_eq_3, iter_3_eq_5plusn n k m hn]

theorem sq_5plusn_eq_3_n_ge1 (n k m : ℕ) (hn : n ≥ 1) :
    (SymmetricCase2.iteratedComm_g₂' n k m ^ 2) ⟨5 + n, by omega⟩ = ⟨3, by omega⟩ := by
  simp only [sq, Perm.mul_apply]; rw [iter_5plusn_eq_1 n k m hn, iter_1_eq_3]

theorem sq_3_eq_1_n_ge1 (n k m : ℕ) (hn : n ≥ 1) :
    (SymmetricCase2.iteratedComm_g₂' n k m ^ 2) ⟨3, by omega⟩ = ⟨1, by omega⟩ := by
  simp only [sq, Perm.mul_apply]; rw [iter_3_eq_5plusn n k m hn, iter_5plusn_eq_1 n k m hn]

end LemmaFeld.GroupTheory.AF.Case2CommutatorLemmas
