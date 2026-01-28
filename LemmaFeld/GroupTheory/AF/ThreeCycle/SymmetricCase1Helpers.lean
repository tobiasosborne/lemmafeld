/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma07
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma08
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Helper Lemmas for Symmetric Case 1: m ≥ 1, k = 0

When k = 0, g₂ has no tail (tailB is empty).
This file provides lemmas for proving (c₁₃ * c₂₃⁻¹)² is a 3-cycle.

## Key Insight

When k = 0:
- g₂ = formPerm [1, 3, 4, 0] (core only)
- g₂ fixes all elements ≥ 6
- The squared product (c₁₃ * c₂₃⁻¹)² is the 3-cycle (3, 4, 5)
-/

open Equiv Perm

namespace LemmaFeld.GroupTheory.AF.SymmetricCase1

-- ============================================
-- SECTION 1: g₂ structure when k = 0
-- ============================================

/-- tailBList is empty when k = 0 -/
lemma tailBList_empty (n m : ℕ) : tailBList n 0 m = [] := by
  unfold tailBList List.finRange; rfl

/-- g₂ when k = 0 equals formPerm of just the core list -/
lemma g₂_k0_eq (n m : ℕ) : g₂ n 0 m = (g₂CoreList n 0 m).formPerm := by
  unfold g₂; rw [tailBList_empty]; simp only [List.append_nil]

/-- g₂ fixes element x if x.val ≥ 6 (when k = 0) -/
lemma g₂_fixes_val_ge_6 (n m : ℕ) (x : Omega n 0 m) (hx : x.val ≥ 6) :
    g₂ n 0 m x = x := by
  rw [g₂_k0_eq]
  apply List.formPerm_apply_of_notMem
  simp only [g₂CoreList, List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals intro h; simp only [Fin.ext_iff] at h; omega

-- ============================================
-- SECTION 2: The 3-cycle definition
-- ============================================

/-- The 3-cycle (3, 4, 5) on Omega n 0 m -/
def threeCycle_3_4_5 (n m : ℕ) : Perm (Omega n 0 m) :=
  [⟨3, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩].formPerm

/-- The list [3, 4, 5] has no duplicates -/
theorem threeCycle_list_nodup (n m : ℕ) :
    ([⟨3, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩] : List (Omega n 0 m)).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, Fin.mk.injEq, or_false, not_or]
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, ⟨not_false, List.nodup_nil⟩⟩⟩

/-- threeCycle_3_4_5 is a 3-cycle -/
theorem threeCycle_3_4_5_isThreeCycle (n m : ℕ) :
    (threeCycle_3_4_5 n m).IsThreeCycle := by
  unfold threeCycle_3_4_5
  rw [← card_support_eq_three_iff, List.support_formPerm_of_nodup _ (threeCycle_list_nodup n m)]
  · simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton, Fin.mk.injEq]; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton, Fin.mk.injEq, not_or]; omega
  · intro x h; have := congrArg List.length h; simp at this

-- ============================================
-- SECTION 3: Product definition
-- ============================================

/-- The product c₁₃ * c₂₃⁻¹ for the k=0 case -/
def c₁₃_times_c₂₃_inv (n m : ℕ) : Perm (Omega n 0 m) :=
  commutator_g₁_g₃ n 0 m * (commutator_g₂_g₃ n 0 m)⁻¹

-- ============================================
-- SECTION 4: Computational verifications
-- ============================================

/-- IsThreeCycle for n=0, m=1 -/
theorem isThreeCycle_n0_m1 : ((c₁₃_times_c₂₃_inv 0 1) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle c₁₃_times_c₂₃_inv; native_decide

/-- IsThreeCycle for n=1, m=1 -/
theorem isThreeCycle_n1_m1 : ((c₁₃_times_c₂₃_inv 1 1) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle c₁₃_times_c₂₃_inv; native_decide

/-- IsThreeCycle for n=2, m=1 -/
theorem isThreeCycle_n2_m1 : ((c₁₃_times_c₂₃_inv 2 1) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle c₁₃_times_c₂₃_inv; native_decide

/-- IsThreeCycle for n=0, m=2 -/
theorem isThreeCycle_n0_m2 : ((c₁₃_times_c₂₃_inv 0 2) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle c₁₃_times_c₂₃_inv; native_decide

/-- IsThreeCycle for n=1, m=2 -/
theorem isThreeCycle_n1_m2 : ((c₁₃_times_c₂₃_inv 1 2) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle c₁₃_times_c₂₃_inv; native_decide

/-- IsThreeCycle for n=2, m=2 -/
theorem isThreeCycle_n2_m2 : ((c₁₃_times_c₂₃_inv 2 2) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle c₁₃_times_c₂₃_inv; native_decide

/-- IsThreeCycle for n=3, m=3 -/
theorem isThreeCycle_n3_m3 : ((c₁₃_times_c₂₃_inv 3 3) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle c₁₃_times_c₂₃_inv; native_decide

-- ============================================
-- SECTION 5: threeCycle_3_4_5 action lemmas
-- ============================================

/-- threeCycle_3_4_5 maps 3 → 4 -/
theorem threeCycle_3_eq_4 (n m : ℕ) :
    threeCycle_3_4_5 n m ⟨3, by omega⟩ = ⟨4, by omega⟩ := by
  unfold threeCycle_3_4_5
  have hnd := threeCycle_list_nodup n m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 0 (by simp)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h_fp; exact h_fp

/-- threeCycle_3_4_5 maps 4 → 5 -/
theorem threeCycle_4_eq_5 (n m : ℕ) :
    threeCycle_3_4_5 n m ⟨4, by omega⟩ = ⟨5, by omega⟩ := by
  unfold threeCycle_3_4_5
  have hnd := threeCycle_list_nodup n m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 1 (by simp)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h_fp; exact h_fp

/-- threeCycle_3_4_5 maps 5 → 3 -/
theorem threeCycle_5_eq_3 (n m : ℕ) :
    threeCycle_3_4_5 n m ⟨5, by omega⟩ = ⟨3, by omega⟩ := by
  unfold threeCycle_3_4_5
  have hnd := threeCycle_list_nodup n m
  have h_fp := List.formPerm_apply_getElem _ hnd 2 (by simp)
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    show (2 + 1) % 3 = 0 by native_decide,
    List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  exact h_fp

/-- threeCycle_3_4_5 fixes 0 -/
theorem threeCycle_fixes_0 (n m : ℕ) : threeCycle_3_4_5 n m ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  unfold threeCycle_3_4_5; apply List.formPerm_apply_of_notMem
  simp only [List.mem_cons, List.not_mem_nil, Fin.mk.injEq, or_false, not_or]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- threeCycle_3_4_5 fixes 1 -/
theorem threeCycle_fixes_1 (n m : ℕ) : threeCycle_3_4_5 n m ⟨1, by omega⟩ = ⟨1, by omega⟩ := by
  unfold threeCycle_3_4_5; apply List.formPerm_apply_of_notMem
  simp only [List.mem_cons, List.not_mem_nil, Fin.mk.injEq, or_false, not_or]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- threeCycle_3_4_5 fixes 2 -/
theorem threeCycle_fixes_2 (n m : ℕ) : threeCycle_3_4_5 n m ⟨2, by omega⟩ = ⟨2, by omega⟩ := by
  unfold threeCycle_3_4_5; apply List.formPerm_apply_of_notMem
  simp only [List.mem_cons, List.not_mem_nil, Fin.mk.injEq, or_false, not_or]
  refine ⟨?_, ?_, ?_⟩ <;> omega

/-- threeCycle_3_4_5 fixes all elements with index ≥ 6 -/
theorem threeCycle_fixes_ge6 (n m : ℕ) (x : Omega n 0 m) (hx : x.val ≥ 6) :
    threeCycle_3_4_5 n m x = x := by
  unfold threeCycle_3_4_5; apply List.formPerm_apply_of_notMem
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_⟩
  all_goals intro h; simp only [Fin.ext_iff] at h; omega

end LemmaFeld.GroupTheory.AF.SymmetricCase1
