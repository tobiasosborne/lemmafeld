/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma09
import LemmaFeld.GroupTheory.AF.ThreeCycle.ThreeCycleExtractHelpers
import LemmaFeld.GroupTheory.AF.ThreeCycle.TailLemmas
import LemmaFeld.GroupTheory.AF.ThreeCycle.ProductLemmas

/-!
# Three-Cycle Extraction Proof

Proves that (c₁₂ * c₁₃⁻¹)² is a 3-cycle for all n ≥ 1, k when m = 0.

## Main Result

* `sq_isThreeCycle_n_ge1_m0` - The squared product is a 3-cycle

## Strategy

The proof shows that the squared product equals `threeCycle_0_5_1 n k`, which is
already proven to be a 3-cycle in ThreeCycleExtractHelpers.

The equality is proven by showing both permutations agree on all elements:
- Core elements {0,1,2,3,4,5}: Determined by generator structure
- Tail elements ≥ 6: Fixed by structural argument (see TailLemmas)
-/

open Equiv Perm

namespace LemmaFeld.GroupTheory.AF.ThreeCycleProof

-- ============================================
-- SECTION 1: Structural Lemmas
-- ============================================

/-- threeCycle_0_5_1 fixes all elements with index ≥ 6 -/
theorem threeCycle_fixes_ge6 (n k : ℕ) (x : Omega n k 0) (hx : x.val ≥ 6) :
    ThreeCycleExtract.threeCycle_0_5_1 n k x = x := by
  unfold ThreeCycleExtract.threeCycle_0_5_1
  apply List.formPerm_apply_of_notMem
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_⟩
  all_goals intro h; simp only [Fin.ext_iff] at h; omega

/-- threeCycle_0_5_1 fixes element 2 -/
theorem threeCycle_fixes_2 (n k : ℕ) :
    ThreeCycleExtract.threeCycle_0_5_1 n k ⟨2, by omega⟩ = ⟨2, by omega⟩ := by
  unfold ThreeCycleExtract.threeCycle_0_5_1
  apply List.formPerm_apply_of_notMem
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_⟩; all_goals simp only [Fin.mk.injEq]; omega

/-- threeCycle_0_5_1 fixes element 3 -/
theorem threeCycle_fixes_3 (n k : ℕ) :
    ThreeCycleExtract.threeCycle_0_5_1 n k ⟨3, by omega⟩ = ⟨3, by omega⟩ := by
  unfold ThreeCycleExtract.threeCycle_0_5_1
  apply List.formPerm_apply_of_notMem
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_⟩; all_goals simp only [Fin.mk.injEq]; omega

/-- threeCycle_0_5_1 fixes element 4 -/
theorem threeCycle_fixes_4 (n k : ℕ) :
    ThreeCycleExtract.threeCycle_0_5_1 n k ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
  unfold ThreeCycleExtract.threeCycle_0_5_1
  apply List.formPerm_apply_of_notMem
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_⟩; all_goals simp only [Fin.mk.injEq]; omega

/-- threeCycle_0_5_1 maps 0 → 5 -/
theorem threeCycle_0_eq_5 (n k : ℕ) :
    ThreeCycleExtract.threeCycle_0_5_1 n k ⟨0, by omega⟩ = ⟨5, by omega⟩ := by
  unfold ThreeCycleExtract.threeCycle_0_5_1
  have hnd := ThreeCycleExtract.threeCycle_list_nodup n k
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 0 (by simp)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h_fp; exact h_fp

/-- threeCycle_0_5_1 maps 5 → 1 -/
theorem threeCycle_5_eq_1 (n k : ℕ) :
    ThreeCycleExtract.threeCycle_0_5_1 n k ⟨5, by omega⟩ = ⟨1, by omega⟩ := by
  unfold ThreeCycleExtract.threeCycle_0_5_1
  have hnd := ThreeCycleExtract.threeCycle_list_nodup n k
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 1 (by simp)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h_fp; exact h_fp

/-- threeCycle_0_5_1 maps 1 → 0 -/
theorem threeCycle_1_eq_0 (n k : ℕ) :
    ThreeCycleExtract.threeCycle_0_5_1 n k ⟨1, by omega⟩ = ⟨0, by omega⟩ := by
  unfold ThreeCycleExtract.threeCycle_0_5_1
  have hnd := ThreeCycleExtract.threeCycle_list_nodup n k
  have h_fp := List.formPerm_apply_getElem _ hnd 2 (by simp)
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    show (2 + 1) % (0 + 1 + 1 + 1) = 0 by native_decide,
    List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  exact h_fp

-- ============================================
-- SECTION 2: Squared actions on core elements
-- ============================================

/-- (c₁₂ * c₁₃⁻¹)²(0) = 5 -/
theorem sq_0_eq_5 (n k : ℕ) :
    (c₁₂_times_c₁₃_inv n k 0 ^ 2) ⟨0, by omega⟩ = ⟨5, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [ProductLemmas.product_0_eq_1, ProductLemmas.product_1_eq_5]

/-- (c₁₂ * c₁₃⁻¹)²(1) = 0 -/
theorem sq_1_eq_0 (n k : ℕ) :
    (c₁₂_times_c₁₃_inv n k 0 ^ 2) ⟨1, by omega⟩ = ⟨0, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [ProductLemmas.product_1_eq_5, ProductLemmas.product_5_eq_0]

/-- (c₁₂ * c₁₃⁻¹)²(2) = 2 (requires n ≥ 1) -/
theorem sq_2_eq_2 (n k : ℕ) (hn : n ≥ 1) :
    (c₁₂_times_c₁₃_inv n k 0 ^ 2) ⟨2, by omega⟩ = ⟨2, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [ProductLemmas.product_2_eq_3 n k hn, ProductLemmas.product_3_eq_2 n k hn]

/-- (c₁₂ * c₁₃⁻¹)²(3) = 3 (requires n ≥ 1) -/
theorem sq_3_eq_3 (n k : ℕ) (hn : n ≥ 1) :
    (c₁₂_times_c₁₃_inv n k 0 ^ 2) ⟨3, by omega⟩ = ⟨3, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [ProductLemmas.product_3_eq_2 n k hn, ProductLemmas.product_2_eq_3 n k hn]

/-- (c₁₂ * c₁₃⁻¹)²(4) = 4 (requires n ≥ 1) -/
theorem sq_4_eq_4 (n k : ℕ) (hn : n ≥ 1) :
    (c₁₂_times_c₁₃_inv n k 0 ^ 2) ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [TailALast.product_4_eq_last_tailA n k hn, TailALast.product_last_tailA_eq_4 n k hn]

/-- (c₁₂ * c₁₃⁻¹)²(5) = 1 -/
theorem sq_5_eq_1 (n k : ℕ) :
    (c₁₂_times_c₁₃_inv n k 0 ^ 2) ⟨5, by omega⟩ = ⟨1, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [ProductLemmas.product_5_eq_0, ProductLemmas.product_0_eq_1]

-- ============================================
-- SECTION 3: Tail and Main Theorem
-- ============================================

/-- The squared product fixes all elements with index ≥ 6 -/
theorem sq_fixes_ge6 (n k : ℕ) (hn : n ≥ 1) (x : Omega n k 0) (hx : x.val ≥ 6) :
    (c₁₂_times_c₁₃_inv n k 0 ^ 2) x = x := by
  by_cases hA : x.val < 6 + n
  · exact TailLemmas.sq_fixes_tailA n k hn x ⟨hx, hA⟩
  · push_neg at hA; exact TailLemmas.sq_fixes_tailB n k x hA

/-- The squared product (c₁₂ * c₁₃⁻¹)² equals threeCycle_0_5_1 for all n ≥ 1, k. -/
theorem sq_eq_threeCycle (n k : ℕ) (hn : n ≥ 1) :
    (c₁₂_times_c₁₃_inv n k 0) ^ 2 = ThreeCycleExtract.threeCycle_0_5_1 n k := by
  ext x
  by_cases hcore : x.val < 6
  · -- Core element: action determined by formPerm structure
    interval_cases hv : x.val
    · -- x.val = 0: both map to 5
      have hx : x = ⟨0, by omega⟩ := Fin.ext hv
      rw [hx, sq_0_eq_5 n k, threeCycle_0_eq_5 n k]
    · -- x.val = 1: both map to 0
      have hx : x = ⟨1, by omega⟩ := Fin.ext hv
      rw [hx, sq_1_eq_0 n k, threeCycle_1_eq_0 n k]
    · -- x.val = 2: both fix 2
      have hx : x = ⟨2, by omega⟩ := Fin.ext hv
      rw [hx, sq_2_eq_2 n k hn, threeCycle_fixes_2 n k]
    · -- x.val = 3: both fix 3
      have hx : x = ⟨3, by omega⟩ := Fin.ext hv
      rw [hx, sq_3_eq_3 n k hn, threeCycle_fixes_3 n k]
    · -- x.val = 4: both fix 4
      have hx : x = ⟨4, by omega⟩ := Fin.ext hv
      rw [hx, sq_4_eq_4 n k hn, threeCycle_fixes_4 n k]
    · -- x.val = 5: both map to 1
      have hx : x = ⟨5, by omega⟩ := Fin.ext hv
      rw [hx, sq_5_eq_1 n k, threeCycle_5_eq_1 n k]
  · -- Tail element
    push_neg at hcore
    rw [sq_fixes_ge6 n k hn x hcore, threeCycle_fixes_ge6 n k x hcore]

/-- The squared product is a 3-cycle -/
theorem sq_isThreeCycle_n_ge1_m0 (n k : ℕ) (hn : n ≥ 1) :
    ((c₁₂_times_c₁₃_inv n k 0) ^ 2).IsThreeCycle := by
  rw [sq_eq_threeCycle n k hn]
  exact ThreeCycleExtract.threeCycle_0_5_1_isThreeCycle n k

end LemmaFeld.GroupTheory.AF.ThreeCycleProof
