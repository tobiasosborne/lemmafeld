/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.ThreeCycle.SymmetricCase2Helpers

/-!
# Product Lemmas for Case 2: k ≥ 1

Action lemmas for g₁ and g₂ when k ≥ 1 (tailB is non-empty).

## Generator Structure

- g₁ = formPerm [0, 5, 3, 2, tailA]: fixes 1, 4, and tailB/tailC
- g₂ = formPerm [1, 3, 4, 0, tailB]: fixes 2, 5, and tailA/tailC
-/

open Equiv Perm

namespace LemmaFeld.GroupTheory.AF.Case2ProductLemmas

-- ============================================
-- SECTION 1: g₁ actions on core elements
-- ============================================

/-- g₁(0) = 5 -/
theorem g₁_0_eq_5 (n k m : ℕ) : g₁ n k m ⟨0, by omega⟩ = ⟨5, by omega⟩ := by
  unfold g₁; have hnd := g₁_list_nodup n k m; have hlen := g₁_cycle_length n k m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 0 (by rw [hlen]; omega)
  simp only [g₁CoreList, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  exact h_fp

/-- g₁(5) = 3 -/
theorem g₁_5_eq_3 (n k m : ℕ) : g₁ n k m ⟨5, by omega⟩ = ⟨3, by omega⟩ := by
  unfold g₁; have hnd := g₁_list_nodup n k m; have hlen := g₁_cycle_length n k m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 1 (by rw [hlen]; omega)
  simp only [g₁CoreList, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  exact h_fp

/-- g₁(3) = 2 -/
theorem g₁_3_eq_2 (n k m : ℕ) : g₁ n k m ⟨3, by omega⟩ = ⟨2, by omega⟩ := by
  unfold g₁; have hnd := g₁_list_nodup n k m; have hlen := g₁_cycle_length n k m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 2 (by rw [hlen]; omega)
  simp only [g₁CoreList, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  exact h_fp

/-- g₁ fixes 1 -/
theorem g₁_fixes_1 (n k m : ℕ) : g₁ n k m ⟨1, by omega⟩ = ⟨1, by omega⟩ := by
  unfold g₁; apply List.formPerm_apply_of_notMem
  simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

/-- g₁ fixes 4 -/
theorem g₁_fixes_4 (n k m : ℕ) : g₁ n k m ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
  unfold g₁; apply List.formPerm_apply_of_notMem
  simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

-- Inverse lemmas
theorem g₁_inv_5_eq_0 (n k m : ℕ) : (g₁ n k m)⁻¹ ⟨5, by omega⟩ = ⟨0, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₁_0_eq_5 n k m).symm

theorem g₁_inv_3_eq_5 (n k m : ℕ) : (g₁ n k m)⁻¹ ⟨3, by omega⟩ = ⟨5, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₁_5_eq_3 n k m).symm

theorem g₁_inv_2_eq_3 (n k m : ℕ) : (g₁ n k m)⁻¹ ⟨2, by omega⟩ = ⟨3, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₁_3_eq_2 n k m).symm

theorem g₁_inv_fixes_1 (n k m : ℕ) : (g₁ n k m)⁻¹ ⟨1, by omega⟩ = ⟨1, by omega⟩ := by
  have h := g₁_fixes_1 n k m; conv_lhs => rw [← h]; rw [Perm.inv_apply_self]

theorem g₁_inv_fixes_4 (n k m : ℕ) : (g₁ n k m)⁻¹ ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
  have h := g₁_fixes_4 n k m; conv_lhs => rw [← h]; rw [Perm.inv_apply_self]

-- ============================================
-- SECTION 2: g₂ actions on core elements
-- ============================================

/-- g₂(1) = 3 -/
theorem g₂_1_eq_3 (n k m : ℕ) : g₂ n k m ⟨1, by omega⟩ = ⟨3, by omega⟩ := by
  unfold g₂; have hnd := g₂_list_nodup n k m; have hlen := g₂_cycle_length n k m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 0 (by rw [hlen]; omega)
  simp only [g₂CoreList, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  exact h_fp

/-- g₂(3) = 4 -/
theorem g₂_3_eq_4 (n k m : ℕ) : g₂ n k m ⟨3, by omega⟩ = ⟨4, by omega⟩ := by
  unfold g₂; have hnd := g₂_list_nodup n k m; have hlen := g₂_cycle_length n k m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 1 (by rw [hlen]; omega)
  simp only [g₂CoreList, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  exact h_fp

/-- g₂(4) = 0 -/
theorem g₂_4_eq_0 (n k m : ℕ) : g₂ n k m ⟨4, by omega⟩ = ⟨0, by omega⟩ := by
  unfold g₂; have hnd := g₂_list_nodup n k m; have hlen := g₂_cycle_length n k m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 2 (by rw [hlen]; omega)
  simp only [g₂CoreList, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  exact h_fp

/-- g₂ fixes 2 -/
theorem g₂_fixes_2 (n k m : ℕ) : g₂ n k m ⟨2, by omega⟩ = ⟨2, by omega⟩ := by
  unfold g₂; apply List.formPerm_apply_of_notMem
  simp only [g₂CoreList, tailBList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

/-- g₂ fixes 5 -/
theorem g₂_fixes_5 (n k m : ℕ) : g₂ n k m ⟨5, by omega⟩ = ⟨5, by omega⟩ := by
  unfold g₂; apply List.formPerm_apply_of_notMem
  simp only [g₂CoreList, tailBList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

-- Inverse lemmas
theorem g₂_inv_3_eq_1 (n k m : ℕ) : (g₂ n k m)⁻¹ ⟨3, by omega⟩ = ⟨1, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₂_1_eq_3 n k m).symm

theorem g₂_inv_4_eq_3 (n k m : ℕ) : (g₂ n k m)⁻¹ ⟨4, by omega⟩ = ⟨3, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₂_3_eq_4 n k m).symm

theorem g₂_inv_0_eq_4 (n k m : ℕ) : (g₂ n k m)⁻¹ ⟨0, by omega⟩ = ⟨4, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₂_4_eq_0 n k m).symm

theorem g₂_inv_fixes_2 (n k m : ℕ) : (g₂ n k m)⁻¹ ⟨2, by omega⟩ = ⟨2, by omega⟩ := by
  have h := g₂_fixes_2 n k m; conv_lhs => rw [← h]; rw [Perm.inv_apply_self]

theorem g₂_inv_fixes_5 (n k m : ℕ) : (g₂ n k m)⁻¹ ⟨5, by omega⟩ = ⟨5, by omega⟩ := by
  have h := g₂_fixes_5 n k m; conv_lhs => rw [← h]; rw [Perm.inv_apply_self]

-- ============================================
-- SECTION 3: g₁ actions on tailB elements
-- ============================================

/-- g₁ fixes elements in tailB (indices 6+n ≤ x < 6+n+k) -/
theorem g₁_fixes_tailB (n k m : ℕ) (x : Omega n k m) (hx : 6 + n ≤ x.val ∧ x.val < 6 + n + k) :
    g₁ n k m x = x := by
  unfold g₁; apply List.formPerm_apply_of_notMem
  simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

/-- g₁⁻¹ fixes elements in tailB -/
theorem g₁_inv_fixes_tailB (n k m : ℕ) (x : Omega n k m) (hx : 6 + n ≤ x.val ∧ x.val < 6 + n + k) :
    (g₁ n k m)⁻¹ x = x := by
  have h := g₁_fixes_tailB n k m x hx; conv_lhs => rw [← h]; rw [Perm.inv_apply_self]

end LemmaFeld.GroupTheory.AF.Case2ProductLemmas
