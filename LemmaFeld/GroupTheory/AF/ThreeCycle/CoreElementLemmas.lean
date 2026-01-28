/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.ThreeCycle.ThreeCycleExtractHelpers
import LemmaFeld.GroupTheory.AF.ThreeCycle.TailLemmas
import LemmaFeld.GroupTheory.AF.ThreeCycle.TailALast

/-!
# Core Element Action Lemmas

Lemmas for generator/commutator actions on core elements {0,1,2,3,4,5}.
These support proving (c₁₂ * c₁₃⁻¹)² = threeCycle_0_5_1.
-/

open Equiv Perm

namespace LemmaFeld.GroupTheory.AF.CoreElementLemmas

-- ============================================
-- SECTION 1: g₃ actions (cycle [2,4,5,1])
-- ============================================

/-- g₃(5) = 1 -/
theorem g₃_5_eq_1 (n k : ℕ) : g₃ n k 0 ⟨5, by omega⟩ = ⟨1, by omega⟩ := by
  rw [ThreeCycleExtract.g₃_m0_eq]; unfold g₃CoreList
  have hnd : ([⟨2, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩, ⟨1, by omega⟩] :
      List (Omega n k 0)).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, Fin.mk.injEq, or_false, not_or]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨not_false, List.nodup_nil⟩⟩ <;> omega
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 2 (by simp)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h_fp; exact h_fp

/-- g₃(1) = 2: element 1 is at position 3 in [2,4,5,1], wraps to position 0 -/
theorem g₃_1_eq_2 (n k : ℕ) : g₃ n k 0 ⟨1, by omega⟩ = ⟨2, by omega⟩ := by
  rw [ThreeCycleExtract.g₃_m0_eq]; unfold g₃CoreList
  have hnd : ([⟨2, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩, ⟨1, by omega⟩] :
      List (Omega n k 0)).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, Fin.mk.injEq, or_false, not_or]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨not_false, List.nodup_nil⟩⟩ <;> omega
  have hpos : 3 < ([⟨2, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩, ⟨1, by omega⟩] :
      List (Omega n k 0)).length := by simp
  have h_fp := List.formPerm_apply_getElem _ hnd 3 hpos
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    show (3 + 1) % (0 + 1 + 1 + 1 + 1) = 0 by native_decide,
    List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  exact h_fp

/-- g₃ fixes 3 (not in cycle) -/
theorem g₃_fixes_3 (n k : ℕ) : g₃ n k 0 ⟨3, by omega⟩ = ⟨3, by omega⟩ := by
  rw [ThreeCycleExtract.g₃_m0_eq]; apply List.formPerm_apply_of_notMem
  simp only [g₃CoreList, List.mem_cons, List.not_mem_nil, Fin.mk.injEq, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- g₃⁻¹(1) = 5 -/
theorem g₃_inv_1_eq_5 (n k : ℕ) : (g₃ n k 0)⁻¹ ⟨1, by omega⟩ = ⟨5, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₃_5_eq_1 n k).symm

/-- g₃⁻¹(2) = 1 -/
theorem g₃_inv_2_eq_1 (n k : ℕ) : (g₃ n k 0)⁻¹ ⟨2, by omega⟩ = ⟨1, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₃_1_eq_2 n k).symm

-- ============================================
-- SECTION 2: g₁ actions (cycle [0,5,3,2,tailA])
-- ============================================

/-- g₁(5) = 3 -/
theorem g₁_5_eq_3 (n k : ℕ) : g₁ n k 0 ⟨5, by omega⟩ = ⟨3, by omega⟩ := by
  unfold g₁; have hnd := g₁_list_nodup n k 0; have hlen := g₁_cycle_length n k 0
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 1 (by rw [hlen]; omega)
  simp only [g₁CoreList, List.cons_append, List.getElem_cons_succ,
    List.getElem_cons_zero] at h_fp; exact h_fp

/-- g₁(3) = 2 -/
theorem g₁_3_eq_2 (n k : ℕ) : g₁ n k 0 ⟨3, by omega⟩ = ⟨2, by omega⟩ := by
  unfold g₁; have hnd := g₁_list_nodup n k 0; have hlen := g₁_cycle_length n k 0
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 2 (by rw [hlen]; omega)
  simp only [g₁CoreList, List.cons_append, List.getElem_cons_succ,
    List.getElem_cons_zero] at h_fp; exact h_fp

/-- g₁⁻¹(3) = 5 -/
theorem g₁_inv_3_eq_5 (n k : ℕ) : (g₁ n k 0)⁻¹ ⟨3, by omega⟩ = ⟨5, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₁_5_eq_3 n k).symm

/-- g₁⁻¹(2) = 3 -/
theorem g₁_inv_2_eq_3 (n k : ℕ) : (g₁ n k 0)⁻¹ ⟨2, by omega⟩ = ⟨3, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₁_3_eq_2 n k).symm

/-- g₁(2) = 6 (first tailA element, requires n ≥ 1) -/
theorem g₁_2_eq_6 (n k : ℕ) (hn : n ≥ 1) : g₁ n k 0 ⟨2, by omega⟩ = ⟨6, by omega⟩ := by
  unfold g₁; have hnd := g₁_list_nodup n k 0; have hlen := g₁_cycle_length n k 0
  have hpos4 : 4 < (g₁CoreList n k 0 ++ tailAList n k 0).length := by rw [hlen]; omega
  have h_at : (g₁CoreList n k 0 ++ tailAList n k 0)[3]'(by rw [hlen]; omega) = ⟨2, by omega⟩ := by
    simp only [g₁CoreList, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]
  have h_next : (g₁CoreList n k 0 ++ tailAList n k 0)[4]'hpos4 = ⟨6, by omega⟩ := by
    have := Transitivity.g₁_list_getElem_tail n k 0 ⟨0, hn⟩
    simp only [Fin.val_mk, Nat.add_zero] at this
    rw [Fin.ext_iff]; simp only [Fin.val_mk]; rw [Fin.ext_iff] at this; simp only [Fin.val_mk] at this
    exact this
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 3 hpos4
  simp only [h_at] at h_fp; rw [h_next] at h_fp; exact h_fp

/-- g₁⁻¹(6) = 2 (requires n ≥ 1) -/
theorem g₁_inv_6_eq_2 (n k : ℕ) (hn : n ≥ 1) : (g₁ n k 0)⁻¹ ⟨6, by omega⟩ = ⟨2, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₁_2_eq_6 n k hn).symm

-- ============================================
-- SECTION 3: g₂ actions (cycle [1,3,4,0,tailB])
-- ============================================

/-- g₂ fixes 5 (not in cycle) -/
theorem g₂_fixes_5 (n k : ℕ) : g₂ n k 0 ⟨5, by omega⟩ = ⟨5, by omega⟩ := by
  unfold g₂; apply List.formPerm_apply_of_notMem
  simp only [g₂CoreList, tailBList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

/-- g₂ fixes 2 (not in cycle) -/
theorem g₂_fixes_2 (n k : ℕ) : g₂ n k 0 ⟨2, by omega⟩ = ⟨2, by omega⟩ := by
  unfold g₂; apply List.formPerm_apply_of_notMem
  simp only [g₂CoreList, tailBList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

/-- g₂(1) = 3 -/
theorem g₂_1_eq_3 (n k : ℕ) : g₂ n k 0 ⟨1, by omega⟩ = ⟨3, by omega⟩ := by
  unfold g₂; have hnd := g₂_list_nodup n k 0; have hlen := g₂_cycle_length n k 0
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 0 (by rw [hlen]; omega)
  simp only [g₂CoreList, List.cons_append, List.getElem_cons_succ,
    List.getElem_cons_zero] at h_fp; exact h_fp

/-- g₂(3) = 4 -/
theorem g₂_3_eq_4 (n k : ℕ) : g₂ n k 0 ⟨3, by omega⟩ = ⟨4, by omega⟩ := by
  unfold g₂; have hnd := g₂_list_nodup n k 0; have hlen := g₂_cycle_length n k 0
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 1 (by rw [hlen]; omega)
  simp only [g₂CoreList, List.cons_append, List.getElem_cons_succ,
    List.getElem_cons_zero] at h_fp; exact h_fp

/-- g₂(4) = 0 -/
theorem g₂_4_eq_0 (n k : ℕ) : g₂ n k 0 ⟨4, by omega⟩ = ⟨0, by omega⟩ := by
  unfold g₂; have hnd := g₂_list_nodup n k 0; have hlen := g₂_cycle_length n k 0
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 2 (by rw [hlen]; omega)
  simp only [g₂CoreList, List.cons_append, List.getElem_cons_succ,
    List.getElem_cons_zero] at h_fp; exact h_fp

/-- g₂⁻¹(3) = 1 -/
theorem g₂_inv_3_eq_1 (n k : ℕ) : (g₂ n k 0)⁻¹ ⟨3, by omega⟩ = ⟨1, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₂_1_eq_3 n k).symm

/-- g₂⁻¹(4) = 3 -/
theorem g₂_inv_4_eq_3 (n k : ℕ) : (g₂ n k 0)⁻¹ ⟨4, by omega⟩ = ⟨3, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₂_3_eq_4 n k).symm

/-- g₂⁻¹(5) = 5 -/
theorem g₂_inv_fixes_5 (n k : ℕ) : (g₂ n k 0)⁻¹ ⟨5, by omega⟩ = ⟨5, by omega⟩ := by
  have h := g₂_fixes_5 n k; conv_lhs => rw [← h]; rw [Perm.inv_apply_self]

/-- g₂⁻¹(2) = 2 -/
theorem g₂_inv_fixes_2 (n k : ℕ) : (g₂ n k 0)⁻¹ ⟨2, by omega⟩ = ⟨2, by omega⟩ := by
  have h := g₂_fixes_2 n k; conv_lhs => rw [← h]; rw [Perm.inv_apply_self]

end LemmaFeld.GroupTheory.AF.CoreElementLemmas
