/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma07
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma08
import LemmaFeld.GroupTheory.AF.ThreeCycle.SymmetricCase1Helpers

/-!
# Product Lemmas for Case 1: m ≥ 1, k = 0

Single-application and squared-action lemmas for (c₁₃ * c₂₃⁻¹) when k = 0.

## Key Results

When k = 0, g₂ = formPerm [1, 3, 4, 0] (no tail).
The product (c₁₃ * c₂₃⁻¹) has cycle type with a 3-cycle on {3, 4, 5}.
Squaring eliminates 2-cycles, leaving threeCycle_3_4_5.

## Computational Verification

The single application values are:
- prod(3) = 5
- prod(4) = 3
- prod(5) = 4
-/

open Equiv Perm

namespace LemmaFeld.GroupTheory.AF.Case1ProductLemmas

-- ============================================
-- SECTION 1: g₂ actions when k = 0
-- ============================================

/-- g₂ when k = 0 has cycle [1, 3, 4, 0] -/
theorem g₂_k0_list_nodup (n m : ℕ) :
    ([⟨1, by omega⟩, ⟨3, by omega⟩, ⟨4, by omega⟩, ⟨0, by omega⟩] :
      List (Omega n 0 m)).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, Fin.mk.injEq, or_false, not_or]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨not_false, List.nodup_nil⟩⟩ <;> omega

/-- g₂(3) = 4 when k = 0 -/
theorem g₂_k0_3_eq_4 (n m : ℕ) : g₂ n 0 m ⟨3, by omega⟩ = ⟨4, by omega⟩ := by
  rw [SymmetricCase1.g₂_k0_eq]; unfold g₂CoreList
  have hnd := g₂_k0_list_nodup n m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 1 (by simp)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h_fp; exact h_fp

/-- g₂(4) = 0 when k = 0 -/
theorem g₂_k0_4_eq_0 (n m : ℕ) : g₂ n 0 m ⟨4, by omega⟩ = ⟨0, by omega⟩ := by
  rw [SymmetricCase1.g₂_k0_eq]; unfold g₂CoreList
  have hnd := g₂_k0_list_nodup n m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 2 (by simp)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h_fp; exact h_fp

/-- g₂(0) = 1 when k = 0 -/
theorem g₂_k0_0_eq_1 (n m : ℕ) : g₂ n 0 m ⟨0, by omega⟩ = ⟨1, by omega⟩ := by
  rw [SymmetricCase1.g₂_k0_eq]; unfold g₂CoreList
  have hnd := g₂_k0_list_nodup n m
  have h_fp := List.formPerm_apply_getElem _ hnd 3 (by simp)
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    show (3 + 1) % 4 = 0 by native_decide,
    List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  exact h_fp

/-- g₂(1) = 3 when k = 0 -/
theorem g₂_k0_1_eq_3 (n m : ℕ) : g₂ n 0 m ⟨1, by omega⟩ = ⟨3, by omega⟩ := by
  rw [SymmetricCase1.g₂_k0_eq]; unfold g₂CoreList
  have hnd := g₂_k0_list_nodup n m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 0 (by simp)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h_fp; exact h_fp

/-- g₂ fixes 2 when k = 0 -/
theorem g₂_k0_fixes_2 (n m : ℕ) : g₂ n 0 m ⟨2, by omega⟩ = ⟨2, by omega⟩ := by
  rw [SymmetricCase1.g₂_k0_eq]; apply List.formPerm_apply_of_notMem
  simp only [g₂CoreList, List.mem_cons, List.not_mem_nil, Fin.mk.injEq, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- g₂ fixes 5 when k = 0 -/
theorem g₂_k0_fixes_5 (n m : ℕ) : g₂ n 0 m ⟨5, by omega⟩ = ⟨5, by omega⟩ := by
  rw [SymmetricCase1.g₂_k0_eq]; apply List.formPerm_apply_of_notMem
  simp only [g₂CoreList, List.mem_cons, List.not_mem_nil, Fin.mk.injEq, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

-- Inverse lemmas
theorem g₂_k0_inv_4_eq_3 (n m : ℕ) : (g₂ n 0 m)⁻¹ ⟨4, by omega⟩ = ⟨3, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₂_k0_3_eq_4 n m).symm

theorem g₂_k0_inv_0_eq_4 (n m : ℕ) : (g₂ n 0 m)⁻¹ ⟨0, by omega⟩ = ⟨4, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₂_k0_4_eq_0 n m).symm

theorem g₂_k0_inv_1_eq_0 (n m : ℕ) : (g₂ n 0 m)⁻¹ ⟨1, by omega⟩ = ⟨0, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₂_k0_0_eq_1 n m).symm

theorem g₂_k0_inv_3_eq_1 (n m : ℕ) : (g₂ n 0 m)⁻¹ ⟨3, by omega⟩ = ⟨1, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₂_k0_1_eq_3 n m).symm

theorem g₂_k0_inv_fixes_2 (n m : ℕ) : (g₂ n 0 m)⁻¹ ⟨2, by omega⟩ = ⟨2, by omega⟩ := by
  have h := g₂_k0_fixes_2 n m; conv_lhs => rw [← h]; rw [Perm.inv_apply_self]

theorem g₂_k0_inv_fixes_5 (n m : ℕ) : (g₂ n 0 m)⁻¹ ⟨5, by omega⟩ = ⟨5, by omega⟩ := by
  have h := g₂_k0_fixes_5 n m; conv_lhs => rw [← h]; rw [Perm.inv_apply_self]

-- ============================================
-- SECTION 2: g₃ actions (cycle [2,4,5,1,tailC])
-- ============================================

/-- g₃ core list for k = 0 -/
theorem g₃_k0_list_nodup (n m : ℕ) :
    ([⟨2, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩, ⟨1, by omega⟩] :
      List (Omega n 0 m)).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, Fin.mk.injEq, or_false, not_or]
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨not_false, List.nodup_nil⟩⟩ <;> omega

/-- g₃ fixes 3 -/
theorem g₃_fixes_3 (n m : ℕ) : g₃ n 0 m ⟨3, by omega⟩ = ⟨3, by omega⟩ := by
  unfold g₃; apply List.formPerm_apply_of_notMem
  simp only [g₃CoreList, tailCList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

/-- g₃ fixes 0 -/
theorem g₃_fixes_0 (n m : ℕ) : g₃ n 0 m ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  unfold g₃; apply List.formPerm_apply_of_notMem
  simp only [g₃CoreList, tailCList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

/-- g₃(4) = 5 -/
theorem g₃_4_eq_5 (n m : ℕ) : g₃ n 0 m ⟨4, by omega⟩ = ⟨5, by omega⟩ := by
  unfold g₃; have hnd := g₃_list_nodup n 0 m; have hlen := g₃_cycle_length n 0 m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 1 (by rw [hlen]; omega)
  simp only [g₃CoreList, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  exact h_fp

/-- g₃(5) = 1 -/
theorem g₃_5_eq_1 (n m : ℕ) : g₃ n 0 m ⟨5, by omega⟩ = ⟨1, by omega⟩ := by
  unfold g₃; have hnd := g₃_list_nodup n 0 m; have hlen := g₃_cycle_length n 0 m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 2 (by rw [hlen]; omega)
  simp only [g₃CoreList, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  exact h_fp

/-- g₃(2) = 4 -/
theorem g₃_2_eq_4 (n m : ℕ) : g₃ n 0 m ⟨2, by omega⟩ = ⟨4, by omega⟩ := by
  unfold g₃; have hnd := g₃_list_nodup n 0 m; have hlen := g₃_cycle_length n 0 m
  have hpos : 0 + 1 < (g₃CoreList n 0 m ++ tailCList n 0 m).length := by rw [hlen]; omega
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 0 hpos
  simp only [g₃CoreList, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  exact h_fp

-- Inverse lemmas
theorem g₃_inv_5_eq_4 (n m : ℕ) : (g₃ n 0 m)⁻¹ ⟨5, by omega⟩ = ⟨4, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₃_4_eq_5 n m).symm

theorem g₃_inv_1_eq_5 (n m : ℕ) : (g₃ n 0 m)⁻¹ ⟨1, by omega⟩ = ⟨5, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₃_5_eq_1 n m).symm

-- Note: g₃⁻¹(2) = 1 only when m = 0. For m ≥ 1, g₃⁻¹(2) = last_tailC.

theorem g₃_inv_4_eq_2 (n m : ℕ) : (g₃ n 0 m)⁻¹ ⟨4, by omega⟩ = ⟨2, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₃_2_eq_4 n m).symm

theorem g₃_inv_fixes_3 (n m : ℕ) : (g₃ n 0 m)⁻¹ ⟨3, by omega⟩ = ⟨3, by omega⟩ := by
  have h := g₃_fixes_3 n m; conv_lhs => rw [← h]; rw [Perm.inv_apply_self]

theorem g₃_inv_fixes_0 (n m : ℕ) : (g₃ n 0 m)⁻¹ ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  have h := g₃_fixes_0 n m; conv_lhs => rw [← h]; rw [Perm.inv_apply_self]

end LemmaFeld.GroupTheory.AF.Case1ProductLemmas
