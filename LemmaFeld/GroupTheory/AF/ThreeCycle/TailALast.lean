/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma06
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma07
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma09
import LemmaFeld.GroupTheory.AF.ThreeCycle.ThreeCycleExtractHelpers
import LemmaFeld.GroupTheory.AF.ThreeCycle.TailAFixing
import LemmaFeld.GroupTheory.AF.Transitivity.Lemma05ListProps

/-!
# Last TailA Element: 2-Cycle with Core Element 4

When m = 0, the product (c₁₂ * c₁₃⁻¹) forms a 2-cycle: 4 ↔ (5+n).
Squaring eliminates this 2-cycle.
-/

open Equiv Perm

namespace LemmaFeld.GroupTheory.AF.TailALast

/-- g₁ fixes element 4 (not in g₁'s cycle) -/
theorem g₁_fixes_4 (n k : ℕ) : g₁ n k 0 ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
  unfold g₁; apply List.formPerm_apply_of_notMem
  simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

/-- g₁⁻¹ fixes element 4 -/
theorem g₁_inv_fixes_4 (n k : ℕ) : (g₁ n k 0)⁻¹ ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
  have h := g₁_fixes_4 n k; conv_lhs => rw [← h]; rw [Perm.inv_apply_self]

/-- g₂⁻¹(0) = 4 (from cycle [1,3,4,0]) -/
theorem g₂_inv_0_eq_4 (n k : ℕ) : (g₂ n k 0)⁻¹ ⟨0, by omega⟩ = ⟨4, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; unfold g₂
  have hnd := g₂_list_nodup n k 0
  have hlen := g₂_cycle_length n k 0
  have hpos : 2 < (g₂CoreList n k 0 ++ tailBList n k 0).length := by rw [hlen]; omega
  have hpos1 : 3 < (g₂CoreList n k 0 ++ tailBList n k 0).length := by rw [hlen]; omega
  have h_at : (g₂CoreList n k 0 ++ tailBList n k 0)[2]'hpos = ⟨4, by omega⟩ := by
    simp only [g₂CoreList, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 2 hpos1
  rw [h_at] at h_fp
  have h_next : (g₂CoreList n k 0 ++ tailBList n k 0)[3]'hpos1 = ⟨0, by omega⟩ := by
    simp only [g₂CoreList, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]
  rw [h_next] at h_fp; exact h_fp.symm

/-- c₁₂(5+n) = 4 when n ≥ 1 -/
theorem c₁₂_last_tailA_eq_4 (n k : ℕ) (hn : n ≥ 1) :
    commutator_g₁_g₂ n k 0 ⟨5 + n, by omega⟩ = ⟨4, by omega⟩ := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  have hA : 6 ≤ (5 + n) ∧ (5 + n) < 6 + n := ⟨by omega, by omega⟩
  have hg₂ := TailAFixing.g₂_fixes_tailA n k ⟨5 + n, by omega⟩ hA
  simp only [Fin.val_mk] at hg₂; rw [hg₂]
  have hg₁ : g₁ n k 0 ⟨5 + n, by omega⟩ = ⟨0, by omega⟩ := by
    have := TailAFixing.g₁_inv_0_eq_last n k hn
    rw [Perm.inv_eq_iff_eq] at this; exact this.symm
  rw [hg₁, g₂_inv_0_eq_4, g₁_inv_fixes_4]

/-- g₃(4) = 5 (from cycle [2,4,5,1]) -/
theorem g₃_4_eq_5 (n k : ℕ) : g₃ n k 0 ⟨4, by omega⟩ = ⟨5, by omega⟩ := by
  rw [ThreeCycleExtract.g₃_m0_eq]; unfold g₃CoreList
  have hnd : ([⟨2, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩, ⟨1, by omega⟩] :
      List (Omega n k 0)).Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, Fin.mk.injEq, or_false, not_or]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨not_false, List.nodup_nil⟩⟩ <;> intro h <;> omega
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 1 (by simp)
  simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h_fp; exact h_fp

/-- g₁⁻¹(5) = 0 (from cycle [0,5,3,2,...]) -/
theorem g₁_inv_5_eq_0 (n k : ℕ) : (g₁ n k 0)⁻¹ ⟨5, by omega⟩ = ⟨0, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; unfold g₁
  have hnd := g₁_list_nodup n k 0
  have hlen := g₁_cycle_length n k 0
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 0 (by rw [hlen]; omega)
  simp only [g₁CoreList, List.cons_append, List.getElem_cons_zero, List.getElem_cons_succ] at h_fp
  exact h_fp.symm

/-- g₁(0) = 5 (from cycle [0,5,3,2,...]) -/
theorem g₁_0_eq_5 (n k : ℕ) : g₁ n k 0 ⟨0, by omega⟩ = ⟨5, by omega⟩ := by
  unfold g₁
  have hnd := g₁_list_nodup n k 0
  have hlen := g₁_cycle_length n k 0
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 0 (by rw [hlen]; omega)
  simp only [g₁CoreList, List.cons_append, List.getElem_cons_zero, List.getElem_cons_succ] at h_fp
  exact h_fp

/-- g₃⁻¹(5) = 4 (from cycle [2,4,5,1], g₃(4)=5 so g₃⁻¹(5)=4) -/
theorem g₃_inv_5_eq_4 (n k : ℕ) : (g₃ n k 0)⁻¹ ⟨5, by omega⟩ = ⟨4, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₃_4_eq_5 n k).symm

/-- c₁₃⁻¹(4) = 0 when m = 0: trace g₃(0)=0, g₁(0)=5, g₃⁻¹(5)=4, g₁⁻¹(4)=4 -/
theorem c₁₃_inv_4_eq_0 (n k : ℕ) : (commutator_g₁_g₃ n k 0)⁻¹ ⟨4, by omega⟩ = ⟨0, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; unfold commutator_g₁_g₃; simp only [Perm.mul_apply]
  -- Goal: 4 = g₁⁻¹(g₃⁻¹(g₁(g₃(0))))
  rw [TailAFixing.g₃_fixes_0 n k, g₁_0_eq_5, g₃_inv_5_eq_4, g₁_inv_fixes_4]

/-- g₁ fixes g₂(0): either 1 (if k=0) or tailB element (if k>0) -/
theorem g₁_fixes_g₂_0 (n k : ℕ) : g₁ n k 0 (g₂ n k 0 ⟨0, by omega⟩) = g₂ n k 0 ⟨0, by omega⟩ := by
  unfold g₁ g₂; apply List.formPerm_apply_of_notMem
  simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  have hnd := g₂_list_nodup n k 0
  have hlen := g₂_cycle_length n k 0
  have hpos : 3 < (g₂CoreList n k 0 ++ tailBList n k 0).length := by rw [hlen]; omega
  have h_at : (g₂CoreList n k 0 ++ tailBList n k 0)[3]'hpos = ⟨0, by omega⟩ := by
    simp only [g₂CoreList, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero]
  have h_fp := List.formPerm_apply_getElem _ hnd 3 hpos
  simp only [h_at] at h_fp
  by_cases hk : k = 0
  · subst hk
    have hmod : (3 + 1) % (g₂CoreList n 0 0 ++ tailBList n 0 0).length = 0 := by
      simp only [g₂_cycle_length, Nat.add_zero, Nat.mod_self]
    simp only [hmod] at h_fp
    have hpos0 : 0 < (g₂CoreList n 0 0 ++ tailBList n 0 0).length := by rw [hlen]; omega
    have h0 : (g₂CoreList n 0 0 ++ tailBList n 0 0)[0]'hpos0 = ⟨1, by omega⟩ := by
      simp only [g₂CoreList, tailBList, List.finRange, List.cons_append, List.nil_append,
        List.getElem_cons_zero]
    simp only [h0] at h_fp; rw [h_fp]
    constructor
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
    · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega
  · have hk' : k ≥ 1 := by omega
    have hmod : (3 + 1) % (g₂CoreList n k 0 ++ tailBList n k 0).length = 4 := by
      simp only [g₂_cycle_length]; exact Nat.mod_eq_of_lt (by omega)
    simp only [hmod] at h_fp
    have hpos4 : 4 < (g₂CoreList n k 0 ++ tailBList n k 0).length := by rw [hlen]; omega
    have h4 : (g₂CoreList n k 0 ++ tailBList n k 0)[4]'hpos4 = ⟨6 + n, by omega⟩ := by
      have := Transitivity.g₂_list_getElem_tail n k 0 ⟨0, hk'⟩
      simp only [Fin.val_mk, Nat.add_zero] at this
      rw [Fin.ext_iff]; simp only [Fin.val_mk]; rw [Fin.ext_iff] at this; simp only [Fin.val_mk] at this
      exact this
    simp only [h4] at h_fp; rw [h_fp]
    constructor
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
    · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

/-- c₁₂(0) = 5+n when n ≥ 1 (via: g₂(0)→y, g₁(y)=y, g₂⁻¹(y)=0, g₁⁻¹(0)=5+n) -/
theorem c₁₂_0_eq_last_tailA (n k : ℕ) (hn : n ≥ 1) :
    commutator_g₁_g₂ n k 0 ⟨0, by omega⟩ = ⟨5 + n, by omega⟩ := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  rw [g₁_fixes_g₂_0, Perm.inv_apply_self, TailAFixing.g₁_inv_0_eq_last n k hn]

/-- (c₁₂ * c₁₃⁻¹)(5+n) = 4 when n ≥ 1 -/
theorem product_last_tailA_eq_4 (n k : ℕ) (hn : n ≥ 1) :
    c₁₂_times_c₁₃_inv n k 0 ⟨5 + n, by omega⟩ = ⟨4, by omega⟩ := by
  unfold c₁₂_times_c₁₃_inv c₁₂ c₁₃; simp only [Perm.mul_apply]
  have hA : 6 ≤ (5 + n) ∧ (5 + n) < 6 + n := ⟨by omega, by omega⟩
  rw [TailAFixing.c₁₃_inv_fixes_tailA n k ⟨5 + n, by omega⟩ hA]
  exact c₁₂_last_tailA_eq_4 n k hn

/-- (c₁₂ * c₁₃⁻¹)(4) = 5+n when n ≥ 1 -/
theorem product_4_eq_last_tailA (n k : ℕ) (hn : n ≥ 1) :
    c₁₂_times_c₁₃_inv n k 0 ⟨4, by omega⟩ = ⟨5 + n, by omega⟩ := by
  unfold c₁₂_times_c₁₃_inv c₁₂ c₁₃; simp only [Perm.mul_apply]
  rw [c₁₃_inv_4_eq_0, c₁₂_0_eq_last_tailA n k hn]

/-- (c₁₂ * c₁₃⁻¹)²(5+n) = 5+n when n ≥ 1 (2-cycle elimination) -/
theorem sq_fixes_last_tailA (n k : ℕ) (hn : n ≥ 1) :
    (c₁₂_times_c₁₃_inv n k 0 ^ 2) ⟨5 + n, by omega⟩ = ⟨5 + n, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [product_last_tailA_eq_4 n k hn, product_4_eq_last_tailA n k hn]

end LemmaFeld.GroupTheory.AF.TailALast
