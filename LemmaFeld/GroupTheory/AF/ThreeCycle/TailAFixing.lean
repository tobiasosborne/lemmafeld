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
import LemmaFeld.GroupTheory.AF.Transitivity.Lemma05ListProps

/-!
# TailA Fixing Lemmas for 3-Cycle Extraction

When m = 0: g₂ fixes tailA, c₁₃⁻¹ fixes tailA, c₁₂ fixes tailA except last.
-/

open Equiv Perm

namespace LemmaFeld.GroupTheory.AF.TailAFixing

/-- g₂ fixes tailA elements (tailA ∩ g₂'s support = ∅) -/
theorem g₂_fixes_tailA (n k : ℕ) (x : Omega n k 0) (hA : 6 ≤ x.val ∧ x.val < 6 + n) :
    g₂ n k 0 x = x := by
  unfold g₂; apply List.formPerm_apply_of_notMem
  simp only [g₂CoreList, tailBList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

/-- g₂⁻¹ fixes tailA elements -/
theorem g₂_inv_fixes_tailA (n k : ℕ) (x : Omega n k 0) (hA : 6 ≤ x.val ∧ x.val < 6 + n) :
    (g₂ n k 0)⁻¹ x = x := by
  have h := g₂_fixes_tailA n k x hA; conv_lhs => rw [← h]; rw [Perm.inv_apply_self]

/-- g₃ fixes 0 when m = 0 -/
theorem g₃_fixes_0 (n k : ℕ) : g₃ n k 0 ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  rw [ThreeCycleExtract.g₃_m0_eq]; apply List.formPerm_apply_of_notMem
  simp only [g₃CoreList, List.mem_cons, List.not_mem_nil, Fin.mk.injEq, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

/-- g₁ maps tailA to tailA or to 0 (last tailA wraps to 0) -/
theorem g₁_maps_tailA (n k : ℕ) (hn : n ≥ 1) (x : Omega n k 0) (hA : 6 ≤ x.val ∧ x.val < 6 + n) :
    (6 ≤ (g₁ n k 0 x).val ∧ (g₁ n k 0 x).val < 6 + n) ∨ (g₁ n k 0 x).val = 0 := by
  have hnd := g₁_list_nodup n k 0
  have hlen := g₁_cycle_length n k 0
  have hx_ge6 : x.val ≥ 6 := hA.1
  have hi_bound : x.val - 6 < n := by omega
  have hpos : 4 + (x.val - 6) < (g₁CoreList n k 0 ++ tailAList n k 0).length := by rw [hlen]; omega
  have h_at : (g₁CoreList n k 0 ++ tailAList n k 0)[4 + (x.val - 6)]'hpos = x := by
    have := Transitivity.g₁_list_getElem_tail n k 0 ⟨x.val - 6, hi_bound⟩
    simp only [Fin.val_mk] at this
    rw [Fin.ext_iff]; simp only [this]; omega
  by_cases hlast : x.val = 5 + n
  · right
    have hpos' : 3 + n < (g₁CoreList n k 0 ++ tailAList n k 0).length := by rw [hlen]; omega
    have h_mod : (3 + n + 1) % (g₁CoreList n k 0 ++ tailAList n k 0).length = 0 := by
      rw [hlen]; simp only [show 3 + n + 1 = 4 + n by omega, Nat.mod_self]
    have h_fp := List.formPerm_apply_getElem (g₁CoreList n k 0 ++ tailAList n k 0) hnd (3 + n) hpos'
    simp only [h_mod] at h_fp
    have hpos_eq : 4 + (x.val - 6) = 3 + n := by omega
    have h_at' : (g₁CoreList n k 0 ++ tailAList n k 0)[3 + n]'hpos' = x := by
      have h := h_at; simp only [hpos_eq] at h; exact h
    rw [h_at'] at h_fp; unfold g₁
    have h0 : (g₁CoreList n k 0 ++ tailAList n k 0)[0]'(by rw [hlen]; omega) = ⟨0, by omega⟩ := by
      simp only [g₁CoreList, List.cons_append, List.getElem_cons_zero]
    rw [h_fp, h0]
  · left
    have hip1_bound : x.val - 6 + 1 < n := by omega
    have hpos1 : 4 + (x.val - 6) + 1 < (g₁CoreList n k 0 ++ tailAList n k 0).length := by
      rw [hlen]; omega
    have h_fp : (g₁ n k 0) x = (g₁CoreList n k 0 ++ tailAList n k 0)[4 + (x.val - 6) + 1]'hpos1 := by
      unfold g₁; conv_lhs => rw [← h_at]
      exact List.formPerm_apply_lt_getElem _ hnd (4 + (x.val - 6)) hpos1
    have h_next : (g₁CoreList n k 0 ++ tailAList n k 0)[4 + (x.val - 6) + 1]'hpos1 =
        ⟨x.val + 1, by omega⟩ := by
      have := Transitivity.g₁_list_getElem_tail n k 0 ⟨x.val - 6 + 1, hip1_bound⟩
      simp only [Fin.val_mk] at this
      have heq : 4 + (x.val - 6) + 1 = 4 + (x.val - 6 + 1) := by ring
      rw [Fin.ext_iff]; simp only [heq] at this ⊢; simp only [this]; omega
    rw [h_fp, h_next]; simp only [Fin.val_mk]; constructor <;> omega

/-- g₁⁻¹(0) = 5+n (the last tailA element) -/
theorem g₁_inv_0_eq_last (n k : ℕ) (hn : n ≥ 1) :
    (g₁ n k 0)⁻¹ ⟨0, by omega⟩ = ⟨5 + n, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; unfold g₁
  have hnd := g₁_list_nodup n k 0
  have hlen := g₁_cycle_length n k 0
  have hpos : 3 + n < (g₁CoreList n k 0 ++ tailAList n k 0).length := by rw [hlen]; omega
  have h_mod : (3 + n + 1) % (g₁CoreList n k 0 ++ tailAList n k 0).length = 0 := by
    rw [hlen]; simp only [show 3 + n + 1 = 4 + n by omega, Nat.mod_self]
  have h_fp := List.formPerm_apply_getElem (g₁CoreList n k 0 ++ tailAList n k 0) hnd (3 + n) hpos
  simp only [h_mod] at h_fp
  have hnm1_bound : n - 1 < n := Nat.sub_lt hn Nat.one_pos
  have h_last : (g₁CoreList n k 0 ++ tailAList n k 0)[3 + n]'hpos = ⟨5 + n, by omega⟩ := by
    have := Transitivity.g₁_list_getElem_tail n k 0 ⟨n - 1, hnm1_bound⟩
    simp only [Fin.val_mk] at this
    have heq : 4 + (n - 1) = 3 + n := by omega
    rw [Fin.ext_iff]; simp only [heq] at this ⊢; simp only [this]; omega
  rw [h_last] at h_fp
  have h0 : (g₁CoreList n k 0 ++ tailAList n k 0)[0]'(by rw [hlen]; omega) = ⟨0, by omega⟩ := by
    simp only [g₁CoreList, List.cons_append, List.getElem_cons_zero]
  rw [h0] at h_fp; exact h_fp.symm

/-- c₁₃⁻¹ fixes ALL tailA elements -/
theorem c₁₃_inv_fixes_tailA (n k : ℕ) (x : Omega n k 0) (hA : 6 ≤ x.val ∧ x.val < 6 + n) :
    (commutator_g₁_g₃ n k 0)⁻¹ x = x := by
  rw [Perm.inv_eq_iff_eq]; unfold commutator_g₁_g₃; simp only [Perm.mul_apply]
  have hx_ge6 : x.val ≥ 6 := hA.1
  have hg₃x := ThreeCycleExtract.g₃_fixes_val_ge_6 n k x hx_ge6
  rw [hg₃x]
  have hn : n ≥ 1 := by omega
  rcases g₁_maps_tailA n k hn x hA with hg₁x_tailA | hg₁x_0
  · have hg₃_g₁x := ThreeCycleExtract.g₃_fixes_val_ge_6 n k (g₁ n k 0 x) hg₁x_tailA.1
    have hg₃_inv_g₁x : (g₃ n k 0)⁻¹ (g₁ n k 0 x) = g₁ n k 0 x := by
      conv_lhs => rw [← hg₃_g₁x]; rw [Perm.inv_apply_self]
    rw [hg₃_inv_g₁x, Perm.inv_apply_self]
  · have h0 : g₁ n k 0 x = ⟨0, by omega⟩ := Fin.ext hg₁x_0
    rw [h0]
    have hg₃_inv_0 : (g₃ n k 0)⁻¹ ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
      have hfix := g₃_fixes_0 n k; conv_lhs => rw [← hfix]; rw [Perm.inv_apply_self]
    rw [hg₃_inv_0]
    -- g₁(x) = 0 means x is the last tailA element (5+n)
    have hx_last : x.val = 5 + n := by
      have hnd := g₁_list_nodup n k 0
      have hlen := g₁_cycle_length n k 0
      have hi_bound : x.val - 6 < n := by omega
      have hpos : 4 + (x.val - 6) < (g₁CoreList n k 0 ++ tailAList n k 0).length := by
        rw [hlen]; omega
      have h_at : (g₁CoreList n k 0 ++ tailAList n k 0)[4 + (x.val - 6)]'hpos = x := by
        have := Transitivity.g₁_list_getElem_tail n k 0 ⟨x.val - 6, hi_bound⟩
        simp only [Fin.val_mk] at this
        rw [Fin.ext_iff]; simp only [this]; omega
      by_contra hne
      have hip1_bound : x.val - 6 + 1 < n := by omega
      have hpos1 : 4 + (x.val - 6) + 1 < (g₁CoreList n k 0 ++ tailAList n k 0).length := by
        rw [hlen]; omega
      have h_fp : (g₁ n k 0) x = (g₁CoreList n k 0 ++ tailAList n k 0)[4 + (x.val - 6) + 1]'hpos1 := by
        unfold g₁; conv_lhs => rw [← h_at]
        exact List.formPerm_apply_lt_getElem _ hnd (4 + (x.val - 6)) hpos1
      have h_next : (g₁CoreList n k 0 ++ tailAList n k 0)[4 + (x.val - 6) + 1]'hpos1 =
          ⟨x.val + 1, by omega⟩ := by
        have := Transitivity.g₁_list_getElem_tail n k 0 ⟨x.val - 6 + 1, hip1_bound⟩
        simp only [Fin.val_mk] at this
        have heq : 4 + (x.val - 6) + 1 = 4 + (x.val - 6 + 1) := by ring
        rw [Fin.ext_iff]; simp only [heq] at this ⊢; simp only [this]; omega
      have h_next_val : ((g₁CoreList n k 0 ++ tailAList n k 0)[4 + (x.val - 6) + 1]'hpos1).val =
          x.val + 1 := by rw [h_next]
      have := congrArg Fin.val h_fp
      simp only [h_next_val] at this; omega
    -- Goal: (g₁ n k 0)⁻¹ ⟨0, _⟩ = x
    -- We know: x.val = 5 + n and g₁⁻¹(0) = ⟨5 + n, _⟩
    have hg₁_inv := g₁_inv_0_eq_last n k hn
    rw [Fin.ext_iff]; rw [Fin.ext_iff] at hg₁_inv
    simp only [Fin.val_mk] at hg₁_inv
    omega

/-- c₁₂ fixes tailA elements that are not the last (x.val < 5+n) -/
theorem c₁₂_fixes_tailA_not_last (n k : ℕ) (x : Omega n k 0)
    (hA : 6 ≤ x.val ∧ x.val < 5 + n) :
    commutator_g₁_g₂ n k 0 x = x := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  have hA' : 6 ≤ x.val ∧ x.val < 6 + n := ⟨hA.1, by omega⟩
  have hg₂x := g₂_fixes_tailA n k x hA'; rw [hg₂x]
  have hn : n ≥ 1 := by omega
  have hx_ge6 : x.val ≥ 6 := hA.1
  have hg₁x_tailA : 6 ≤ (g₁ n k 0 x).val ∧ (g₁ n k 0 x).val < 6 + n := by
    rcases g₁_maps_tailA n k hn x hA' with h | h
    · exact h
    · exfalso
      have hnd := g₁_list_nodup n k 0
      have hlen := g₁_cycle_length n k 0
      have hi_bound : x.val - 6 < n := by omega
      have hip1_bound : x.val - 6 + 1 < n := by omega
      have hpos1 : 4 + (x.val - 6) + 1 < (g₁CoreList n k 0 ++ tailAList n k 0).length := by
        rw [hlen]; omega
      have hpos : 4 + (x.val - 6) < (g₁CoreList n k 0 ++ tailAList n k 0).length := by
        rw [hlen]; omega
      have h_at : (g₁CoreList n k 0 ++ tailAList n k 0)[4 + (x.val - 6)]'hpos = x := by
        have := Transitivity.g₁_list_getElem_tail n k 0 ⟨x.val - 6, hi_bound⟩
        simp only [Fin.val_mk] at this
        rw [Fin.ext_iff]; simp only [this]; omega
      have h_fp : (g₁ n k 0) x = (g₁CoreList n k 0 ++ tailAList n k 0)[4 + (x.val - 6) + 1]'hpos1 := by
        unfold g₁; conv_lhs => rw [← h_at]
        exact List.formPerm_apply_lt_getElem _ hnd (4 + (x.val - 6)) hpos1
      have h_next : (g₁CoreList n k 0 ++ tailAList n k 0)[4 + (x.val - 6) + 1]'hpos1 =
          ⟨x.val + 1, by omega⟩ := by
        have := Transitivity.g₁_list_getElem_tail n k 0 ⟨x.val - 6 + 1, hip1_bound⟩
        simp only [Fin.val_mk] at this
        have heq : 4 + (x.val - 6) + 1 = 4 + (x.val - 6 + 1) := by ring
        rw [Fin.ext_iff]; simp only [heq] at this ⊢; simp only [this]; omega
      have h_next_val : ((g₁CoreList n k 0 ++ tailAList n k 0)[4 + (x.val - 6) + 1]'hpos1).val =
          x.val + 1 := by rw [h_next]
      have := congrArg Fin.val h_fp
      simp only [h_next_val] at this; omega
  have hg₂_inv := g₂_inv_fixes_tailA n k (g₁ n k 0 x) hg₁x_tailA
  rw [hg₂_inv, Perm.inv_apply_self]
end LemmaFeld.GroupTheory.AF.TailAFixing
