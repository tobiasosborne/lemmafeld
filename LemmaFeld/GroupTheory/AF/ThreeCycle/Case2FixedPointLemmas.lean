/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.ThreeCycle.Case2CommutatorLemmas

/-! Fixed-Point Lemmas for Case 2: k ≥ 1 -/

open Equiv Perm

namespace LemmaFeld.GroupTheory.AF.Case2FixedPointLemmas

open Case2ProductLemmas LemmaFeld.GroupTheory.AF.Case2CommutatorLemmas

-- ============================================
-- SECTION 1: n = 0 lemmas
-- ============================================

theorem g₁_fixes_tailB_n0 (k m : ℕ) (x : Omega 0 k m) (hx : 6 ≤ x.val) :
    g₁ 0 k m x = x := by
  unfold g₁
  have htail_empty : tailAList 0 k m = [] := by unfold tailAList List.finRange; rfl
  simp only [htail_empty, List.append_nil]
  apply List.formPerm_apply_of_notMem
  simp only [g₁CoreList, List.mem_cons, List.not_mem_nil, or_false, not_or]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega

theorem g₁_inv_fixes_tailB_n0 (k m : ℕ) (x : Omega 0 k m) (hx : 6 ≤ x.val) :
    (g₁ 0 k m)⁻¹ x = x := by
  have h := g₁_fixes_tailB_n0 k m x hx
  calc (g₁ 0 k m)⁻¹ x = (g₁ 0 k m)⁻¹ ((g₁ 0 k m) x) := by rw [h]
    _ = x := Equiv.symm_apply_apply _ _

theorem c₁₂_fixes_tailB_n0 (k m : ℕ) (x : Omega 0 k m) (hx : 6 ≤ x.val) :
    commutator_g₁_g₂ 0 k m x = x := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  -- g₁ fixes g₂(x) since g₂ maps tailB to tailB or core element 1 (which g₁ also fixes)
  have hg₂x_fixed_by_g₁ : g₁ 0 k m (g₂ 0 k m x) = g₂ 0 k m x := by
    by_cases h : (g₂ 0 k m x).val < 6
    · -- g₂(x) is a core element. For x ≥ 6, g₂(x) can only be 1 (last tailB wraps to 1)
      -- All other core elements would require x < 6 via g₂⁻¹
      have hx_recover : x = (g₂ 0 k m)⁻¹ (g₂ 0 k m x) := (Equiv.symm_apply_apply _ _).symm
      have heq1 : (g₂ 0 k m x).val = 1 := by
        interval_cases hv : (g₂ 0 k m x).val
        · -- case 0: g₂⁻¹(0) = 4, but x ≥ 6
          exfalso; rw [show g₂ 0 k m x = ⟨0, by omega⟩ from Fin.ext hv] at hx_recover
          simp only [g₂_inv_0_eq_4, Fin.ext_iff] at hx_recover; omega
        · rfl  -- case 1: valid
        · -- case 2: g₂⁻¹(2) = 2, but x ≥ 6
          exfalso; rw [show g₂ 0 k m x = ⟨2, by omega⟩ from Fin.ext hv] at hx_recover
          simp only [g₂_inv_fixes_2, Fin.ext_iff] at hx_recover; omega
        · -- case 3: g₂⁻¹(3) = 1, but x ≥ 6
          exfalso; rw [show g₂ 0 k m x = ⟨3, by omega⟩ from Fin.ext hv] at hx_recover
          simp only [g₂_inv_3_eq_1, Fin.ext_iff] at hx_recover; omega
        · -- case 4: g₂⁻¹(4) = 3, but x ≥ 6
          exfalso; rw [show g₂ 0 k m x = ⟨4, by omega⟩ from Fin.ext hv] at hx_recover
          simp only [g₂_inv_4_eq_3, Fin.ext_iff] at hx_recover; omega
        · -- case 5: g₂⁻¹(5) = 5, but x ≥ 6
          exfalso; rw [show g₂ 0 k m x = ⟨5, by omega⟩ from Fin.ext hv] at hx_recover
          simp only [g₂_inv_fixes_5, Fin.ext_iff] at hx_recover; omega
      have heq : g₂ 0 k m x = ⟨1, by omega⟩ := Fin.ext heq1
      rw [heq, g₁_fixes_1]
    · push_neg at h; exact g₁_fixes_tailB_n0 k m (g₂ 0 k m x) h
  rw [hg₂x_fixed_by_g₁]
  have h1 : (g₂ 0 k m)⁻¹ ((g₂ 0 k m) x) = x := Equiv.symm_apply_apply _ _
  rw [h1, g₁_inv_fixes_tailB_n0 k m x hx]

theorem c₁₂_inv_fixes_tailB_n0 (k m : ℕ) (x : Omega 0 k m) (hx : 6 ≤ x.val) :
    (commutator_g₁_g₂ 0 k m)⁻¹ x = x := by
  have h := c₁₂_fixes_tailB_n0 k m x hx
  calc (commutator_g₁_g₂ 0 k m)⁻¹ x
      = (commutator_g₁_g₂ 0 k m)⁻¹ ((commutator_g₁_g₂ 0 k m) x) := by rw [h]
    _ = x := Equiv.symm_apply_apply _ _

theorem g₂_0_eq_6_n0 (k m : ℕ) (hk : k ≥ 1) : g₂ 0 k m ⟨0, by omega⟩ = ⟨6, by omega⟩ := by
  unfold g₂
  have hnd := g₂_list_nodup 0 k m; have hlen := g₂_cycle_length 0 k m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 3 (by rw [hlen]; omega)
  simp only [g₂CoreList, tailBList, List.cons_append, List.nil_append,
    List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  convert h_fp using 2; simp only [List.getElem_map, List.getElem_finRange, Fin.coe_cast]

theorem g₂_inv_6_eq_0_n0 (k m : ℕ) (hk : k ≥ 1) :
    (g₂ 0 k m)⁻¹ ⟨6, by omega⟩ = ⟨0, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₂_0_eq_6_n0 k m hk).symm

theorem c₁₂_0_eq_2_n0 (k m : ℕ) (hk : k ≥ 1) :
    commutator_g₁_g₂ 0 k m ⟨0, by omega⟩ = ⟨2, by omega⟩ := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  rw [g₂_0_eq_6_n0 k m hk, g₁_fixes_tailB_n0 k m ⟨6, by omega⟩ (le_refl 6),
      g₂_inv_6_eq_0_n0 k m hk, g₁_inv_0_eq_2_n0]

theorem c₁₂_inv_2_eq_0_n0 (k m : ℕ) (hk : k ≥ 1) :
    (commutator_g₁_g₂ 0 k m)⁻¹ ⟨2, by omega⟩ = ⟨0, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (c₁₂_0_eq_2_n0 k m hk).symm

theorem iter_0_eq_4_n0 (k m : ℕ) (hk : k ≥ 1) :
    SymmetricCase2.iteratedComm_g₂' 0 k m ⟨0, by omega⟩ = ⟨4, by omega⟩ := by
  unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
  rw [g₂_0_eq_6_n0 k m hk, c₁₂_fixes_tailB_n0 k m ⟨6, by omega⟩ (le_refl 6),
      g₂_inv_6_eq_0_n0 k m hk, c₁₂_inv_0_eq_4]

theorem iter_4_eq_0_n0 (k m : ℕ) (hk : k ≥ 1) :
    SymmetricCase2.iteratedComm_g₂' 0 k m ⟨4, by omega⟩ = ⟨0, by omega⟩ := by
  unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
  rw [g₂_4_eq_0, c₁₂_0_eq_2_n0 k m hk, g₂_inv_fixes_2, c₁₂_inv_2_eq_0_n0 k m hk]

theorem sq_fixes_0_n0 (k m : ℕ) (hk : k ≥ 1) :
    (SymmetricCase2.iteratedComm_g₂' 0 k m ^ 2) ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  simp only [sq, Perm.mul_apply]; rw [iter_0_eq_4_n0 k m hk, iter_4_eq_0_n0 k m hk]

theorem sq_fixes_4_n0 (k m : ℕ) (hk : k ≥ 1) :
    (SymmetricCase2.iteratedComm_g₂' 0 k m ^ 2) ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
  simp only [sq, Perm.mul_apply]; rw [iter_4_eq_0_n0 k m hk, iter_0_eq_4_n0 k m hk]

theorem g₂_lastTailB_eq_1_n0 (k m : ℕ) (hk : k ≥ 1) :
    g₂ 0 k m ⟨5 + k, by omega⟩ = ⟨1, by omega⟩ := by
  unfold g₂
  have h := List.formPerm_apply_getLast (⟨1, by omega⟩ : Omega 0 k m)
              (⟨3, by omega⟩ :: ⟨4, by omega⟩ :: ⟨0, by omega⟩ :: (tailBList 0 k m))
  simp only [g₂CoreList, List.cons_append, List.nil_append] at h ⊢
  convert h using 2
  have hne : tailBList 0 k m ≠ [] := by unfold tailBList; simp [List.map_eq_nil_iff]; omega
  rw [List.getLast_cons_cons, List.getLast_cons_cons, List.getLast_cons_cons, List.getLast_cons hne]
  unfold tailBList; rw [List.getLast_map (by simp; omega)]
  have hlen : (List.finRange k).length = k := List.length_finRange
  have hidx : k - 1 < (List.finRange k).length := by rw [hlen]; omega
  rw [List.getLast_eq_getElem, List.getElem_finRange]
  simp only [Fin.ext_iff, Fin.coe_cast]; omega

theorem g₂_inv_1_eq_lastTailB_n0 (k m : ℕ) (hk : k ≥ 1) :
    (g₂ 0 k m)⁻¹ ⟨1, by omega⟩ = ⟨5 + k, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₂_lastTailB_eq_1_n0 k m hk).symm

theorem iter_5_eq_lastTailB_n0 (k m : ℕ) (hk : k ≥ 1) :
    SymmetricCase2.iteratedComm_g₂' 0 k m ⟨5, by omega⟩ = ⟨5 + k, by omega⟩ := by
  unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
  have h_bound : 6 ≤ (⟨5 + k, by omega⟩ : Omega 0 k m).val := by simp only [Fin.val_mk]; omega
  rw [g₂_fixes_5, c₁₂_5_eq_1, g₂_inv_1_eq_lastTailB_n0 k m hk,
      c₁₂_inv_fixes_tailB_n0 k m ⟨5 + k, by omega⟩ h_bound]

theorem iter_lastTailB_eq_5_n0 (k m : ℕ) (hk : k ≥ 1) :
    SymmetricCase2.iteratedComm_g₂' 0 k m ⟨5 + k, by omega⟩ = ⟨5, by omega⟩ := by
  unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
  rw [g₂_lastTailB_eq_1_n0 k m hk, c₁₂_1_eq_3, g₂_inv_3_eq_1, c₁₂_inv_1_eq_5]

theorem sq_fixes_5_n0 (k m : ℕ) (hk : k ≥ 1) :
    (SymmetricCase2.iteratedComm_g₂' 0 k m ^ 2) ⟨5, by omega⟩ = ⟨5, by omega⟩ := by
  simp only [sq, Perm.mul_apply]; rw [iter_5_eq_lastTailB_n0 k m hk, iter_lastTailB_eq_5_n0 k m hk]

theorem sq_fixes_lastTailB_n0 (k m : ℕ) (hk : k ≥ 1) :
    (SymmetricCase2.iteratedComm_g₂' 0 k m ^ 2) ⟨5 + k, by omega⟩ = ⟨5 + k, by omega⟩ := by
  simp only [sq, Perm.mul_apply]; rw [iter_lastTailB_eq_5_n0 k m hk, iter_5_eq_lastTailB_n0 k m hk]

-- ============================================
-- SECTION 2: n ≥ 1 lemmas (minimal set)
-- ============================================

theorem g₁_2_eq_6_n_ge1 (n k m : ℕ) (hn : n ≥ 1) :
    g₁ n k m ⟨2, by omega⟩ = ⟨6, by omega⟩ := by
  unfold g₁
  have hnd := g₁_list_nodup n k m; have hlen := g₁_cycle_length n k m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 3 (by rw [hlen]; omega)
  simp only [g₁CoreList, tailAList, List.cons_append, List.nil_append,
    List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  convert h_fp using 2; simp only [List.getElem_map, List.getElem_finRange, Fin.coe_cast]

theorem g₁_inv_6_eq_2_n_ge1 (n k m : ℕ) (hn : n ≥ 1) :
    (g₁ n k m)⁻¹ ⟨6, by omega⟩ = ⟨2, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₁_2_eq_6_n_ge1 n k m hn).symm

theorem g₂_fixes_6_n_ge1 (n k m : ℕ) (hn : n ≥ 1) :
    g₂ n k m ⟨6, by omega⟩ = ⟨6, by omega⟩ := by
  unfold g₂; apply List.formPerm_apply_of_notMem
  simp only [g₂CoreList, tailBList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

theorem g₂_inv_fixes_6_n_ge1 (n k m : ℕ) (hn : n ≥ 1) :
    (g₂ n k m)⁻¹ ⟨6, by omega⟩ = ⟨6, by omega⟩ := by
  have h := g₂_fixes_6_n_ge1 n k m hn
  calc (g₂ n k m)⁻¹ ⟨6, by omega⟩ = (g₂ n k m)⁻¹ ((g₂ n k m) ⟨6, by omega⟩) := by rw [h]
    _ = ⟨6, by omega⟩ := Equiv.symm_apply_apply _ _

theorem c₁₂_fixes_2_n_ge1 (n k m : ℕ) (hn : n ≥ 1) :
    commutator_g₁_g₂ n k m ⟨2, by omega⟩ = ⟨2, by omega⟩ := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  rw [g₂_fixes_2, g₁_2_eq_6_n_ge1 n k m hn, g₂_inv_fixes_6_n_ge1 n k m hn,
      g₁_inv_6_eq_2_n_ge1 n k m hn]

theorem iter_fixes_2_n_ge1 (n k m : ℕ) (hn : n ≥ 1) :
    SymmetricCase2.iteratedComm_g₂' n k m ⟨2, by omega⟩ = ⟨2, by omega⟩ := by
  unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
  rw [g₂_fixes_2, c₁₂_fixes_2_n_ge1 n k m hn, g₂_inv_fixes_2]
  rw [Perm.inv_eq_iff_eq]; exact (c₁₂_fixes_2_n_ge1 n k m hn).symm

theorem sq_fixes_2_n_ge1 (n k m : ℕ) (hn : n ≥ 1) :
    (SymmetricCase2.iteratedComm_g₂' n k m ^ 2) ⟨2, by omega⟩ = ⟨2, by omega⟩ := by
  simp only [sq, Perm.mul_apply]; rw [iter_fixes_2_n_ge1 n k m hn, iter_fixes_2_n_ge1 n k m hn]

theorem g₂_0_eq_firstTailB (n k m : ℕ) (hk : k ≥ 1) :
    g₂ n k m ⟨0, by omega⟩ = ⟨6 + n, by omega⟩ := by
  unfold g₂
  have hnd := g₂_list_nodup n k m; have hlen := g₂_cycle_length n k m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 3 (by rw [hlen]; omega)
  simp only [g₂CoreList, tailBList, List.cons_append, List.nil_append,
    List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  convert h_fp using 2; simp only [List.getElem_map, List.getElem_finRange, Fin.coe_cast]; omega

theorem g₂_inv_firstTailB_eq_0 (n k m : ℕ) (hk : k ≥ 1) :
    (g₂ n k m)⁻¹ ⟨6 + n, by omega⟩ = ⟨0, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₂_0_eq_firstTailB n k m hk).symm

theorem g₁_fixes_firstTailB (n k m : ℕ) (hk : k ≥ 1) :
    g₁ n k m ⟨6 + n, by omega⟩ = ⟨6 + n, by omega⟩ := by
  unfold g₁; apply List.formPerm_apply_of_notMem
  simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

theorem g₁_inv_fixes_firstTailB (n k m : ℕ) (hk : k ≥ 1) :
    (g₁ n k m)⁻¹ ⟨6 + n, by omega⟩ = ⟨6 + n, by omega⟩ := by
  have h := g₁_fixes_firstTailB n k m hk
  calc (g₁ n k m)⁻¹ ⟨6 + n, by omega⟩
      = (g₁ n k m)⁻¹ ((g₁ n k m) ⟨6 + n, by omega⟩) := by rw [h]
    _ = ⟨6 + n, by omega⟩ := Equiv.symm_apply_apply _ _

theorem c₁₂_0_eq_5plusn (n k m : ℕ) (hn : n ≥ 1) (hk : k ≥ 1) :
    commutator_g₁_g₂ n k m ⟨0, by omega⟩ = ⟨5 + n, by omega⟩ := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  rw [g₂_0_eq_firstTailB n k m hk, g₁_fixes_firstTailB n k m hk, g₂_inv_firstTailB_eq_0 n k m hk]
  have hlast := Case2CommutatorLemmas.g₁_5plusn_eq_0 n k m hn
  rw [Perm.inv_eq_iff_eq]; exact hlast.symm

theorem c₁₂_inv_5plusn_eq_0 (n k m : ℕ) (hn : n ≥ 1) (hk : k ≥ 1) :
    (commutator_g₁_g₂ n k m)⁻¹ ⟨5 + n, by omega⟩ = ⟨0, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (c₁₂_0_eq_5plusn n k m hn hk).symm

theorem g₂_fixes_5plusn (n k m : ℕ) (hn : n ≥ 1) :
    g₂ n k m ⟨5 + n, by omega⟩ = ⟨5 + n, by omega⟩ := by
  unfold g₂; apply List.formPerm_apply_of_notMem
  simp only [g₂CoreList, tailBList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

theorem g₂_inv_fixes_5plusn (n k m : ℕ) (hn : n ≥ 1) :
    (g₂ n k m)⁻¹ ⟨5 + n, by omega⟩ = ⟨5 + n, by omega⟩ := by
  have h := g₂_fixes_5plusn n k m hn
  calc (g₂ n k m)⁻¹ ⟨5 + n, by omega⟩
      = (g₂ n k m)⁻¹ ((g₂ n k m) ⟨5 + n, by omega⟩) := by rw [h]
    _ = ⟨5 + n, by omega⟩ := Equiv.symm_apply_apply _ _

theorem iter_0_eq_4_n_ge1 (n k m : ℕ) (hn : n ≥ 1) (hk : k ≥ 1) :
    SymmetricCase2.iteratedComm_g₂' n k m ⟨0, by omega⟩ = ⟨4, by omega⟩ := by
  unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
  rw [g₂_0_eq_firstTailB n k m hk]
  -- c₁₂ fixes 6+n since it's in tailB (g₁ fixes tailB, and g₂(6+n) stays in tailB or wraps to 1)
  have hc₁₂_fix : commutator_g₁_g₂ n k m ⟨6 + n, by omega⟩ = ⟨6 + n, by omega⟩ := by
    unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
    -- Work from inside out: g₂(6+n) → g₁(...) → g₂⁻¹(...) → g₁⁻¹(...)
    by_cases hk1 : k = 1
    · -- k = 1: g₂(6+n) = 1 (last tailB wraps to cycle start)
      subst hk1
      have hg₂_first : g₂ n 1 m ⟨6 + n, by omega⟩ = ⟨1, by omega⟩ := by
        unfold g₂
        have h := List.formPerm_apply_getLast (⟨1, by omega⟩ : Omega n 1 m)
                    (⟨3, by omega⟩ :: ⟨4, by omega⟩ :: ⟨0, by omega⟩ :: (tailBList n 1 m))
        simp only [g₂CoreList, List.cons_append, List.nil_append] at h ⊢; convert h using 2
      rw [hg₂_first, g₁_fixes_1]
      have hg₂_inv_1 : (g₂ n 1 m)⁻¹ ⟨1, by omega⟩ = ⟨6 + n, by omega⟩ := by
        rw [Perm.inv_eq_iff_eq]; exact hg₂_first.symm
      rw [hg₂_inv_1, g₁_inv_fixes_firstTailB n 1 m (le_refl 1)]
    · -- k ≥ 2: g₂(6+n) = 7+n (next in tailB)
      have hk2 : k ≥ 2 := by omega
      have hg₂_first : g₂ n k m ⟨6 + n, by omega⟩ = ⟨7 + n, by omega⟩ := by
        unfold g₂
        have hnd := g₂_list_nodup n k m; have hlen := g₂_cycle_length n k m
        have hidx : 4 + 1 < (g₂CoreList n k m ++ tailBList n k m).length := by rw [hlen]; omega
        have h_fp := List.formPerm_apply_lt_getElem _ hnd 4 hidx
        simp only [g₂CoreList, tailBList, List.cons_append, List.nil_append,
          List.getElem_cons_succ] at h_fp
        convert h_fp using 2
        · have hlen' : (List.finRange k).length = k := List.length_finRange
          have hidx' : 0 < k := by omega
          simp only [List.getElem_map, List.getElem_finRange, Fin.ext_iff, Fin.coe_cast]; omega
        · have hlen' : (List.finRange k).length = k := List.length_finRange
          have hidx' : 0 < k := by omega
          simp only [List.getElem_map, List.getElem_finRange, Fin.ext_iff, Fin.coe_cast]; omega
      rw [hg₂_first]
      have hg₁_fix_7n : g₁ n k m ⟨7 + n, by omega⟩ = ⟨7 + n, by omega⟩ := by
        unfold g₁; apply List.formPerm_apply_of_notMem
        simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false, List.mem_map, List.mem_finRange, not_or]
        constructor
        · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
        · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega
      rw [hg₁_fix_7n]
      have hg₂_inv_7n : (g₂ n k m)⁻¹ ⟨7 + n, by omega⟩ = ⟨6 + n, by omega⟩ := by
        rw [Perm.inv_eq_iff_eq]; exact hg₂_first.symm
      rw [hg₂_inv_7n, g₁_inv_fixes_firstTailB n k m hk]
  rw [hc₁₂_fix, g₂_inv_firstTailB_eq_0 n k m hk, c₁₂_inv_0_eq_4]

theorem iter_4_eq_0_n_ge1 (n k m : ℕ) (hn : n ≥ 1) (hk : k ≥ 1) :
    SymmetricCase2.iteratedComm_g₂' n k m ⟨4, by omega⟩ = ⟨0, by omega⟩ := by
  unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
  rw [g₂_4_eq_0, c₁₂_0_eq_5plusn n k m hn hk, g₂_inv_fixes_5plusn n k m hn,
      c₁₂_inv_5plusn_eq_0 n k m hn hk]

theorem sq_fixes_0_n_ge1 (n k m : ℕ) (hn : n ≥ 1) (hk : k ≥ 1) :
    (SymmetricCase2.iteratedComm_g₂' n k m ^ 2) ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  simp only [sq, Perm.mul_apply]; rw [iter_0_eq_4_n_ge1 n k m hn hk, iter_4_eq_0_n_ge1 n k m hn hk]

theorem sq_fixes_4_n_ge1 (n k m : ℕ) (hn : n ≥ 1) (hk : k ≥ 1) :
    (SymmetricCase2.iteratedComm_g₂' n k m ^ 2) ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
  simp only [sq, Perm.mul_apply]; rw [iter_4_eq_0_n_ge1 n k m hn hk, iter_0_eq_4_n_ge1 n k m hn hk]

-- Simpler tail lemmas
theorem g₂_fixes_tailA (n k m : ℕ) (x : Omega n k m) (hlo : 6 ≤ x.val) (hhi : x.val < 6 + n) :
    g₂ n k m x = x := by
  unfold g₂; apply List.formPerm_apply_of_notMem
  simp only [g₂CoreList, tailBList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

theorem g₂_inv_fixes_tailA (n k m : ℕ) (x : Omega n k m) (hlo : 6 ≤ x.val) (hhi : x.val < 6 + n) :
    (g₂ n k m)⁻¹ x = x := by
  have h := g₂_fixes_tailA n k m x hlo hhi
  calc (g₂ n k m)⁻¹ x = (g₂ n k m)⁻¹ ((g₂ n k m) x) := by rw [h]
    _ = x := Equiv.symm_apply_apply _ _

-- Note: For 6 ≤ x.val < 5 + n, we need n ≥ 2. When n ≤ 1, the range is empty.
-- The proof uses that g₂ fixes tailA elements, and g₁ maps strict tailA to other tailA elements.
theorem c₁₂_fixes_tailA_strict (n k m : ℕ) (x : Omega n k m) (hlo : 6 ≤ x.val) (hhi : x.val < 5 + n) :
    commutator_g₁_g₂ n k m x = x := by
  -- Derive n ≥ 2 from the hypotheses
  have hn2 : n ≥ 2 := by omega
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  have hhi' : x.val < 6 + n := by omega
  -- g₂ fixes x (x ∈ tailA, disjoint from g₂'s support)
  have hg₂_fix := g₂_fixes_tailA n k m x hlo hhi'
  -- Key: g₁(x) is NOT in g₂'s support, so g₂ fixes g₁(x)
  -- g₂'s support is {1, 3, 4, 0} ∪ tailB. We show g₁(x) ∉ this set.
  -- For x in strict tailA, g₁(x) ≠ 0 (since x is not the last tailA element, g₁ doesn't wrap)
  -- And g₁(x) ∉ {1, 3, 4} (g₁ only maps to these from specific predecessors)
  -- And g₁(x) ∉ tailB (g₁'s cycle doesn't touch tailB)
  have hg₂_inv_fix_g₁x : (g₂ n k m)⁻¹ (g₁ n k m x) = g₁ n k m x := by
    have hg₁x_not_in_g₂ : g₁ n k m x ∉ (g₂CoreList n k m ++ tailBList n k m) := by
      intro hmem
      simp only [g₂CoreList, tailBList, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, List.mem_map, List.mem_finRange] at hmem
      -- g₁(x) is in g₁'s cycle, which is [0, 5, 3, 2, tailA]
      -- Since x ∈ tailA (with value 6 ≤ x.val < 5+n), g₁(x) is either in tailA or = 0
      -- But x < 5+n means x ≠ last tailA element, so g₁(x) ≠ 0
      -- Therefore g₁(x) ∈ tailA with value ≥ 6
      -- This contradicts g₁(x) ∈ {1, 3, 4, 0} ∪ tailB
      -- First handle disjunction on core elements
      rcases hmem with hcore | htail
      · -- g₁(x) ∈ {1, 3, 4, 0}
        rcases hcore with h1 | h3 | h4 | h0
        · -- g₁(x) = 1: g₁⁻¹(1) = 1, but x.val ≥ 6
          have hx_pre : x = (g₁ n k m)⁻¹ (g₁ n k m x) := (Equiv.symm_apply_apply _ _).symm
          rw [h1] at hx_pre
          have := g₁_inv_fixes_1 n k m
          simp only [this, Fin.ext_iff] at hx_pre; omega
        · -- g₁(x) = 3: g₁⁻¹(3) = 5, but x.val ≥ 6
          have hx_pre : x = (g₁ n k m)⁻¹ (g₁ n k m x) := (Equiv.symm_apply_apply _ _).symm
          rw [h3] at hx_pre
          have := g₁_inv_3_eq_5 n k m
          simp only [this, Fin.ext_iff] at hx_pre; omega
        · -- g₁(x) = 4: g₁⁻¹(4) = 4, but x.val ≥ 6
          have hx_pre : x = (g₁ n k m)⁻¹ (g₁ n k m x) := (Equiv.symm_apply_apply _ _).symm
          rw [h4] at hx_pre
          have := g₁_inv_fixes_4 n k m
          simp only [this, Fin.ext_iff] at hx_pre; omega
        · -- g₁(x) = 0: g₁⁻¹(0) = 5+n, but x.val < 5+n
          have hx_pre : x = (g₁ n k m)⁻¹ (g₁ n k m x) := (Equiv.symm_apply_apply _ _).symm
          rw [h0] at hx_pre
          have := g₁_inv_0_eq_5plusn n k m (by omega : n ≥ 1)
          simp only [this, Fin.ext_iff] at hx_pre; omega
      · -- g₁(x) ∈ tailB
        obtain ⟨i, _, hi⟩ := htail
        simp only [Fin.ext_iff] at hi
        have hx_pre : x = (g₁ n k m)⁻¹ (g₁ n k m x) := (Equiv.symm_apply_apply _ _).symm
        have htailB_fixed := g₁_inv_fixes_tailB n k m (g₁ n k m x) ⟨by omega, by omega⟩
        simp only [htailB_fixed, Fin.ext_iff] at hx_pre
        omega
    have hg₂_fix_g₁x : g₂ n k m (g₁ n k m x) = g₁ n k m x := by
      unfold g₂; exact List.formPerm_apply_of_notMem hg₁x_not_in_g₂
    have h := hg₂_fix_g₁x
    calc (g₂ n k m)⁻¹ (g₁ n k m x) = (g₂ n k m)⁻¹ (g₂ n k m (g₁ n k m x)) := by rw [h]
      _ = g₁ n k m x := Equiv.symm_apply_apply _ _
  -- Now compute: c₁₂(x) = g₁⁻¹(g₂⁻¹(g₁(g₂(x)))) = g₁⁻¹(g₂⁻¹(g₁(x))) = g₁⁻¹(g₁(x)) = x
  rw [hg₂_fix, hg₂_inv_fix_g₁x]
  exact Equiv.symm_apply_apply (g₁ n k m) x

theorem sq_fixes_tailC_n_ge1 (n k m : ℕ) (x : Omega n k m) (hlo : 6 + n + k ≤ x.val) :
    (SymmetricCase2.iteratedComm_g₂' n k m ^ 2) x = x := by
  have hg₁_fix : g₁ n k m x = x := by
    unfold g₁; apply List.formPerm_apply_of_notMem
    simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map, List.mem_finRange, not_or]
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
    · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega
  have hg₂_fix : g₂ n k m x = x := by
    unfold g₂; apply List.formPerm_apply_of_notMem
    simp only [g₂CoreList, tailBList, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map, List.mem_finRange, not_or]
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
    · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega
  have hg₁_inv_fix : (g₁ n k m)⁻¹ x = x := by
    calc (g₁ n k m)⁻¹ x = (g₁ n k m)⁻¹ ((g₁ n k m) x) := by rw [hg₁_fix]
      _ = x := Equiv.symm_apply_apply _ _
  have hg₂_inv_fix : (g₂ n k m)⁻¹ x = x := by
    calc (g₂ n k m)⁻¹ x = (g₂ n k m)⁻¹ ((g₂ n k m) x) := by rw [hg₂_fix]
      _ = x := Equiv.symm_apply_apply _ _
  -- c₁₂(x) = g₁⁻¹(g₂⁻¹(g₁(g₂(x)))) = x since all fix x
  have hc₁₂_fix : commutator_g₁_g₂ n k m x = x := by
    unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
    rw [hg₂_fix, hg₁_fix, hg₂_inv_fix, hg₁_inv_fix]
  have hc₁₂_inv_fix : (commutator_g₁_g₂ n k m)⁻¹ x = x := by
    calc (commutator_g₁_g₂ n k m)⁻¹ x
        = (commutator_g₁_g₂ n k m)⁻¹ ((commutator_g₁_g₂ n k m) x) := by rw [hc₁₂_fix]
      _ = x := Equiv.symm_apply_apply _ _
  -- iter(x) = c₁₂⁻¹(g₂⁻¹(c₁₂(g₂(x)))) = x since all fix x
  have hiter_fix : SymmetricCase2.iteratedComm_g₂' n k m x = x := by
    unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
    rw [hg₂_fix, hc₁₂_fix, hg₂_inv_fix, hc₁₂_inv_fix]
  simp only [sq, Perm.mul_apply, hiter_fix]

-- g₁ fixes all tailB elements for any n
theorem g₁_fixes_tailB_general (n k m : ℕ) (x : Omega n k m)
    (hlo : 6 + n ≤ x.val) (hhi : x.val < 6 + n + k) :
    g₁ n k m x = x := by
  unfold g₁; apply List.formPerm_apply_of_notMem
  simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

theorem g₁_inv_fixes_tailB_general (n k m : ℕ) (x : Omega n k m)
    (hlo : 6 + n ≤ x.val) (hhi : x.val < 6 + n + k) :
    (g₁ n k m)⁻¹ x = x := by
  have h := g₁_fixes_tailB_general n k m x hlo hhi
  calc (g₁ n k m)⁻¹ x = (g₁ n k m)⁻¹ ((g₁ n k m) x) := by rw [h]
    _ = x := Equiv.symm_apply_apply _ _

-- c₁₂ fixes all tailB elements for any n, k ≥ 1
-- Proof: g₂ maps tailB to tailB (or to 1), g₁ fixes tailB and 1
theorem c₁₂_fixes_tailB_general (n k m : ℕ) (hk : k ≥ 1) (x : Omega n k m)
    (hlo : 6 + n ≤ x.val) (hhi : x.val < 6 + n + k) :
    commutator_g₁_g₂ n k m x = x := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  -- Key insight: g₂(x) is either in tailB or = 1, and g₁ fixes both
  have hg₂x_fixed_by_g₁ : g₁ n k m (g₂ n k m x) = g₂ n k m x := by
    by_cases h : (g₂ n k m x).val < 6
    · -- g₂(x) is a core element. For tailB, g₂(x) can only be 1 (lastTailB wraps)
      have hx_recover : x = (g₂ n k m)⁻¹ (g₂ n k m x) := (Equiv.symm_apply_apply _ _).symm
      have heq1 : (g₂ n k m x).val = 1 := by
        interval_cases hv : (g₂ n k m x).val
        · -- g₂⁻¹(0) = 4, but x ≥ 6+n
          exfalso; rw [show g₂ n k m x = ⟨0, by omega⟩ from Fin.ext hv] at hx_recover
          simp only [Case2ProductLemmas.g₂_inv_0_eq_4, Fin.ext_iff] at hx_recover; omega
        · rfl
        · -- g₂⁻¹(2) = 2, but x ≥ 6+n
          exfalso; rw [show g₂ n k m x = ⟨2, by omega⟩ from Fin.ext hv] at hx_recover
          simp only [Case2ProductLemmas.g₂_inv_fixes_2, Fin.ext_iff] at hx_recover; omega
        · -- g₂⁻¹(3) = 1, but x ≥ 6+n
          exfalso; rw [show g₂ n k m x = ⟨3, by omega⟩ from Fin.ext hv] at hx_recover
          simp only [Case2ProductLemmas.g₂_inv_3_eq_1, Fin.ext_iff] at hx_recover; omega
        · -- g₂⁻¹(4) = 3, but x ≥ 6+n
          exfalso; rw [show g₂ n k m x = ⟨4, by omega⟩ from Fin.ext hv] at hx_recover
          simp only [Case2ProductLemmas.g₂_inv_4_eq_3, Fin.ext_iff] at hx_recover; omega
        · -- g₂⁻¹(5) = 5, but x ≥ 6+n
          exfalso; rw [show g₂ n k m x = ⟨5, by omega⟩ from Fin.ext hv] at hx_recover
          simp only [Case2ProductLemmas.g₂_inv_fixes_5, Fin.ext_iff] at hx_recover; omega
      have heq : g₂ n k m x = ⟨1, by omega⟩ := Fin.ext heq1
      rw [heq, g₁_fixes_1]
    · -- g₂(x) ≥ 6, need to show it's in tailB range (6+n ≤ g₂(x) < 6+n+k)
      push_neg at h
      -- g₂(x) must be ≥ 6+n since g₂ maps tailB to tailB or 1
      -- and 6 ≤ g₂(x) < 6+n would mean g₂(x) is in tailA, contradiction
      have hg₂x_lo : 6 + n ≤ (g₂ n k m x).val := by
        by_contra hbad; push_neg at hbad
        -- g₂(x) ∈ tailA means g₂⁻¹(g₂(x)) = g₂(x) since g₂ fixes tailA
        have htailA : g₂ n k m (g₂ n k m x) = g₂ n k m x := g₂_fixes_tailA n k m (g₂ n k m x) h hbad
        have hx_eq : x = (g₂ n k m)⁻¹ (g₂ n k m x) := (Equiv.symm_apply_apply _ _).symm
        -- So x = g₂⁻¹(g₂(x)) = g₂(x), but x ≥ 6+n and g₂(x) < 6+n, contradiction
        have hg₂_inv_fix : (g₂ n k m)⁻¹ (g₂ n k m x) = g₂ n k m x := g₂_inv_fixes_tailA n k m (g₂ n k m x) h hbad
        rw [hg₂_inv_fix] at hx_eq
        have := congrArg Fin.val hx_eq
        omega
      have hg₂x_hi : (g₂ n k m x).val < 6 + n + k := by
        by_contra hbad; push_neg at hbad
        -- g₂(x) ∈ tailC means g₂ fixes g₂(x)
        -- First establish that g₂(x) is definitely ≥ 6+n+k
        have hg₂x_ge : (g₂ n k m x).val ≥ 6 + n + k := hbad
        have htailC : g₂ n k m (g₂ n k m x) = g₂ n k m x := by
          unfold g₂; apply List.formPerm_apply_of_notMem
          simp only [g₂CoreList, tailBList, List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false, List.mem_map, List.mem_finRange, not_or]
          refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
          · intro hh; simp only [Fin.ext_iff] at hh
            have heq : (g₂ n k m x).val = 1 := hh
            have hge : (g₂ n k m x).val ≥ 6 + n + k := hg₂x_ge; omega
          · intro hh; simp only [Fin.ext_iff] at hh
            have heq : (g₂ n k m x).val = 3 := hh
            have hge : (g₂ n k m x).val ≥ 6 + n + k := hg₂x_ge; omega
          · intro hh; simp only [Fin.ext_iff] at hh
            have heq : (g₂ n k m x).val = 4 := hh
            have hge : (g₂ n k m x).val ≥ 6 + n + k := hg₂x_ge; omega
          · intro hh; simp only [Fin.ext_iff] at hh
            have heq : (g₂ n k m x).val = 0 := hh
            have hge : (g₂ n k m x).val ≥ 6 + n + k := hg₂x_ge; omega
          · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi
            have heq : (g₂ n k m x).val = 6 + n + i.val := hi.symm
            have hge : (g₂ n k m x).val ≥ 6 + n + k := hg₂x_ge
            have hik : i.val < k := i.isLt; omega
        have hx_eq : x = (g₂ n k m)⁻¹ (g₂ n k m x) := (Equiv.symm_apply_apply _ _).symm
        have hfix : (g₂ n k m)⁻¹ (g₂ n k m x) = g₂ n k m x := by
          calc (g₂ n k m)⁻¹ (g₂ n k m x) = (g₂ n k m)⁻¹ (g₂ n k m (g₂ n k m x)) := by rw [htailC]
            _ = g₂ n k m x := Equiv.symm_apply_apply _ _
        rw [hfix] at hx_eq
        have := congrArg Fin.val hx_eq; omega
      exact g₁_fixes_tailB_general n k m (g₂ n k m x) hg₂x_lo hg₂x_hi
  rw [hg₂x_fixed_by_g₁]
  have h1 : (g₂ n k m)⁻¹ ((g₂ n k m) x) = x := Equiv.symm_apply_apply _ _
  rw [h1, g₁_inv_fixes_tailB_general n k m x hlo hhi]

theorem c₁₂_inv_fixes_tailB_general (n k m : ℕ) (hk : k ≥ 1) (x : Omega n k m)
    (hlo : 6 + n ≤ x.val) (hhi : x.val < 6 + n + k) :
    (commutator_g₁_g₂ n k m)⁻¹ x = x := by
  have h := c₁₂_fixes_tailB_general n k m hk x hlo hhi
  calc (commutator_g₁_g₂ n k m)⁻¹ x
      = (commutator_g₁_g₂ n k m)⁻¹ ((commutator_g₁_g₂ n k m) x) := by rw [h]
    _ = x := Equiv.symm_apply_apply _ _

-- For n ≥ 1: g₂(lastTailB) = 1 where lastTailB = 5+n+k
theorem g₂_lastTailB_eq_1_n_ge1 (n k m : ℕ) (hn : n ≥ 1) (hk : k ≥ 1) :
    g₂ n k m ⟨5 + n + k, by omega⟩ = ⟨1, by omega⟩ := by
  unfold g₂
  have h := List.formPerm_apply_getLast (⟨1, by omega⟩ : Omega n k m)
              (⟨3, by omega⟩ :: ⟨4, by omega⟩ :: ⟨0, by omega⟩ :: (tailBList n k m))
  simp only [g₂CoreList, List.cons_append, List.nil_append] at h ⊢
  convert h using 2
  have hne : tailBList n k m ≠ [] := by unfold tailBList; simp [List.map_eq_nil_iff]; omega
  rw [List.getLast_cons_cons, List.getLast_cons_cons, List.getLast_cons_cons, List.getLast_cons hne]
  unfold tailBList; rw [List.getLast_map (by simp; omega)]
  rw [List.getLast_eq_getElem, List.getElem_finRange]
  simp only [Fin.ext_iff, Fin.coe_cast, List.length_finRange, Fin.val_mk]; omega

theorem g₂_inv_1_eq_lastTailB_n_ge1 (n k m : ℕ) (hn : n ≥ 1) (hk : k ≥ 1) :
    (g₂ n k m)⁻¹ ⟨1, by omega⟩ = ⟨5 + n + k, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₂_lastTailB_eq_1_n_ge1 n k m hn hk).symm

-- iter(5) = lastTailB for n ≥ 1
theorem iter_5_eq_lastTailB_n_ge1 (n k m : ℕ) (hn : n ≥ 1) (hk : k ≥ 1) :
    SymmetricCase2.iteratedComm_g₂' n k m ⟨5, by omega⟩ = ⟨5 + n + k, by omega⟩ := by
  unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
  have hlo : 6 + n ≤ (⟨5 + n + k, (by omega : 5 + n + k < 6 + n + k + m)⟩ : Omega n k m).val := by
    simp only [Fin.val_mk]; omega
  have hhi : (⟨5 + n + k, (by omega : 5 + n + k < 6 + n + k + m)⟩ : Omega n k m).val < 6 + n + k := by
    simp only [Fin.val_mk]; omega
  rw [g₂_fixes_5, c₁₂_5_eq_1, g₂_inv_1_eq_lastTailB_n_ge1 n k m hn hk,
      c₁₂_inv_fixes_tailB_general n k m hk ⟨5 + n + k, by omega⟩ hlo hhi]

-- iter(lastTailB) = 5 for n ≥ 1
theorem iter_lastTailB_eq_5_n_ge1 (n k m : ℕ) (hn : n ≥ 1) (hk : k ≥ 1) :
    SymmetricCase2.iteratedComm_g₂' n k m ⟨5 + n + k, by omega⟩ = ⟨5, by omega⟩ := by
  unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
  rw [g₂_lastTailB_eq_1_n_ge1 n k m hn hk, c₁₂_1_eq_3, g₂_inv_3_eq_1, c₁₂_inv_1_eq_5]

theorem sq_fixes_5_n_ge1 (n k m : ℕ) (hn : n ≥ 1) (hk : k ≥ 1) :
    (SymmetricCase2.iteratedComm_g₂' n k m ^ 2) ⟨5, by omega⟩ = ⟨5, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [iter_5_eq_lastTailB_n_ge1 n k m hn hk, iter_lastTailB_eq_5_n_ge1 n k m hn hk]

theorem sq_fixes_lastTailB_n_ge1 (n k m : ℕ) (hn : n ≥ 1) (hk : k ≥ 1) :
    (SymmetricCase2.iteratedComm_g₂' n k m ^ 2) ⟨5 + n + k, by omega⟩ = ⟨5 + n + k, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [iter_lastTailB_eq_5_n_ge1 n k m hn hk, iter_5_eq_lastTailB_n_ge1 n k m hn hk]

-- sq fixes all tailB elements for any n, k ≥ 1
-- For middle tailB: iter fixes x directly via c₁₂ fixing tailB
-- For lastTailB: iter(lastTailB) = 5, iter(5) = lastTailB, so sq fixes both
theorem sq_fixes_tailB_n_ge1 (n k m : ℕ) (x : Omega n k m)
    (hlo : 6 + n ≤ x.val) (hhi : x.val < 6 + n + k) :
    (SymmetricCase2.iteratedComm_g₂' n k m ^ 2) x = x := by
  have hk_ge1 : k ≥ 1 := by omega
  by_cases hn : n = 0
  · -- n = 0 case
    subst hn; simp only [add_zero] at hlo hhi ⊢
    by_cases hlast : x.val = 5 + k
    · have hx : x = ⟨5 + k, by omega⟩ := Fin.ext hlast
      rw [hx]; exact sq_fixes_lastTailB_n0 k m hk_ge1
    · -- middle tailB: iter fixes x directly
      have hiter : SymmetricCase2.iteratedComm_g₂' 0 k m x = x := by
        unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
        -- g₂(x) is in tailB (since x is not lastTailB, g₂(x) ≠ 1)
        have hg₂x_in_tailB : 6 ≤ (g₂ 0 k m x).val := by
          by_contra h_neg; push_neg at h_neg
          have hx_rec : x = (g₂ 0 k m)⁻¹ (g₂ 0 k m x) := (Equiv.symm_apply_apply _ _).symm
          interval_cases hv : (g₂ 0 k m x).val
          · rw [show g₂ 0 k m x = ⟨0, by omega⟩ from Fin.ext hv] at hx_rec
            rw [Case2ProductLemmas.g₂_inv_0_eq_4] at hx_rec; simp only [Fin.ext_iff] at hx_rec; omega
          · rw [show g₂ 0 k m x = ⟨1, by omega⟩ from Fin.ext hv] at hx_rec
            rw [g₂_inv_1_eq_lastTailB_n0 k m hk_ge1] at hx_rec; simp only [Fin.ext_iff] at hx_rec; omega
          · rw [show g₂ 0 k m x = ⟨2, by omega⟩ from Fin.ext hv] at hx_rec
            rw [Case2ProductLemmas.g₂_inv_fixes_2] at hx_rec; simp only [Fin.ext_iff] at hx_rec; omega
          · rw [show g₂ 0 k m x = ⟨3, by omega⟩ from Fin.ext hv] at hx_rec
            rw [Case2ProductLemmas.g₂_inv_3_eq_1] at hx_rec; simp only [Fin.ext_iff] at hx_rec; omega
          · rw [show g₂ 0 k m x = ⟨4, by omega⟩ from Fin.ext hv] at hx_rec
            rw [Case2ProductLemmas.g₂_inv_4_eq_3] at hx_rec; simp only [Fin.ext_iff] at hx_rec; omega
          · rw [show g₂ 0 k m x = ⟨5, by omega⟩ from Fin.ext hv] at hx_rec
            rw [Case2ProductLemmas.g₂_inv_fixes_5] at hx_rec; simp only [Fin.ext_iff] at hx_rec; omega
        have hg₂_simp : (g₂ 0 k m)⁻¹ ((g₂ 0 k m) x) = x := Equiv.symm_apply_apply _ _
        rw [c₁₂_fixes_tailB_n0 k m (g₂ 0 k m x) hg₂x_in_tailB, hg₂_simp,
            c₁₂_inv_fixes_tailB_n0 k m x hlo]
      simp only [sq, Perm.mul_apply, hiter]
  · -- n ≥ 1 case
    have hn_ge1 : n ≥ 1 := by omega
    by_cases hlast : x.val = 5 + n + k
    · have hx : x = ⟨5 + n + k, by omega⟩ := Fin.ext hlast
      rw [hx]; exact sq_fixes_lastTailB_n_ge1 n k m hn_ge1 hk_ge1
    · -- middle tailB: iter fixes x directly
      have hiter : SymmetricCase2.iteratedComm_g₂' n k m x = x := by
        unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
        -- g₂(x) is in tailB: 6+n ≤ g₂(x) < 6+n+k
        have hg₂x_in_tailB : 6 + n ≤ (g₂ n k m x).val ∧ (g₂ n k m x).val < 6 + n + k := by
          constructor
          · -- Lower bound: g₂(x) ≥ 6+n
            by_contra hbad; push_neg at hbad
            have hx_rec : x = (g₂ n k m)⁻¹ (g₂ n k m x) := (Equiv.symm_apply_apply _ _).symm
            by_cases h2 : (g₂ n k m x).val < 6
            · -- g₂(x) in core: check which one
              interval_cases hv : (g₂ n k m x).val
              · rw [show g₂ n k m x = ⟨0, by omega⟩ from Fin.ext hv] at hx_rec
                rw [Case2ProductLemmas.g₂_inv_0_eq_4] at hx_rec; simp only [Fin.ext_iff] at hx_rec; omega
              · rw [show g₂ n k m x = ⟨1, by omega⟩ from Fin.ext hv] at hx_rec
                rw [g₂_inv_1_eq_lastTailB_n_ge1 n k m hn_ge1 hk_ge1] at hx_rec
                simp only [Fin.ext_iff] at hx_rec; omega
              · rw [show g₂ n k m x = ⟨2, by omega⟩ from Fin.ext hv] at hx_rec
                rw [Case2ProductLemmas.g₂_inv_fixes_2] at hx_rec; simp only [Fin.ext_iff] at hx_rec; omega
              · rw [show g₂ n k m x = ⟨3, by omega⟩ from Fin.ext hv] at hx_rec
                rw [Case2ProductLemmas.g₂_inv_3_eq_1] at hx_rec; simp only [Fin.ext_iff] at hx_rec; omega
              · rw [show g₂ n k m x = ⟨4, by omega⟩ from Fin.ext hv] at hx_rec
                rw [Case2ProductLemmas.g₂_inv_4_eq_3] at hx_rec; simp only [Fin.ext_iff] at hx_rec; omega
              · rw [show g₂ n k m x = ⟨5, by omega⟩ from Fin.ext hv] at hx_rec
                rw [Case2ProductLemmas.g₂_inv_fixes_5] at hx_rec; simp only [Fin.ext_iff] at hx_rec; omega
            · -- g₂(x) in tailA: g₂ fixes tailA, so g₂⁻¹(g₂(x)) = g₂(x)
              push_neg at h2
              have hfix := g₂_inv_fixes_tailA n k m (g₂ n k m x) h2 hbad
              rw [hfix] at hx_rec
              have := congrArg Fin.val hx_rec; omega
          · -- Upper bound: g₂(x) < 6+n+k
            by_contra hbad; push_neg at hbad
            have hx_rec : x = (g₂ n k m)⁻¹ (g₂ n k m x) := (Equiv.symm_apply_apply _ _).symm
            -- g₂(x) in tailC: g₂ fixes tailC
            have hg₂x_ge : (g₂ n k m x).val ≥ 6 + n + k := hbad
            have hg₂_fix : g₂ n k m (g₂ n k m x) = g₂ n k m x := by
              unfold g₂; apply List.formPerm_apply_of_notMem
              simp only [g₂CoreList, tailBList, List.mem_append, List.mem_cons, List.not_mem_nil,
                or_false, List.mem_map, List.mem_finRange, not_or]
              refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
              · intro hh; simp only [Fin.ext_iff] at hh
                have heq : (g₂ n k m x).val = 1 := hh
                have hge : (g₂ n k m x).val ≥ 6 + n + k := hg₂x_ge; omega
              · intro hh; simp only [Fin.ext_iff] at hh
                have heq : (g₂ n k m x).val = 3 := hh
                have hge : (g₂ n k m x).val ≥ 6 + n + k := hg₂x_ge; omega
              · intro hh; simp only [Fin.ext_iff] at hh
                have heq : (g₂ n k m x).val = 4 := hh
                have hge : (g₂ n k m x).val ≥ 6 + n + k := hg₂x_ge; omega
              · intro hh; simp only [Fin.ext_iff] at hh
                have heq : (g₂ n k m x).val = 0 := hh
                have hge : (g₂ n k m x).val ≥ 6 + n + k := hg₂x_ge; omega
              · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi
                have heq : (g₂ n k m x).val = 6 + n + i.val := hi.symm
                have hge : (g₂ n k m x).val ≥ 6 + n + k := hg₂x_ge
                have hik : i.val < k := i.isLt; omega
            have hfix : (g₂ n k m)⁻¹ (g₂ n k m x) = g₂ n k m x := by
              calc (g₂ n k m)⁻¹ (g₂ n k m x) = (g₂ n k m)⁻¹ (g₂ n k m (g₂ n k m x)) := by rw [hg₂_fix]
                _ = g₂ n k m x := Equiv.symm_apply_apply _ _
            rw [hfix] at hx_rec
            have := congrArg Fin.val hx_rec; omega
        have hg₂_simp : (g₂ n k m)⁻¹ ((g₂ n k m) x) = x := Equiv.symm_apply_apply _ _
        rw [c₁₂_fixes_tailB_general n k m hk_ge1 (g₂ n k m x) hg₂x_in_tailB.1 hg₂x_in_tailB.2,
            hg₂_simp, c₁₂_inv_fixes_tailB_general n k m hk_ge1 x hlo hhi]
      simp only [sq, Perm.mul_apply, hiter]

end LemmaFeld.GroupTheory.AF.Case2FixedPointLemmas
