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
import LemmaFeld.GroupTheory.AF.ThreeCycle.TailALast
import LemmaFeld.GroupTheory.AF.Transitivity.Lemma05ListProps

/-!
# Tail Fixing Lemmas for 3-Cycle Extraction

Proves that c₁₂ and c₁₃ fix tail elements appropriately when m = 0.
-/

open Equiv Perm

namespace LemmaFeld.GroupTheory.AF.TailLemmas

-- ============================================
-- SECTION 1: g₁ fixes tailB elements
-- ============================================

/-- g₁ fixes tailB elements (outside its cycle) -/
theorem g₁_fixes_tailB (n k : ℕ) (x : Omega n k 0) (hx : 6 + n ≤ x.val) :
    g₁ n k 0 x = x := by
  unfold g₁
  apply List.formPerm_apply_of_notMem
  simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · constructor
    · simp only [Fin.ext_iff]; omega
    · constructor
      · simp only [Fin.ext_iff]; omega
      · constructor
        · simp only [Fin.ext_iff]; omega
        · simp only [Fin.ext_iff]; omega
  · intro ⟨i, _, hi⟩
    simp only [Fin.ext_iff] at hi
    omega

/-- g₁⁻¹ fixes tailB elements -/
theorem g₁_inv_fixes_tailB (n k : ℕ) (x : Omega n k 0) (hx : 6 + n ≤ x.val) :
    (g₁ n k 0)⁻¹ x = x := by
  have h := g₁_fixes_tailB n k x hx
  conv_lhs => rw [← h]; rw [Perm.inv_apply_self]

/-- g₁ fixes element 1 (since 1 is not in g₁'s cycle) -/
theorem g₁_fixes_1 (n k : ℕ) : g₁ n k 0 ⟨1, by omega⟩ = ⟨1, by omega⟩ := by
  unfold g₁
  apply List.formPerm_apply_of_notMem
  simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

/-- g₁⁻¹ fixes element 1 -/
theorem g₁_inv_fixes_1 (n k : ℕ) : (g₁ n k 0)⁻¹ ⟨1, by omega⟩ = ⟨1, by omega⟩ := by
  have h := g₁_fixes_1 n k
  conv_lhs => rw [← h]; rw [Perm.inv_apply_self]

-- ============================================
-- SECTION 3: c₁₂ fixes tailB elements
-- ============================================

/-- c₁₂ fixes tailB elements -/
theorem c₁₂_fixes_tailB (n k : ℕ) (x : Omega n k 0) (hx : 6 + n ≤ x.val) :
    commutator_g₁_g₂ n k 0 x = x := by
  have hk : k ≥ 1 := by omega
  have hx_bound : x.val ≤ 5 + n + k := by have := x.isLt; omega
  unfold commutator_g₁_g₂
  simp only [Perm.mul_apply]
  have hg₁ := g₁_fixes_tailB n k x hx
  have hg₁_inv : (g₁ n k 0)⁻¹ x = x := g₁_inv_fixes_tailB n k x hx
  by_cases hg₂x : 6 + n ≤ (g₂ n k 0 x).val
  · have hg₁_g₂x := g₁_fixes_tailB n k (g₂ n k 0 x) hg₂x
    rw [hg₁_g₂x, Perm.inv_apply_self, hg₁_inv]
  · push_neg at hg₂x
    have hnd := g₂_list_nodup n k 0
    have hlen : (g₂CoreList n k 0 ++ tailBList n k 0).length = 4 + k := g₂_cycle_length n k 0
    have hx_last : x.val = 5 + n + k := by
      by_contra hne
      have hx_not_last : x.val < 5 + n + k := by omega
      set i := x.val - (6 + n) with hi_def
      have hi_lt_k : i < k := by omega
      have hip1_lt_k : i + 1 < k := by omega
      have hpos : 4 + i < (g₂CoreList n k 0 ++ tailBList n k 0).length := by rw [hlen]; omega
      have hpos1 : 4 + i + 1 < (g₂CoreList n k 0 ++ tailBList n k 0).length := by rw [hlen]; omega
      have h_at_pos : (g₂CoreList n k 0 ++ tailBList n k 0)[4 + i]'hpos = x := by
        have := Transitivity.g₂_list_getElem_tail n k 0 ⟨i, hi_lt_k⟩
        simp only [Fin.val_mk] at this
        ext; rw [this]; simp only [hi_def]; omega
      have h_fp : (g₂ n k 0) x = (g₂CoreList n k 0 ++ tailBList n k 0)[4 + i + 1]'hpos1 := by
        unfold g₂; conv_lhs => rw [← h_at_pos]
        exact List.formPerm_apply_lt_getElem _ hnd (4 + i) hpos1
      have h_next : ((g₂CoreList n k 0 ++ tailBList n k 0)[4 + i + 1]'hpos1).val = 6 + n + (i + 1) := by
        have heq : 4 + i + 1 = 4 + (i + 1) := by ring
        have := Transitivity.g₂_list_getElem_tail n k 0 ⟨i + 1, hip1_lt_k⟩
        simp only [Fin.val_mk, heq] at this ⊢; rw [this]
      rw [h_fp] at hg₂x; omega
    have hx_eq : x = ⟨5 + n + k, by omega⟩ := Fin.ext hx_last
    rw [hx_eq]; unfold g₂
    have h_last_pos : 3 + k < (g₂CoreList n k 0 ++ tailBList n k 0).length := by rw [hlen]; omega
    have h_at_last : (g₂CoreList n k 0 ++ tailBList n k 0)[3 + k]'h_last_pos = ⟨5 + n + k, by omega⟩ := by
      have heq : 3 + k = 4 + (k - 1) := by omega
      have hkm1 : k - 1 < k := by omega
      have := Transitivity.g₂_list_getElem_tail n k 0 ⟨k - 1, hkm1⟩
      simp only [Fin.val_mk, heq] at this ⊢
      ext; simp only [this, Fin.val_mk]; omega
    have h0_pos' : 0 < (g₂CoreList n k 0 ++ tailBList n k 0).length := by rw [hlen]; omega
    have h_at_0 : (g₂CoreList n k 0 ++ tailBList n k 0)[0]'h0_pos' = ⟨1, by omega⟩ := by
      simp only [g₂CoreList, List.cons_append, List.getElem_cons_zero]
    have h_mod : (3 + k + 1) % (g₂CoreList n k 0 ++ tailBList n k 0).length = 0 := by
      simp only [hlen]
      have : 3 + k + 1 = 4 + k := by omega
      simp only [this, Nat.mod_self]
    have h_fp := List.formPerm_apply_getElem (g₂CoreList n k 0 ++ tailBList n k 0)
      hnd (3 + k) h_last_pos
    simp only [h_mod] at h_fp
    rw [h_at_last] at h_fp
    have h_at_0' : (g₂CoreList n k 0 ++ tailBList n k 0)[0]'(by rw [hlen]; omega) =
        (g₂CoreList n k 0 ++ tailBList n k 0)[0]'h0_pos' := rfl
    rw [h_at_0', h_at_0] at h_fp
    have hg₂x_val : ((g₂CoreList n k 0 ++ tailBList n k 0).formPerm ⟨5 + n + k, by omega⟩).val = 1 :=
      congrArg Fin.val h_fp
    have hg₂x_eq : (g₂CoreList n k 0 ++ tailBList n k 0).formPerm ⟨5 + n + k, by omega⟩ =
        ⟨1, by omega⟩ := Fin.ext hg₂x_val
    rw [hg₂x_eq, g₁_fixes_1 n k]
    have hg₂_inv_1 : (g₂CoreList n k 0 ++ tailBList n k 0).formPerm⁻¹ ⟨1, by omega⟩ =
        ⟨5 + n + k, by omega⟩ := by
      rw [Perm.inv_eq_iff_eq]; exact hg₂x_eq.symm
    rw [hg₂_inv_1]
    have : 6 + n ≤ 5 + n + k := by omega
    exact g₁_inv_fixes_tailB n k ⟨5 + n + k, by omega⟩ this

-- ============================================
-- SECTION 4: c₁₃⁻¹ fixes tailB when m = 0
-- ============================================

/-- c₁₃⁻¹ fixes tailB elements when m = 0 -/
theorem c₁₃_inv_fixes_tailB (n k : ℕ) (x : Omega n k 0) (hx : 6 + n ≤ x.val) :
    (commutator_g₁_g₃ n k 0)⁻¹ x = x := by
  rw [Perm.inv_eq_iff_eq]
  unfold commutator_g₁_g₃
  simp only [Perm.mul_apply]
  have hx_ge6 : x.val ≥ 6 := by omega
  have hg₃ := ThreeCycleExtract.g₃_fixes_val_ge_6 n k x hx_ge6
  rw [hg₃]
  have hg₁ := g₁_fixes_tailB n k x hx
  rw [hg₁]
  have hg₃_inv : (g₃ n k 0)⁻¹ x = x := by
    conv_lhs => rw [← hg₃]; rw [Perm.inv_apply_self]
  rw [hg₃_inv]
  have hg₁_inv' : (g₁ n k 0)⁻¹ x = x := g₁_inv_fixes_tailB n k x hx
  exact hg₁_inv'.symm

/-- c₁₂ * c₁₃⁻¹ fixes tailB elements -/
theorem product_fixes_tailB (n k : ℕ) (x : Omega n k 0) (hx : 6 + n ≤ x.val) :
    c₁₂_times_c₁₃_inv n k 0 x = x := by
  unfold c₁₂_times_c₁₃_inv c₁₂ c₁₃
  simp only [Perm.mul_apply]
  rw [c₁₃_inv_fixes_tailB n k x hx]
  exact c₁₂_fixes_tailB n k x hx

/-- The squared product fixes tailB elements -/
theorem sq_fixes_tailB (n k : ℕ) (x : Omega n k 0) (hx : 6 + n ≤ x.val) :
    (c₁₂_times_c₁₃_inv n k 0 ^ 2) x = x := by
  simp only [sq, Perm.mul_apply]
  rw [product_fixes_tailB n k x hx, product_fixes_tailB n k x hx]

-- ============================================
-- SECTION 6: TailA fixing (structural)
-- ============================================

/-- The squared product fixes tailA elements -/
theorem sq_fixes_tailA (n k : ℕ) (hn : n ≥ 1) (x : Omega n k 0)
    (hA : 6 ≤ x.val ∧ x.val < 6 + n) :
    (c₁₂_times_c₁₃_inv n k 0 ^ 2) x = x := by
  by_cases hx_last : x.val = 5 + n
  · -- Last tailA element: forms 2-cycle with 4, squaring fixes it
    have hx_eq : x = ⟨5 + n, by omega⟩ := Fin.ext hx_last
    rw [hx_eq]; exact TailALast.sq_fixes_last_tailA n k hn
  · -- Not last: both c₁₂ and c₁₃⁻¹ fix x directly
    have hA' : 6 ≤ x.val ∧ x.val < 5 + n := ⟨hA.1, by omega⟩
    simp only [sq, Perm.mul_apply, c₁₂_times_c₁₃_inv, c₁₂, c₁₃]
    rw [TailAFixing.c₁₃_inv_fixes_tailA n k x hA]
    rw [TailAFixing.c₁₂_fixes_tailA_not_last n k x hA']
    rw [TailAFixing.c₁₃_inv_fixes_tailA n k x hA]
    exact TailAFixing.c₁₂_fixes_tailA_not_last n k x hA'

end LemmaFeld.GroupTheory.AF.TailLemmas
