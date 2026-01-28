/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.ThreeCycle.Case1CommutatorLemmas
import LemmaFeld.GroupTheory.AF.ThreeCycle.Case2CommutatorLemmas
import LemmaFeld.GroupTheory.AF.ThreeCycle.Case2FixedPointLemmas
import LemmaFeld.GroupTheory.AF.Transitivity.Lemma05ListProps

/-!
# Fixed-Point Proofs for Case 1: m ≥ 1, k = 0

This file provides explicit proofs for fixed-point lemmas of (c₁₃ * c₂₃⁻¹)².
These replace the axioms in Case1FixedPointLemmas.lean.

## Key Results

- sq_fixes_0: (0,1) form a 2-cycle in prod, fixed on squaring
- sq_fixes_1: same reason
- sq_fixes_2: (2, last_tailC) form a 2-cycle when m ≥ 1
- sq_fixes_tailA: tailA elements are fixed by prod
- sq_fixes_tailC: tailC elements form 2-cycles or are fixed
-/

open Equiv Perm

namespace LemmaFeld.GroupTheory.AF.Case1FixedPointProofs

-- ============================================
-- SECTION 1: g₃(1) = first tailC when m ≥ 1
-- ============================================

/-- Helper: tailCList[0] = ⟨6+n, _⟩ when m ≥ 1 and k = 0 -/
theorem tailCList_head (n m : ℕ) (hm : m ≥ 1) :
    (tailCList n 0 m)[0]'(by simp [tailCList, List.finRange]; omega) = ⟨6 + n, by omega⟩ := by
  simp only [tailCList, List.finRange]
  cases m with
  | zero => omega
  | succ m' =>
    simp only [List.ofFn_succ, List.map_cons, List.getElem_cons_zero]
    rfl

/-- When m ≥ 1 and k = 0, g₃(1) = ⟨6+n, _⟩ (first tailC element).
    Position 3 in [2,4,5,1,6+n,...] maps to position 4. -/
theorem g₃_1_eq_firstTailC (n m : ℕ) (hm : m ≥ 1) :
    g₃ n 0 m ⟨1, by omega⟩ = ⟨6 + n, by omega⟩ := by
  unfold g₃
  have hnd := g₃_list_nodup n 0 m
  have hlen := g₃_cycle_length n 0 m
  have h_pos : 3 + 1 < (g₃CoreList n 0 m ++ tailCList n 0 m).length := by rw [hlen]; omega
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 3 h_pos
  -- The input is index 3 which is ⟨1, _⟩
  have h_in : (g₃CoreList n 0 m ++ tailCList n 0 m)[3]'(by rw [hlen]; omega) = ⟨1, by omega⟩ := by
    simp [g₃CoreList]
  -- The output is index 4 which is in tailCList
  have h_out : (g₃CoreList n 0 m ++ tailCList n 0 m)[4]'h_pos = ⟨6 + n, by omega⟩ := by
    have h_core_len : (g₃CoreList n 0 m).length = 4 := by simp [g₃CoreList]
    rw [List.getElem_append_right (by omega : 4 ≥ (g₃CoreList n 0 m).length)]
    simp only [h_core_len]
    exact tailCList_head n m hm
  simp only [h_in] at h_fp
  simp only [h_out] at h_fp
  exact h_fp

/-- g₃⁻¹(6+n) = 1 when m ≥ 1 and k = 0 -/
theorem g₃_inv_firstTailC_eq_1 (n m : ℕ) (hm : m ≥ 1) :
    (g₃ n 0 m)⁻¹ ⟨6 + n, by omega⟩ = ⟨1, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]
  exact (g₃_1_eq_firstTailC n m hm).symm

-- ============================================
-- SECTION 2: c₂₃ actions when m ≥ 1
-- ============================================

/-- c₂₃(1) = 0 when m ≥ 1 and k = 0.
    Trace: g₃(1)=6+n, g₂(6+n)=6+n, g₃⁻¹(6+n)=1, g₂⁻¹(1)=0 -/
theorem c₂₃_1_eq_0 (n m : ℕ) (hm : m ≥ 1) :
    commutator_g₂_g₃ n 0 m ⟨1, by omega⟩ = ⟨0, by omega⟩ := by
  unfold commutator_g₂_g₃
  simp only [Perm.mul_apply]
  -- g₃(1) = 6+n
  rw [g₃_1_eq_firstTailC n m hm]
  -- g₂(6+n) = 6+n (g₂ fixes elements ≥ 6 when k=0)
  have hg₂_fix : g₂ n 0 m ⟨6 + n, by omega⟩ = ⟨6 + n, by omega⟩ :=
    SymmetricCase1.g₂_fixes_val_ge_6 n m ⟨6 + n, by omega⟩ (by simp only [Fin.val_mk]; omega)
  rw [hg₂_fix]
  -- g₃⁻¹(6+n) = 1
  rw [g₃_inv_firstTailC_eq_1 n m hm]
  -- g₂⁻¹(1) = 0
  exact Case1ProductLemmas.g₂_k0_inv_1_eq_0 n m

/-- c₂₃(5) = 1 when k = 0. Trace: g₃(5)=1, g₂(1)=3, g₃⁻¹(3)=3, g₂⁻¹(3)=1 -/
theorem c₂₃_5_eq_1 (n m : ℕ) :
    commutator_g₂_g₃ n 0 m ⟨5, by omega⟩ = ⟨1, by omega⟩ := by
  unfold commutator_g₂_g₃
  simp only [Perm.mul_apply]
  rw [Case1ProductLemmas.g₃_5_eq_1, Case1ProductLemmas.g₂_k0_1_eq_3,
      Case1ProductLemmas.g₃_inv_fixes_3, Case1ProductLemmas.g₂_k0_inv_3_eq_1]

/-- c₂₃⁻¹(0) = 1 when m ≥ 1 (since c₂₃(1) = 0) -/
theorem c₂₃_inv_0_eq_1 (n m : ℕ) (hm : m ≥ 1) :
    (commutator_g₂_g₃ n 0 m)⁻¹ ⟨0, by omega⟩ = ⟨1, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]
  exact (c₂₃_1_eq_0 n m hm).symm

/-- c₂₃⁻¹(1) = 5 (since c₂₃(5) = 1) -/
theorem c₂₃_inv_1_eq_5 (n m : ℕ) :
    (commutator_g₂_g₃ n 0 m)⁻¹ ⟨1, by omega⟩ = ⟨5, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]
  exact (c₂₃_5_eq_1 n m).symm

-- ============================================
-- SECTION 3: c₁₃ actions when m ≥ 1
-- ============================================

/-- c₁₃(1) = 1 when m ≥ 1 and k = 0.
    Trace: g₃(1)=6+n, g₁(6+n)=6+n, g₃⁻¹(6+n)=1, g₁⁻¹(1)=1 -/
theorem c₁₃_fixes_1 (n m : ℕ) (hm : m ≥ 1) :
    commutator_g₁_g₃ n 0 m ⟨1, by omega⟩ = ⟨1, by omega⟩ := by
  unfold commutator_g₁_g₃
  simp only [Perm.mul_apply]
  -- g₃(1) = 6+n
  rw [g₃_1_eq_firstTailC n m hm]
  -- g₁(6+n) = 6+n (g₁ fixes tailC elements, 6+n is first tailC when k=0)
  have hg₁_fix : g₁ n 0 m ⟨6 + n, by omega⟩ = ⟨6 + n, by omega⟩ := by
    unfold g₁
    apply List.formPerm_apply_of_notMem
    simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map, List.mem_finRange, not_or]
    constructor
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
    · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega
  rw [hg₁_fix]
  -- g₃⁻¹(6+n) = 1
  rw [g₃_inv_firstTailC_eq_1 n m hm]
  -- g₁⁻¹(1) = 1
  exact Case1CommutatorLemmas.g₁_inv_fixes_1 n m

/-- c₁₃(5) = 0. Trace: g₃(5)=1, g₁(1)=1, g₃⁻¹(1)=5, g₁⁻¹(5)=0 -/
theorem c₁₃_5_eq_0 (n m : ℕ) :
    commutator_g₁_g₃ n 0 m ⟨5, by omega⟩ = ⟨0, by omega⟩ := by
  unfold commutator_g₁_g₃
  simp only [Perm.mul_apply]
  rw [Case1ProductLemmas.g₃_5_eq_1, Case1CommutatorLemmas.g₁_fixes_1,
      Case1ProductLemmas.g₃_inv_1_eq_5, Case1CommutatorLemmas.g₁_inv_5_eq_0]

-- ============================================
-- SECTION 4: Product lemmas
-- ============================================

/-- prod(0) = 1 when m ≥ 1 -/
theorem product_0_eq_1 (n m : ℕ) (hm : m ≥ 1) :
    SymmetricCase1.c₁₃_times_c₂₃_inv n m ⟨0, by omega⟩ = ⟨1, by omega⟩ := by
  unfold SymmetricCase1.c₁₃_times_c₂₃_inv
  simp only [Perm.mul_apply]
  rw [c₂₃_inv_0_eq_1 n m hm, c₁₃_fixes_1 n m hm]

/-- prod(1) = 0 -/
theorem product_1_eq_0 (n m : ℕ) :
    SymmetricCase1.c₁₃_times_c₂₃_inv n m ⟨1, by omega⟩ = ⟨0, by omega⟩ := by
  unfold SymmetricCase1.c₁₃_times_c₂₃_inv
  simp only [Perm.mul_apply]
  rw [c₂₃_inv_1_eq_5, c₁₃_5_eq_0]

-- ============================================
-- SECTION 5: Main fixed-point theorems
-- ============================================

/-- (c₁₃ * c₂₃⁻¹)²(0) = 0: (0,1) form a 2-cycle -/
theorem sq_fixes_0 (n m : ℕ) (hm : m ≥ 1) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) ⟨0, by omega⟩ = ⟨0, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [product_0_eq_1 n m hm, product_1_eq_0]

/-- (c₁₃ * c₂₃⁻¹)²(1) = 1: (0,1) form a 2-cycle -/
theorem sq_fixes_1 (n m : ℕ) (hm : m ≥ 1) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) ⟨1, by omega⟩ = ⟨1, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [product_1_eq_0, product_0_eq_1 n m hm]

-- ============================================
-- SECTION 6: sq_fixes_2 (element 2 pairs with last tailC)
-- ============================================

/-- c₂₃(3) = 2. Trace: g₃(3)=3, g₂(3)=4, g₃⁻¹(4)=2, g₂⁻¹(2)=2 -/
theorem c₂₃_3_eq_2 (n m : ℕ) :
    commutator_g₂_g₃ n 0 m ⟨3, by omega⟩ = ⟨2, by omega⟩ := by
  unfold commutator_g₂_g₃
  simp only [Perm.mul_apply]
  rw [Case1ProductLemmas.g₃_fixes_3, Case1ProductLemmas.g₂_k0_3_eq_4,
      Case1ProductLemmas.g₃_inv_4_eq_2, Case1ProductLemmas.g₂_k0_inv_fixes_2]

/-- c₂₃⁻¹(2) = 3 -/
theorem c₂₃_inv_2_eq_3 (n m : ℕ) :
    (commutator_g₂_g₃ n 0 m)⁻¹ ⟨2, by omega⟩ = ⟨3, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]
  exact (c₂₃_3_eq_2 n m).symm

/-- g₃⁻¹(2) = last tailC when m ≥ 1. The wrap point of the g₃ cycle.
    Verified computationally for all small (n,m) pairs. -/
theorem g₃_inv_2_eq_lastTailC (n m : ℕ) (hm : m ≥ 1) :
    (g₃ n 0 m)⁻¹ ⟨2, by omega⟩ = ⟨5 + n + m, by omega⟩ := by
  -- g₃ cycle: 2 → 4 → 5 → 1 → (6+n) → ... → (5+n+m) → 2
  -- So g₃⁻¹(2) = last element = 5+n+m
  rw [Perm.inv_eq_iff_eq]
  unfold g₃
  have hnd := g₃_list_nodup n 0 m
  have hlen := g₃_cycle_length n 0 m
  have h_last_idx : (4 + m - 1) < (g₃CoreList n 0 m ++ tailCList n 0 m).length := by
    rw [hlen]; omega
  have h_fp := List.formPerm_apply_getElem _ hnd (4 + m - 1) h_last_idx
  have h_wrap : (4 + m - 1 + 1) % (g₃CoreList n 0 m ++ tailCList n 0 m).length = 0 := by
    rw [hlen]
    have h : 4 + m - 1 + 1 = 4 + m := by omega
    rw [h]
    exact Nat.mod_self (4 + m)
  simp only [h_wrap] at h_fp
  have h_idx0 : (g₃CoreList n 0 m ++ tailCList n 0 m)[0] = ⟨2, by omega⟩ := by
    simp [g₃CoreList]
  simp only [h_idx0] at h_fp
  -- The last element is ⟨5+n+m, _⟩
  have h_last : (g₃CoreList n 0 m ++ tailCList n 0 m)[4 + m - 1]'h_last_idx =
      ⟨5 + n + m, by omega⟩ := by
    have idx_eq : 4 + m - 1 = 4 + (m - 1) := by omega
    have hm_pos : m - 1 < m := Nat.sub_lt hm Nat.one_pos
    have h := LemmaFeld.GroupTheory.AF.Transitivity.g₃_list_getElem_tail n 0 m ⟨m - 1, hm_pos⟩
    simp only [Fin.val_mk] at h
    convert h using 2 <;> omega
  simp only [h_last] at h_fp
  exact h_fp.symm

/-- c₁₃(3) = last_tailC when m ≥ 1. -/
theorem c₁₃_3_eq_lastTailC (n m : ℕ) (hm : m ≥ 1) :
    commutator_g₁_g₃ n 0 m ⟨3, by omega⟩ = ⟨5 + n + m, by omega⟩ := by
  unfold commutator_g₁_g₃
  simp only [Perm.mul_apply]
  rw [Case1ProductLemmas.g₃_fixes_3, Case1CommutatorLemmas.g₁_3_eq_2,
      g₃_inv_2_eq_lastTailC n m hm]
  -- g₁⁻¹(last_tailC) = last_tailC (g₁ fixes tailC)
  have hg₁_inv_fix : (g₁ n 0 m)⁻¹ ⟨5 + n + m, by omega⟩ = ⟨5 + n + m, by omega⟩ := by
    have hg₁_fix : g₁ n 0 m ⟨5 + n + m, by omega⟩ = ⟨5 + n + m, by omega⟩ := by
      unfold g₁; apply List.formPerm_apply_of_notMem
      simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, List.mem_map, List.mem_finRange, not_or]
      constructor
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
      · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega
    calc (g₁ n 0 m)⁻¹ ⟨5 + n + m, by omega⟩
        = (g₁ n 0 m)⁻¹ ((g₁ n 0 m) ⟨5 + n + m, by omega⟩) := by rw [hg₁_fix]
      _ = ⟨5 + n + m, by omega⟩ := Equiv.symm_apply_apply _ _
  exact hg₁_inv_fix

/-- prod(2) = last_tailC when m ≥ 1 -/
theorem product_2_eq_lastTailC (n m : ℕ) (hm : m ≥ 1) :
    SymmetricCase1.c₁₃_times_c₂₃_inv n m ⟨2, by omega⟩ = ⟨5 + n + m, by omega⟩ := by
  unfold SymmetricCase1.c₁₃_times_c₂₃_inv
  simp only [Perm.mul_apply]
  rw [c₂₃_inv_2_eq_3, c₁₃_3_eq_lastTailC n m hm]

/-- c₂₃ fixes last_tailC. -/
theorem c₂₃_fixes_lastTailC (n m : ℕ) (hm : m ≥ 1) :
    commutator_g₂_g₃ n 0 m ⟨5 + n + m, by omega⟩ = ⟨5 + n + m, by omega⟩ := by
  unfold commutator_g₂_g₃
  simp only [Perm.mul_apply]
  -- g₃(last_tailC) = 2
  have hg₃ : g₃ n 0 m ⟨5 + n + m, by omega⟩ = ⟨2, by omega⟩ := by
    have h := g₃_inv_2_eq_lastTailC n m hm
    rw [Perm.inv_eq_iff_eq] at h
    exact h.symm
  rw [hg₃, Case1ProductLemmas.g₂_k0_fixes_2, g₃_inv_2_eq_lastTailC n m hm]
  -- g₂⁻¹(last_tailC) = last_tailC
  have hg₂_fix : g₂ n 0 m ⟨5 + n + m, by omega⟩ = ⟨5 + n + m, by omega⟩ :=
    SymmetricCase1.g₂_fixes_val_ge_6 n m _ (by simp only [Fin.val_mk]; omega)
  calc (g₂ n 0 m)⁻¹ ⟨5 + n + m, by omega⟩
      = (g₂ n 0 m)⁻¹ ((g₂ n 0 m) ⟨5 + n + m, by omega⟩) := by rw [hg₂_fix]
    _ = ⟨5 + n + m, by omega⟩ := Equiv.symm_apply_apply _ _

/-- c₁₃(last_tailC) = 2 when m ≥ 1. -/
theorem c₁₃_lastTailC_eq_2 (n m : ℕ) (hm : m ≥ 1) :
    commutator_g₁_g₃ n 0 m ⟨5 + n + m, by omega⟩ = ⟨2, by omega⟩ := by
  unfold commutator_g₁_g₃
  simp only [Perm.mul_apply]
  -- g₃(5+n+m) = 2 (wrap in g₃ cycle)
  have hg₃ : g₃ n 0 m ⟨5 + n + m, by omega⟩ = ⟨2, by omega⟩ := by
    have h := g₃_inv_2_eq_lastTailC n m hm
    rw [Perm.inv_eq_iff_eq] at h
    exact h.symm
  rw [hg₃]
  -- Now we need g₁⁻¹(g₃⁻¹(g₁(2)))
  by_cases hn : n = 0
  · -- Case n = 0: g₁(2) = 0, g₃⁻¹(0) = 0, g₁⁻¹(0) = 2
    subst hn
    rw [Case2CommutatorLemmas.g₁_2_eq_0_n0 0 m,
        Case1ProductLemmas.g₃_inv_fixes_0 0 m,
        Case2CommutatorLemmas.g₁_inv_0_eq_2_n0 0 m]
  · -- Case n ≥ 1: g₁(2) = 6, g₃⁻¹(6) = 6, g₁⁻¹(6) = 2
    have hn_pos : n ≥ 1 := Nat.one_le_iff_ne_zero.mpr hn
    rw [Case2FixedPointLemmas.g₁_2_eq_6_n_ge1 n 0 m hn_pos]
    -- g₃⁻¹(6) = 6 (6 is in tailA when n ≥ 1, not in g₃ cycle)
    have hg₃_inv_6 : (g₃ n 0 m)⁻¹ ⟨6, by omega⟩ = ⟨6, by omega⟩ := by
      have hg₃_fix : g₃ n 0 m ⟨6, by omega⟩ = ⟨6, by omega⟩ := by
        unfold g₃; apply List.formPerm_apply_of_notMem
        simp only [g₃CoreList, tailCList, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false, List.mem_map, List.mem_finRange, not_or]
        constructor
        · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
        · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega
      calc (g₃ n 0 m)⁻¹ ⟨6, by omega⟩
          = (g₃ n 0 m)⁻¹ ((g₃ n 0 m) ⟨6, by omega⟩) := by rw [hg₃_fix]
        _ = ⟨6, by omega⟩ := Equiv.symm_apply_apply _ _
    rw [hg₃_inv_6, Case2FixedPointLemmas.g₁_inv_6_eq_2_n_ge1 n 0 m hn_pos]

/-- prod(last_tailC) = 2 when m ≥ 1 -/
theorem product_lastTailC_eq_2 (n m : ℕ) (hm : m ≥ 1) :
    SymmetricCase1.c₁₃_times_c₂₃_inv n m ⟨5 + n + m, by omega⟩ = ⟨2, by omega⟩ := by
  unfold SymmetricCase1.c₁₃_times_c₂₃_inv
  simp only [Perm.mul_apply]
  -- c₂₃⁻¹(last_tailC) = last_tailC
  have hc₂₃_inv : (commutator_g₂_g₃ n 0 m)⁻¹ ⟨5 + n + m, by omega⟩ = ⟨5 + n + m, by omega⟩ := by
    have h := c₂₃_fixes_lastTailC n m hm
    calc (commutator_g₂_g₃ n 0 m)⁻¹ ⟨5 + n + m, by omega⟩
        = (commutator_g₂_g₃ n 0 m)⁻¹ ((commutator_g₂_g₃ n 0 m) ⟨5 + n + m, by omega⟩) := by rw [h]
      _ = ⟨5 + n + m, by omega⟩ := Equiv.symm_apply_apply _ _
  rw [hc₂₃_inv, c₁₃_lastTailC_eq_2 n m hm]

/-- (c₁₃ * c₂₃⁻¹)²(2) = 2: (2, last_tailC) form a 2-cycle -/
theorem sq_fixes_2 (n m : ℕ) (hm : m ≥ 1) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) ⟨2, by omega⟩ = ⟨2, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [product_2_eq_lastTailC n m hm, product_lastTailC_eq_2 n m hm]

-- ============================================
-- SECTION 7: TailA fixed-point lemmas
-- ============================================

/-- c₂₃ fixes tailA elements. g₂ and g₃ both fix tailA when k = 0. -/
theorem c₂₃_fixes_tailA (n m : ℕ) (x : Omega n 0 m) (hx : 6 ≤ x.val ∧ x.val < 6 + n) :
    commutator_g₂_g₃ n 0 m x = x := by
  unfold commutator_g₂_g₃
  simp only [Perm.mul_apply]
  -- g₃ fixes tailA elements
  have hg₃_fix : g₃ n 0 m x = x := by
    unfold g₃; apply List.formPerm_apply_of_notMem
    simp only [g₃CoreList, tailCList, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map, List.mem_finRange, not_or]
    constructor
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
    · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega
  rw [hg₃_fix]
  -- g₂ fixes tailA elements when k = 0
  have hg₂_fix : g₂ n 0 m x = x := SymmetricCase1.g₂_fixes_val_ge_6 n m x (by omega)
  rw [hg₂_fix]
  -- g₃⁻¹(x) = x and g₂⁻¹(x) = x
  have hg₃_inv : (g₃ n 0 m)⁻¹ x = x := by
    calc (g₃ n 0 m)⁻¹ x = (g₃ n 0 m)⁻¹ ((g₃ n 0 m) x) := by rw [hg₃_fix]
      _ = x := Equiv.symm_apply_apply _ _
  have hg₂_inv : (g₂ n 0 m)⁻¹ x = x := by
    calc (g₂ n 0 m)⁻¹ x = (g₂ n 0 m)⁻¹ ((g₂ n 0 m) x) := by rw [hg₂_fix]
      _ = x := Equiv.symm_apply_apply _ _
  rw [hg₃_inv, hg₂_inv]

/-- c₁₃ fixes tailA elements. -/
theorem c₁₃_fixes_tailA (n m : ℕ) (x : Omega n 0 m) (hx : 6 ≤ x.val ∧ x.val < 6 + n) :
    commutator_g₁_g₃ n 0 m x = x := by
  unfold commutator_g₁_g₃
  simp only [Perm.mul_apply]
  have hn : n ≥ 1 := by omega
  -- g₃ fixes tailA (tailA not in g₃'s cycle when k=0)
  have hg₃_fix : g₃ n 0 m x = x := by
    unfold g₃; apply List.formPerm_apply_of_notMem
    simp only [g₃CoreList, tailCList, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map, List.mem_finRange, not_or]
    constructor
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
    · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega
  rw [hg₃_fix]
  by_cases hlast : x.val = 5 + n
  · -- x is last tailA element: g₁(5+n)=0, g₃⁻¹(0)=0, g₁⁻¹(0)=5+n
    have hx_eq : x = ⟨5 + n, by omega⟩ := Fin.ext hlast
    rw [hx_eq, Case2CommutatorLemmas.g₁_5plusn_eq_0 n 0 m hn,
        Case1ProductLemmas.g₃_inv_fixes_0 n m,
        Case2CommutatorLemmas.g₁_inv_0_eq_5plusn n 0 m hn]
  · -- x is not last: g₁(x) = x+1 (in tailA), g₃⁻¹(x+1) = x+1, g₁⁻¹(x+1) = x
    have hx_not_last : x.val < 5 + n := by omega
    -- g₁(x) = x+1 for x in tailA (not last)
    have hg₁_next : g₁ n 0 m x = ⟨x.val + 1, by omega⟩ := by
      unfold g₁
      have hnd := g₁_list_nodup n 0 m
      have hlen := g₁_cycle_length n 0 m
      have hi_bound : x.val - 6 < n := by omega
      have hpos : 4 + (x.val - 6) < (g₁CoreList n 0 m ++ tailAList n 0 m).length := by
        rw [hlen]; omega
      have hpos1 : 4 + (x.val - 6) + 1 < (g₁CoreList n 0 m ++ tailAList n 0 m).length := by
        rw [hlen]; omega
      have h_at : (g₁CoreList n 0 m ++ tailAList n 0 m)[4 + (x.val - 6)]'hpos = x := by
        have := LemmaFeld.GroupTheory.AF.Transitivity.g₁_list_getElem_tail n 0 m ⟨x.val - 6, hi_bound⟩
        simp only [Fin.val_mk] at this
        rw [Fin.ext_iff]; simp only [this]; omega
      have h_fp : List.formPerm (g₁CoreList n 0 m ++ tailAList n 0 m) x =
          (g₁CoreList n 0 m ++ tailAList n 0 m)[4 + (x.val - 6) + 1]'hpos1 := by
        conv_lhs => rw [← h_at]
        exact List.formPerm_apply_lt_getElem _ hnd (4 + (x.val - 6)) hpos1
      have h_next : (g₁CoreList n 0 m ++ tailAList n 0 m)[4 + (x.val - 6) + 1]'hpos1 =
          ⟨x.val + 1, by omega⟩ := by
        have hip1 : x.val - 6 + 1 < n := by omega
        have := LemmaFeld.GroupTheory.AF.Transitivity.g₁_list_getElem_tail n 0 m ⟨x.val - 6 + 1, hip1⟩
        simp only [Fin.val_mk] at this
        have heq : 4 + (x.val - 6) + 1 = 4 + (x.val - 6 + 1) := by ring
        rw [Fin.ext_iff]; simp only [heq] at this ⊢; simp only [this]; omega
      rw [h_fp, h_next]
    rw [hg₁_next]
    -- g₃⁻¹(x+1) = x+1 (x+1 is still in tailA)
    have hg₃_inv_next : (g₃ n 0 m)⁻¹ ⟨x.val + 1, by omega⟩ = ⟨x.val + 1, by omega⟩ := by
      have hg₃_fix' : g₃ n 0 m ⟨x.val + 1, by omega⟩ = ⟨x.val + 1, by omega⟩ := by
        unfold g₃; apply List.formPerm_apply_of_notMem
        simp only [g₃CoreList, tailCList, List.mem_append, List.mem_cons, List.not_mem_nil,
          or_false, List.mem_map, List.mem_finRange, not_or]
        constructor
        · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
        · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega
      calc (g₃ n 0 m)⁻¹ ⟨x.val + 1, by omega⟩
          = (g₃ n 0 m)⁻¹ ((g₃ n 0 m) ⟨x.val + 1, by omega⟩) := by rw [hg₃_fix']
        _ = ⟨x.val + 1, by omega⟩ := Equiv.symm_apply_apply _ _
    rw [hg₃_inv_next]
    -- g₁⁻¹(x+1) = x
    have hg₁_inv_next : (g₁ n 0 m)⁻¹ ⟨x.val + 1, by omega⟩ = x := by
      rw [Perm.inv_eq_iff_eq]; exact hg₁_next.symm
    rw [hg₁_inv_next]

/-- prod fixes tailA elements -/
theorem product_fixes_tailA (n m : ℕ) (x : Omega n 0 m) (hx : 6 ≤ x.val ∧ x.val < 6 + n) :
    SymmetricCase1.c₁₃_times_c₂₃_inv n m x = x := by
  unfold SymmetricCase1.c₁₃_times_c₂₃_inv
  simp only [Perm.mul_apply]
  have hc₂₃_inv : (commutator_g₂_g₃ n 0 m)⁻¹ x = x := by
    have h := c₂₃_fixes_tailA n m x hx
    calc (commutator_g₂_g₃ n 0 m)⁻¹ x
        = (commutator_g₂_g₃ n 0 m)⁻¹ ((commutator_g₂_g₃ n 0 m) x) := by rw [h]
      _ = x := Equiv.symm_apply_apply _ _
  rw [hc₂₃_inv, c₁₃_fixes_tailA n m x hx]

/-- sq fixes tailA elements -/
theorem sq_fixes_tailA (n m : ℕ) (x : Omega n 0 m) (hx : 6 ≤ x.val ∧ x.val < 6 + n) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) x = x := by
  simp only [sq, Perm.mul_apply]
  rw [product_fixes_tailA n m x hx, product_fixes_tailA n m x hx]

-- ============================================
-- SECTION 8: TailC fixed-point lemmas
-- ============================================

/-- sq fixes elements ≥ 6 (tailA ∪ tailC, since k = 0 means tailB is empty) -/
theorem sq_fixes_ge6 (n m : ℕ) (hm : m ≥ 1) (x : Omega n 0 m) (hx : x.val ≥ 6) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) x = x := by
  by_cases hA : x.val < 6 + n
  · exact sq_fixes_tailA n m x ⟨hx, hA⟩
  · -- tailC case
    push_neg at hA
    by_cases hlast : x.val = 5 + n + m
    · -- x is last tailC, forms 2-cycle with 2
      have hx_eq : x = ⟨5 + n + m, by omega⟩ := Fin.ext hlast
      simp only [sq, Perm.mul_apply]
      rw [hx_eq, product_lastTailC_eq_2 n m hm, product_2_eq_lastTailC n m hm]
    · -- x is in tailC but not last - these are fixed directly
      -- For middle tailC: c₂₃(x) = x and c₁₃(x) = x, so prod(x) = x
      have hx_mid : 6 + n ≤ x.val ∧ x.val < 5 + n + m := ⟨hA, by omega⟩
      -- c₂₃ fixes middle tailC: g₃(x)=x+1, g₂(x+1)=x+1, g₃⁻¹(x+1)=x, g₂⁻¹(x)=x
      have hc₂₃_fix : commutator_g₂_g₃ n 0 m x = x := by
        unfold commutator_g₂_g₃; simp only [Perm.mul_apply]
        -- g₃(x) = x+1 (middle tailC, not wrap)
        have hg₃_next : g₃ n 0 m x = ⟨x.val + 1, by omega⟩ := by
          unfold g₃
          have hnd := g₃_list_nodup n 0 m
          have hlen := g₃_cycle_length n 0 m
          have hi_bound : x.val - (6 + n) < m := by omega
          have hpos : 4 + (x.val - (6 + n)) < (g₃CoreList n 0 m ++ tailCList n 0 m).length := by
            rw [hlen]; omega
          have hpos1 : 4 + (x.val - (6 + n)) + 1 < (g₃CoreList n 0 m ++ tailCList n 0 m).length := by
            rw [hlen]; omega
          have h_at : (g₃CoreList n 0 m ++ tailCList n 0 m)[4 + (x.val - (6 + n))]'hpos = x := by
            have := LemmaFeld.GroupTheory.AF.Transitivity.g₃_list_getElem_tail n 0 m ⟨x.val - (6 + n), hi_bound⟩
            simp only [Fin.val_mk] at this
            rw [Fin.ext_iff]; simp only [this]; omega
          have h_fp : List.formPerm (g₃CoreList n 0 m ++ tailCList n 0 m) x =
              (g₃CoreList n 0 m ++ tailCList n 0 m)[4 + (x.val - (6 + n)) + 1]'hpos1 := by
            conv_lhs => rw [← h_at]
            exact List.formPerm_apply_lt_getElem _ hnd (4 + (x.val - (6 + n))) hpos1
          have hip1 : x.val - (6 + n) + 1 < m := by omega
          have h_next : (g₃CoreList n 0 m ++ tailCList n 0 m)[4 + (x.val - (6 + n)) + 1]'hpos1 =
              ⟨x.val + 1, by omega⟩ := by
            have := LemmaFeld.GroupTheory.AF.Transitivity.g₃_list_getElem_tail n 0 m ⟨x.val - (6 + n) + 1, hip1⟩
            simp only [Fin.val_mk] at this
            have heq : 4 + (x.val - (6 + n)) + 1 = 4 + (x.val - (6 + n) + 1) := by ring
            rw [Fin.ext_iff]; simp only [heq] at this ⊢; simp only [this]; omega
          rw [h_fp, h_next]
        rw [hg₃_next]
        -- g₂(x+1) = x+1 (g₂ fixes tailC)
        have hx_ge6_plus1 : x.val + 1 ≥ 6 := by omega
        have hg₂_fix : g₂ n 0 m ⟨x.val + 1, by omega⟩ = ⟨x.val + 1, by omega⟩ :=
          SymmetricCase1.g₂_fixes_val_ge_6 n m _ hx_ge6_plus1
        rw [hg₂_fix]
        -- g₃⁻¹(x+1) = x
        have hg₃_inv : (g₃ n 0 m)⁻¹ ⟨x.val + 1, by omega⟩ = x := by
          rw [Perm.inv_eq_iff_eq]; exact hg₃_next.symm
        rw [hg₃_inv]
        -- g₂⁻¹(x) = x
        have hg₂_inv_x : (g₂ n 0 m)⁻¹ x = x := by
          have hg₂_fix_x : g₂ n 0 m x = x := SymmetricCase1.g₂_fixes_val_ge_6 n m x (by omega)
          calc (g₂ n 0 m)⁻¹ x = (g₂ n 0 m)⁻¹ ((g₂ n 0 m) x) := by rw [hg₂_fix_x]
            _ = x := Equiv.symm_apply_apply _ _
        exact hg₂_inv_x
      -- c₁₃ fixes middle tailC: same structure
      have hc₁₃_fix : commutator_g₁_g₃ n 0 m x = x := by
        unfold commutator_g₁_g₃; simp only [Perm.mul_apply]
        have hg₃_next : g₃ n 0 m x = ⟨x.val + 1, by omega⟩ := by
          unfold g₃
          have hnd := g₃_list_nodup n 0 m
          have hlen := g₃_cycle_length n 0 m
          have hi_bound : x.val - (6 + n) < m := by omega
          have hpos : 4 + (x.val - (6 + n)) < (g₃CoreList n 0 m ++ tailCList n 0 m).length := by
            rw [hlen]; omega
          have hpos1 : 4 + (x.val - (6 + n)) + 1 < (g₃CoreList n 0 m ++ tailCList n 0 m).length := by
            rw [hlen]; omega
          have h_at : (g₃CoreList n 0 m ++ tailCList n 0 m)[4 + (x.val - (6 + n))]'hpos = x := by
            have := LemmaFeld.GroupTheory.AF.Transitivity.g₃_list_getElem_tail n 0 m ⟨x.val - (6 + n), hi_bound⟩
            simp only [Fin.val_mk] at this
            rw [Fin.ext_iff]; simp only [this]; omega
          have h_fp : List.formPerm (g₃CoreList n 0 m ++ tailCList n 0 m) x =
              (g₃CoreList n 0 m ++ tailCList n 0 m)[4 + (x.val - (6 + n)) + 1]'hpos1 := by
            conv_lhs => rw [← h_at]
            exact List.formPerm_apply_lt_getElem _ hnd (4 + (x.val - (6 + n))) hpos1
          have hip1 : x.val - (6 + n) + 1 < m := by omega
          have h_next : (g₃CoreList n 0 m ++ tailCList n 0 m)[4 + (x.val - (6 + n)) + 1]'hpos1 =
              ⟨x.val + 1, by omega⟩ := by
            have := LemmaFeld.GroupTheory.AF.Transitivity.g₃_list_getElem_tail n 0 m ⟨x.val - (6 + n) + 1, hip1⟩
            simp only [Fin.val_mk] at this
            have heq : 4 + (x.val - (6 + n)) + 1 = 4 + (x.val - (6 + n) + 1) := by ring
            rw [Fin.ext_iff]; simp only [heq] at this ⊢; simp only [this]; omega
          rw [h_fp, h_next]
        rw [hg₃_next]
        -- g₁(x+1) = x+1 (g₁ fixes tailC)
        have hg₁_fix : g₁ n 0 m ⟨x.val + 1, by omega⟩ = ⟨x.val + 1, by omega⟩ := by
          unfold g₁; apply List.formPerm_apply_of_notMem
          simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false, List.mem_map, List.mem_finRange, not_or]
          constructor
          · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
          · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega
        rw [hg₁_fix]
        -- g₃⁻¹(x+1) = x
        have hg₃_inv : (g₃ n 0 m)⁻¹ ⟨x.val + 1, by omega⟩ = x := by
          rw [Perm.inv_eq_iff_eq]; exact hg₃_next.symm
        rw [hg₃_inv]
        -- g₁⁻¹(x) = x
        have hg₁_fix_x : g₁ n 0 m x = x := by
          unfold g₁; apply List.formPerm_apply_of_notMem
          simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
            or_false, List.mem_map, List.mem_finRange, not_or]
          constructor
          · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
          · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega
        calc (g₁ n 0 m)⁻¹ x = (g₁ n 0 m)⁻¹ ((g₁ n 0 m) x) := by rw [hg₁_fix_x]
          _ = x := Equiv.symm_apply_apply _ _
      -- prod(x) = c₁₃(c₂₃⁻¹(x)) = c₁₃(x) = x
      have hc₂₃_inv_fix : (commutator_g₂_g₃ n 0 m)⁻¹ x = x := by
        calc (commutator_g₂_g₃ n 0 m)⁻¹ x
            = (commutator_g₂_g₃ n 0 m)⁻¹ ((commutator_g₂_g₃ n 0 m) x) := by rw [hc₂₃_fix]
          _ = x := Equiv.symm_apply_apply _ _
      have hprod_fix : SymmetricCase1.c₁₃_times_c₂₃_inv n m x = x := by
        unfold SymmetricCase1.c₁₃_times_c₂₃_inv
        simp only [Perm.mul_apply]
        rw [hc₂₃_inv_fix, hc₁₃_fix]
      simp only [sq, Perm.mul_apply]
      rw [hprod_fix, hprod_fix]

/-- sq fixes tailC elements when m ≥ 1 -/
theorem sq_fixes_tailC (n m : ℕ) (hm : m ≥ 1) (x : Omega n 0 m) (hx : 6 + n ≤ x.val) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) x = x :=
  sq_fixes_ge6 n m hm x (by omega)

end LemmaFeld.GroupTheory.AF.Case1FixedPointProofs
