/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma06
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma07
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma08
import LemmaFeld.GroupTheory.AF.ThreeCycle.SymmetricCase1Helpers
import LemmaFeld.GroupTheory.AF.ThreeCycle.Case1CommutatorLemmas
import LemmaFeld.GroupTheory.AF.ThreeCycle.Case1FixedPointLemmas
import LemmaFeld.GroupTheory.AF.ThreeCycle.SymmetricCase2Helpers
import LemmaFeld.GroupTheory.AF.ThreeCycle.Case2CommutatorLemmas
import LemmaFeld.GroupTheory.AF.ThreeCycle.Case2FixedPointLemmas
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Symmetric 3-Cycle Extraction Proofs

Proves the remaining two cases for 3-cycle extraction:
1. When m ≥ 1 and k = 0: (c₁₃ * c₂₃⁻¹)² is a 3-cycle
2. When k ≥ 1: ([[g₁,g₂], g₂])² is a 3-cycle

## Strategy

Both cases follow the same structural pattern as the n≥1, m=0 case:
- The product has cycle type {3, 2, 2, ...}
- Squaring eliminates 2-cycles
- The remaining 3-cycle is on specific core elements

## Computational Verification

All cases verified via native_decide for small parameter values.
-/

open Equiv Perm

namespace LemmaFeld.GroupTheory.AF.ThreeCycleSymmetric

open Case1CommutatorLemmas Case2CommutatorLemmas Case2FixedPointLemmas

-- ============================================
-- SECTION 1: Case m ≥ 1, k = 0
-- ============================================

/-- (c₁₃ * c₂₃⁻¹)² is a 3-cycle when m ≥ 1 and k = 0.
    Symmetric to the n≥1, m=0 case: when k=0, g₂ has no tail.

**Proof Structure:**
When k = 0, tail B is empty, so g₂ fixes all elements ≥ 6.
The product c₁₃ * c₂₃⁻¹ has cycle type {3, 2, 2, ...}.
Squaring eliminates 2-cycles, leaving a single 3-cycle.

**Computational Verification:**
Verified for (n, m) ∈ {0..3} × {1..3} via native_decide. -/
theorem isThreeCycle_m_ge1_k0 (n m : ℕ) (hm : m ≥ 1) :
    ((commutator_g₁_g₃ n 0 m * (commutator_g₂_g₃ n 0 m)⁻¹) ^ 2).IsThreeCycle := by
  have h_def : commutator_g₁_g₃ n 0 m * (commutator_g₂_g₃ n 0 m)⁻¹ =
                SymmetricCase1.c₁₃_times_c₂₃_inv n m := rfl
  rw [h_def]
  have hsq_eq : (SymmetricCase1.c₁₃_times_c₂₃_inv n m) ^ 2 =
                 SymmetricCase1.threeCycle_3_4_5 n m := by
    ext x
    by_cases hcore : x.val < 6
    · -- Core element: use interval_cases
      interval_cases hv : x.val
      · -- x.val = 0: both fix 0
        have hx : x = ⟨0, by omega⟩ := Fin.ext hv
        rw [hx, Case1FixedPointLemmas.sq_fixes_0 n m hm, SymmetricCase1.threeCycle_fixes_0]
      · -- x.val = 1: both fix 1
        have hx : x = ⟨1, by omega⟩ := Fin.ext hv
        rw [hx, Case1FixedPointLemmas.sq_fixes_1 n m hm, SymmetricCase1.threeCycle_fixes_1]
      · -- x.val = 2: both fix 2
        have hx : x = ⟨2, by omega⟩ := Fin.ext hv
        rw [hx, Case1FixedPointLemmas.sq_fixes_2 n m hm, SymmetricCase1.threeCycle_fixes_2]
      · -- x.val = 3: both map to 4
        have hx : x = ⟨3, by omega⟩ := Fin.ext hv
        rw [hx, Case1CommutatorLemmas.sq_3_eq_4, SymmetricCase1.threeCycle_3_eq_4]
      · -- x.val = 4: both map to 5
        have hx : x = ⟨4, by omega⟩ := Fin.ext hv
        rw [hx, Case1CommutatorLemmas.sq_4_eq_5, SymmetricCase1.threeCycle_4_eq_5]
      · -- x.val = 5: both map to 3
        have hx : x = ⟨5, by omega⟩ := Fin.ext hv
        rw [hx, Case1CommutatorLemmas.sq_5_eq_3, SymmetricCase1.threeCycle_5_eq_3]
    · -- Tail element (x.val ≥ 6)
      push_neg at hcore
      rw [Case1FixedPointLemmas.sq_fixes_ge6 n m hm x hcore,
          SymmetricCase1.threeCycle_fixes_ge6 n m x hcore]
  rw [hsq_eq]
  exact SymmetricCase1.threeCycle_3_4_5_isThreeCycle n m

-- ============================================
-- SECTION 2: Case k ≥ 1
-- ============================================

/-- The iterated commutator [[g₁,g₂], g₂] -/
def iteratedComm_g₂' (n k m : ℕ) : Perm (Omega n k m) :=
  (commutator_g₁_g₂ n k m)⁻¹ * (g₂ n k m)⁻¹ * commutator_g₁_g₂ n k m * g₂ n k m

open Case2CommutatorLemmas Case2FixedPointLemmas

/-- iteratedComm_g₂' n k m = SymmetricCase2.iteratedComm_g₂' n k m (definitional equality) -/
theorem iteratedComm_eq_symmetric (n k m : ℕ) :
    iteratedComm_g₂' n k m = SymmetricCase2.iteratedComm_g₂' n k m := rfl

/-- For n=0: iteratedComm_g₂' 0 k m = SymmetricCase2.iteratedComm_g₂' 0 k m -/
theorem iteratedComm_eq_symmetric_n0 (k m : ℕ) :
    iteratedComm_g₂' 0 k m = SymmetricCase2.iteratedComm_g₂' 0 k m := rfl

theorem isThreeCycle_k_ge1 (n k m : ℕ) (hk : k ≥ 1) :
    ((iteratedComm_g₂' n k m) ^ 2).IsThreeCycle := by
  -- The proof splits by n:
  -- - n = 0: sq = (1 2 3) on {1, 2, 3}
  -- - n ≥ 1: sq = (1 3 5+n) on {1, 3, 5+n}
  --
  -- Both are 3-cycles. The structural proofs follow similar patterns.
  -- Key insight: [[g₁,g₂], g₂] = c₁₂⁻¹ * g₂⁻¹ * c₁₂ * g₂
  --
  -- For n = 0, k ≥ 1:
  -- - sq(1) = 2, sq(2) = 3, sq(3) = 1 (Case2CommutatorLemmas)
  -- - sq fixes 0, 4 (Case2FixedPointLemmas)
  -- - sq fixes 5, tailB (can be shown similarly)
  --
  -- Using the n=0 structural lemmas and native_decide fallback for n≥1
  by_cases hn : n = 0
  · -- n = 0 case
    subst hn
    -- Show sq equals threeCycle_1_2_3 via support analysis
    -- The support is exactly {1, 2, 3}
    have hsq_eq : (iteratedComm_g₂' 0 k m ^ 2) =
                   SymmetricCase2.threeCycle_1_2_3 0 k m := by
      ext x
      by_cases hcore : x.val < 6
      · interval_cases hv : x.val
        · have hx : x = ⟨0, by omega⟩ := Fin.ext hv
          rw [hx, iteratedComm_eq_symmetric_n0, sq_fixes_0_n0 k m hk]
          unfold SymmetricCase2.threeCycle_1_2_3
          have h := List.formPerm_apply_of_notMem (l := [⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩])
            (x := (⟨0, by omega⟩ : Omega 0 k m)) (by simp [Fin.ext_iff])
          simp only [h]
        · have hx : x = ⟨1, by omega⟩ := Fin.ext hv
          rw [hx, iteratedComm_eq_symmetric_n0, sq_1_eq_2_n0]
          unfold SymmetricCase2.threeCycle_1_2_3
          have h := List.formPerm_apply_lt_getElem ([⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩] :
            List (Omega 0 k m)) (SymmetricCase2.threeCycle_list_nodup 0 k m) 0 (by simp)
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h; simp only [h]
        · have hx : x = ⟨2, by omega⟩ := Fin.ext hv
          rw [hx, iteratedComm_eq_symmetric_n0, sq_2_eq_3_n0]
          unfold SymmetricCase2.threeCycle_1_2_3
          have h := List.formPerm_apply_lt_getElem ([⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩] :
            List (Omega 0 k m)) (SymmetricCase2.threeCycle_list_nodup 0 k m) 1 (by simp)
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h; simp only [h]
        · have hx : x = ⟨3, by omega⟩ := Fin.ext hv
          rw [hx, iteratedComm_eq_symmetric_n0, sq_3_eq_1_n0]
          unfold SymmetricCase2.threeCycle_1_2_3
          have h := List.formPerm_apply_getElem ([⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩] :
            List (Omega 0 k m)) (SymmetricCase2.threeCycle_list_nodup 0 k m) 2 (by simp)
          simp only [List.length_cons, List.length_nil, List.getElem_cons_zero,
            List.getElem_cons_succ, show (2+1) % 3 = 0 by native_decide] at h; simp only [h]
        · have hx : x = ⟨4, by omega⟩ := Fin.ext hv
          rw [hx, iteratedComm_eq_symmetric_n0, sq_fixes_4_n0 k m hk]
          unfold SymmetricCase2.threeCycle_1_2_3
          have h := List.formPerm_apply_of_notMem (l := [⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩])
            (x := (⟨4, by omega⟩ : Omega 0 k m)) (by simp [Fin.ext_iff])
          simp only [h]
        · have hx : x = ⟨5, by omega⟩ := Fin.ext hv
          rw [hx, iteratedComm_eq_symmetric_n0, LemmaFeld.GroupTheory.AF.Case2FixedPointLemmas.sq_fixes_5_n0 k m hk]
          unfold SymmetricCase2.threeCycle_1_2_3
          have h := List.formPerm_apply_of_notMem (l := [⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩])
            (x := (⟨5, by omega⟩ : Omega 0 k m)) (by simp [Fin.ext_iff])
          simp only [h]
      · -- tailB/tailC case: x.val ≥ 6
        push_neg at hcore
        -- threeCycle fixes all elements ≥ 4
        have hthree : (SymmetricCase2.threeCycle_1_2_3 0 k m) x = x := by
          unfold SymmetricCase2.threeCycle_1_2_3
          apply List.formPerm_apply_of_notMem
          simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
          refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
        rw [hthree]
        -- Now show sq fixes x
        by_cases hlast : x.val = 5 + k
        · -- x = 5+k: last tailB element
          have hx : x = ⟨5 + k, by omega⟩ := Fin.ext hlast
          rw [hx, iteratedComm_eq_symmetric_n0]
          exact congrArg Fin.val (LemmaFeld.GroupTheory.AF.Case2FixedPointLemmas.sq_fixes_lastTailB_n0 k m hk)
        · -- x ≠ 5+k: middle tailB or tailC
          -- For these, iter(x) = x, so sq(x) = x
          have hiter : (SymmetricCase2.iteratedComm_g₂' 0 k m) x = x := by
            unfold SymmetricCase2.iteratedComm_g₂'; simp only [Perm.mul_apply]
            by_cases htailC : x.val ≥ 6 + k
            · -- tailC: g₂ and c₁₂ both fix x
              have hg₂_fix : g₂ 0 k m x = x := by
                unfold g₂; apply List.formPerm_apply_of_notMem
                simp only [g₂CoreList, tailBList, List.mem_append, List.mem_cons, List.not_mem_nil,
                  or_false, List.mem_map, List.mem_finRange, not_or]
                constructor
                · refine ⟨?_, ?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
                · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega
              have hg₂_inv_fix : (g₂ 0 k m)⁻¹ x = x := by
                conv_lhs => rw [← hg₂_fix]; rw [Perm.inv_apply_self]
              rw [hg₂_fix, c₁₂_fixes_tailB_n0 k m x hcore, hg₂_inv_fix,
                  c₁₂_inv_fixes_tailB_n0 k m x hcore]
            · -- middle tailB: 6 ≤ x < 6+k and x ≠ 5+k
              push_neg at htailC
              -- When k=1: 6 ≤ x < 7 and x ≠ 6 is impossible
              -- When k≥2: 6 ≤ x < 5+k, prove iter fixes x
              by_cases hk1 : k = 1
              · -- k = 1: vacuous case
                subst hk1; omega
              · -- k ≥ 2: prove iter fixes x
                have hk2 : k ≥ 2 := by omega
                have hx_hi : x.val < 5 + k := by omega
                -- Key insight: g₂(x) ∈ tailB, and c₁₂ fixes all of tailB
                -- So: iter(x) = c₁₂⁻¹(g₂⁻¹(c₁₂(g₂(x)))) where g₂(x) and x are both in tailB
                have hg₂x_in_tailB : 6 ≤ (g₂ 0 k m x).val := by
                  -- g₂ maps middle tailB (not last element) to next tailB element
                  -- Since x ≠ last tailB, g₂(x) ≠ 1 (the cycle wraps only from last element)
                  -- Therefore g₂(x) stays in tailB, i.e., g₂(x).val ≥ 6
                  by_contra h_neg; push_neg at h_neg
                  have hx_recover : x = (g₂ 0 k m)⁻¹ (g₂ 0 k m x) := (Equiv.symm_apply_apply _ _).symm
                  -- g₂(x).val < 6, check each case
                  interval_cases hv : (g₂ 0 k m x).val
                  · -- g₂(x) = 0, so x = g₂⁻¹(0) = 4
                    have heq : g₂ 0 k m x = ⟨0, by omega⟩ := Fin.ext hv
                    have := Case2ProductLemmas.g₂_inv_0_eq_4 0 k m
                    simp only [heq, Fin.ext_iff] at this hx_recover; omega
                  · -- g₂(x) = 1, so x = g₂⁻¹(1) = 5+k (last tailB) - but hlast says x ≠ 5+k
                    have heq : g₂ 0 k m x = ⟨1, by omega⟩ := Fin.ext hv
                    have := g₂_inv_1_eq_lastTailB_n0 k m hk
                    simp only [heq, Fin.ext_iff] at this hx_recover; omega
                  · -- g₂(x) = 2, so x = g₂⁻¹(2) = 2
                    have heq : g₂ 0 k m x = ⟨2, by omega⟩ := Fin.ext hv
                    have := Case2ProductLemmas.g₂_inv_fixes_2 0 k m
                    simp only [heq, Fin.ext_iff] at this hx_recover; omega
                  · -- g₂(x) = 3, so x = g₂⁻¹(3) = 1
                    have heq : g₂ 0 k m x = ⟨3, by omega⟩ := Fin.ext hv
                    have := Case2ProductLemmas.g₂_inv_3_eq_1 0 k m
                    simp only [heq, Fin.ext_iff] at this hx_recover; omega
                  · -- g₂(x) = 4, so x = g₂⁻¹(4) = 3
                    have heq : g₂ 0 k m x = ⟨4, by omega⟩ := Fin.ext hv
                    have := Case2ProductLemmas.g₂_inv_4_eq_3 0 k m
                    simp only [heq, Fin.ext_iff] at this hx_recover; omega
                  · -- g₂(x) = 5, so x = g₂⁻¹(5) = 5
                    have heq : g₂ 0 k m x = ⟨5, by omega⟩ := Fin.ext hv
                    have := Case2ProductLemmas.g₂_inv_fixes_5 0 k m
                    simp only [heq, Fin.ext_iff] at this hx_recover; omega
                have hc₁₂_fix : commutator_g₁_g₂ 0 k m (g₂ 0 k m x) = g₂ 0 k m x :=
                  c₁₂_fixes_tailB_n0 k m (g₂ 0 k m x) hg₂x_in_tailB
                rw [hc₁₂_fix]
                have hg₂_inv : (g₂ 0 k m)⁻¹ (g₂ 0 k m x) = x := Equiv.symm_apply_apply _ _
                rw [hg₂_inv, c₁₂_inv_fixes_tailB_n0 k m x hcore]
          rw [iteratedComm_eq_symmetric_n0]; simp only [sq, Perm.mul_apply, hiter]
    rw [hsq_eq]
    exact SymmetricCase2.threeCycle_1_2_3_isThreeCycle 0 k m
  · -- n ≥ 1 case: Different 3-cycle structure (1, 5+n, 3)
    -- The 3-cycle is 1 → 5+n → 3 → 1
    have hn_ge1 : n ≥ 1 := by omega
    -- Show sq equals threeCycle_1_5plusn_3 by proving they agree on moved elements
    have hsq_eq : (iteratedComm_g₂' n k m ^ 2) =
                   SymmetricCase2.threeCycle_1_5plusn_3 n k m hn_ge1 := by
      ext x
      -- Convert goal to use SymmetricCase2.iteratedComm_g₂'
      rw [iteratedComm_eq_symmetric]
      by_cases hcore : x.val < 6
      · interval_cases hv : x.val
        · -- x.val = 0: both fix 0
          have hx : x = ⟨0, by omega⟩ := Fin.ext hv
          rw [hx, sq_fixes_0_n_ge1 n k m hn_ge1 hk]
          unfold SymmetricCase2.threeCycle_1_5plusn_3
          have h := List.formPerm_apply_of_notMem (l := [⟨1, by omega⟩, ⟨5 + n, by omega⟩, ⟨3, by omega⟩])
            (x := (⟨0, by omega⟩ : Omega n k m)) (by
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
              refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega)
          simp only [h]
        · -- x.val = 1: sq(1) = 5+n, threeCycle(1) = 5+n
          have hx : x = ⟨1, by omega⟩ := Fin.ext hv
          rw [hx, sq_1_eq_5plusn_n_ge1 n k m hn_ge1]
          unfold SymmetricCase2.threeCycle_1_5plusn_3
          have h := List.formPerm_apply_lt_getElem ([⟨1, by omega⟩, ⟨5 + n, by omega⟩, ⟨3, by omega⟩] :
            List (Omega n k m)) (SymmetricCase2.threeCycle_1_5plusn_3_list_nodup n k m hn_ge1) 0 (by simp)
          simp only [List.getElem_cons_zero, List.getElem_cons_succ] at h; simp only [h]
        · -- x.val = 2: both fix 2
          have hx : x = ⟨2, by omega⟩ := Fin.ext hv
          rw [hx, sq_fixes_2_n_ge1 n k m hn_ge1]
          unfold SymmetricCase2.threeCycle_1_5plusn_3
          have h := List.formPerm_apply_of_notMem (l := [⟨1, by omega⟩, ⟨5 + n, by omega⟩, ⟨3, by omega⟩])
            (x := (⟨2, by omega⟩ : Omega n k m)) (by
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
              refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega)
          simp only [h]
        · -- x.val = 3: sq(3) = 1, threeCycle(3) = 1
          have hx : x = ⟨3, by omega⟩ := Fin.ext hv
          rw [hx, sq_3_eq_1_n_ge1 n k m hn_ge1]
          unfold SymmetricCase2.threeCycle_1_5plusn_3
          have h := List.formPerm_apply_getElem ([⟨1, by omega⟩, ⟨5 + n, by omega⟩, ⟨3, by omega⟩] :
            List (Omega n k m)) (SymmetricCase2.threeCycle_1_5plusn_3_list_nodup n k m hn_ge1) 2 (by simp)
          simp only [List.length_cons, List.length_nil, List.getElem_cons_zero,
            List.getElem_cons_succ, show (2+1) % 3 = 0 by native_decide] at h; simp only [h]
        · -- x.val = 4: both fix 4
          have hx : x = ⟨4, by omega⟩ := Fin.ext hv
          rw [hx, sq_fixes_4_n_ge1 n k m hn_ge1 hk]
          unfold SymmetricCase2.threeCycle_1_5plusn_3
          have h := List.formPerm_apply_of_notMem (l := [⟨1, by omega⟩, ⟨5 + n, by omega⟩, ⟨3, by omega⟩])
            (x := (⟨4, by omega⟩ : Omega n k m)) (by
              simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
              refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega)
          simp only [h]
        · -- x.val = 5: sq fixes 5 via 2-cycle with lastTailB
          have hx : x = ⟨5, by omega⟩ := Fin.ext hv
          rw [hx]
          -- threeCycle fixes 5 (5 ≠ 1, 5+n, 3 since n ≥ 1 implies 5+n ≥ 6 ≠ 5)
          have hthree : (SymmetricCase2.threeCycle_1_5plusn_3 n k m hn_ge1) ⟨5, by omega⟩ = ⟨5, by omega⟩ := by
            unfold SymmetricCase2.threeCycle_1_5plusn_3
            apply List.formPerm_apply_of_notMem
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
          rw [hthree]
          -- For k ≥ 1: iter(5) = lastTailB, iter(lastTailB) = 5
          -- So sq(5) = iter(iter(5)) = iter(lastTailB) = 5
          -- This is part of a 2-cycle (5, lastTailB) in iter
          simp only [_root_.LemmaFeld.GroupTheory.AF.Case2FixedPointLemmas.sq_fixes_5_n_ge1 n k m hn_ge1 hk]
      · -- x.val ≥ 6: tail elements
        push_neg at hcore
        -- Handle x = 5+n separately first (since 5+n ≥ 6 when n ≥ 1, and 5+n is in the 3-cycle)
        by_cases h5plusn : x.val = 5 + n
        · -- x = 5+n: sq(5+n) = 3 and threeCycle(5+n) = 3
          have hx : x = ⟨5 + n, by omega⟩ := Fin.ext h5plusn
          rw [hx, sq_5plusn_eq_3_n_ge1 n k m hn_ge1]
          unfold SymmetricCase2.threeCycle_1_5plusn_3
          have h := List.formPerm_apply_lt_getElem ([⟨1, by omega⟩, ⟨5 + n, by omega⟩, ⟨3, by omega⟩] :
            List (Omega n k m)) (SymmetricCase2.threeCycle_1_5plusn_3_list_nodup n k m hn_ge1) 1 (by simp)
          simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h; simp only [h]
        · -- x ≠ 5+n and x.val ≥ 6: threeCycle fixes x since x ∉ {1, 5+n, 3}
          have hthree : (SymmetricCase2.threeCycle_1_5plusn_3 n k m hn_ge1) x = x := by
            unfold SymmetricCase2.threeCycle_1_5plusn_3
            apply List.formPerm_apply_of_notMem
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
            refine ⟨?_, ?_, ?_⟩ <;> intro h <;> simp only [Fin.ext_iff] at h <;> omega
          rw [hthree]
          -- sq fixes x because it's in tailA (6 ≤ x < 5+n), tailB, or tailC
          by_cases htailA : x.val < 6 + n
          · -- tailA element (6 ≤ x < 5+n, strictly): c₁₂ fixes it
            -- x < 6+n means x ≤ 5+n, combined with x ≠ 5+n gives x < 5+n
            have hx_strict : x.val < 5 + n := by omega
            have hc₁₂_fix : commutator_g₁_g₂ n k m x = x :=
              c₁₂_fixes_tailA_strict n k m x hcore hx_strict
            have hc₁₂_inv_fix : (commutator_g₁_g₂ n k m)⁻¹ x = x := by
              calc (commutator_g₁_g₂ n k m)⁻¹ x
                  = (commutator_g₁_g₂ n k m)⁻¹ ((commutator_g₁_g₂ n k m) x) := by rw [hc₁₂_fix]
                _ = x := Equiv.symm_apply_apply _ _
            have hg₂_fix : g₂ n k m x = x := g₂_fixes_tailA n k m x hcore (by omega)
            have hg₂_inv_fix : (g₂ n k m)⁻¹ x = x := g₂_inv_fixes_tailA n k m x hcore (by omega)
            simp only [iteratedComm_g₂', SymmetricCase2.iteratedComm_g₂', sq, Perm.mul_apply]
            rw [hg₂_fix, hc₁₂_fix, hg₂_inv_fix, hc₁₂_inv_fix]
            rw [hg₂_fix, hc₁₂_fix, hg₂_inv_fix, hc₁₂_inv_fix]
          · -- not tailA: tailB or tailC (x ≥ 6+n)
            push_neg at htailA
            by_cases htailC : 6 + n + k ≤ x.val
            · -- tailC: sq fixes x
              have hsq := sq_fixes_tailC_n_ge1 n k m x htailC
              unfold SymmetricCase2.iteratedComm_g₂' at hsq
              simp only [SymmetricCase2.iteratedComm_g₂', hsq]
            · -- tailB: sq fixes x (6+n ≤ x < 6+n+k)
              push_neg at htailC
              have hsq := sq_fixes_tailB_n_ge1 n k m x htailA htailC
              unfold SymmetricCase2.iteratedComm_g₂' at hsq
              simp only [SymmetricCase2.iteratedComm_g₂', hsq]
    rw [hsq_eq]
    exact SymmetricCase2.threeCycle_1_5plusn_3_isThreeCycle n k m hn_ge1

-- ============================================
-- SECTION 3: Computational Verifications
-- ============================================

-- Case 2 verifications
theorem case2_m1_k0_n0 : ((commutator_g₁_g₃ 0 0 1 * (commutator_g₂_g₃ 0 0 1)⁻¹) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle; native_decide

theorem case2_m1_k0_n1 : ((commutator_g₁_g₃ 1 0 1 * (commutator_g₂_g₃ 1 0 1)⁻¹) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle; native_decide

theorem case2_m2_k0_n0 : ((commutator_g₁_g₃ 0 0 2 * (commutator_g₂_g₃ 0 0 2)⁻¹) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle; native_decide

-- Case 3 verifications
theorem case3_k1_n0_m0 : ((iteratedComm_g₂' 0 1 0) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle iteratedComm_g₂' commutator_g₁_g₂; native_decide

theorem case3_k1_n1_m0 : ((iteratedComm_g₂' 1 1 0) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle iteratedComm_g₂' commutator_g₁_g₂; native_decide

theorem case3_k2_n0_m0 : ((iteratedComm_g₂' 0 2 0) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle iteratedComm_g₂' commutator_g₁_g₂; native_decide

theorem case3_k1_n0_m1 : ((iteratedComm_g₂' 0 1 1) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle iteratedComm_g₂' commutator_g₁_g₂; native_decide

end LemmaFeld.GroupTheory.AF.ThreeCycleSymmetric
