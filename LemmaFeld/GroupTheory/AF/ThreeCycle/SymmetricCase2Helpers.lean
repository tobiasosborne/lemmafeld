/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma06
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Helper Lemmas for Symmetric Case 2: k ≥ 1

When k ≥ 1, the iterated commutator [[g₁,g₂], g₂] squared is a 3-cycle.
This file provides lemmas for proving (iteratedComm_g₂')² is a 3-cycle.

## Key Insight

The iterated commutator [[g₁,g₂], g₂] = c₁₂⁻¹ * g₂⁻¹ * c₁₂ * g₂.
When k ≥ 1, the squared product is the 3-cycle (1, 2, 3).
-/

open Equiv Perm

namespace LemmaFeld.GroupTheory.AF.SymmetricCase2

-- ============================================
-- SECTION 1: Iterated commutator definition
-- ============================================

/-- The iterated commutator [[g₁,g₂], g₂] -/
def iteratedComm_g₂' (n k m : ℕ) : Perm (Omega n k m) :=
  (commutator_g₁_g₂ n k m)⁻¹ * (g₂ n k m)⁻¹ * commutator_g₁_g₂ n k m * g₂ n k m

-- ============================================
-- SECTION 2: The 3-cycle definition
-- ============================================

/-- The 3-cycle (1, 2, 3) on Omega n k m -/
def threeCycle_1_2_3 (n k m : ℕ) : Perm (Omega n k m) :=
  [⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩].formPerm

/-- The list [1, 2, 3] has no duplicates -/
theorem threeCycle_list_nodup (n k m : ℕ) :
    ([⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩] : List (Omega n k m)).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, Fin.mk.injEq, or_false, not_or]
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, ⟨not_false, List.nodup_nil⟩⟩⟩

/-- threeCycle_1_2_3 is a 3-cycle -/
theorem threeCycle_1_2_3_isThreeCycle (n k m : ℕ) :
    (threeCycle_1_2_3 n k m).IsThreeCycle := by
  unfold threeCycle_1_2_3
  rw [← card_support_eq_three_iff, List.support_formPerm_of_nodup _ (threeCycle_list_nodup n k m)]
  · simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton, Fin.mk.injEq]; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton, Fin.mk.injEq, not_or]; omega
  · intro x h; have := congrArg List.length h; simp at this

-- ============================================
-- SECTION 2b: The 3-cycle (1, 5+n, 3) for n ≥ 1
-- ============================================

/-- The 3-cycle (1, 5+n, 3) on Omega n k m for n ≥ 1: sends 1→5+n→3→1 -/
def threeCycle_1_5plusn_3 (n k m : ℕ) (hn : n ≥ 1) : Perm (Omega n k m) :=
  [⟨1, by omega⟩, ⟨5 + n, by omega⟩, ⟨3, by omega⟩].formPerm

theorem threeCycle_1_5plusn_3_list_nodup (n k m : ℕ) (hn : n ≥ 1) :
    ([⟨1, by omega⟩, ⟨5 + n, by omega⟩, ⟨3, by omega⟩] : List (Omega n k m)).Nodup := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, Fin.mk.injEq, or_false, not_or]
  refine ⟨⟨by omega, by omega⟩, ⟨by omega, ⟨not_false, List.nodup_nil⟩⟩⟩

/-- threeCycle_1_5plusn_3 is a 3-cycle -/
theorem threeCycle_1_5plusn_3_isThreeCycle (n k m : ℕ) (hn : n ≥ 1) :
    (threeCycle_1_5plusn_3 n k m hn).IsThreeCycle := by
  unfold threeCycle_1_5plusn_3
  rw [← card_support_eq_three_iff, List.support_formPerm_of_nodup _ (threeCycle_1_5plusn_3_list_nodup n k m hn)]
  · simp only [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
    rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_singleton]
    · simp only [Finset.mem_singleton, Fin.mk.injEq]; omega
    · simp only [Finset.mem_insert, Finset.mem_singleton, Fin.mk.injEq, not_or]; omega
  · intro x h; have := congrArg List.length h; simp at this

-- ============================================
-- SECTION 3: Computational verifications
-- ============================================

/-- IsThreeCycle for n=0, k=1, m=0 -/
theorem isThreeCycle_n0_k1_m0 : ((iteratedComm_g₂' 0 1 0) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle iteratedComm_g₂' commutator_g₁_g₂; native_decide

/-- IsThreeCycle for n=1, k=1, m=0 -/
theorem isThreeCycle_n1_k1_m0 : ((iteratedComm_g₂' 1 1 0) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle iteratedComm_g₂' commutator_g₁_g₂; native_decide

/-- IsThreeCycle for n=0, k=2, m=0 -/
theorem isThreeCycle_n0_k2_m0 : ((iteratedComm_g₂' 0 2 0) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle iteratedComm_g₂' commutator_g₁_g₂; native_decide

/-- IsThreeCycle for n=0, k=1, m=1 -/
theorem isThreeCycle_n0_k1_m1 : ((iteratedComm_g₂' 0 1 1) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle iteratedComm_g₂' commutator_g₁_g₂; native_decide

/-- IsThreeCycle for n=1, k=1, m=1 -/
theorem isThreeCycle_n1_k1_m1 : ((iteratedComm_g₂' 1 1 1) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle iteratedComm_g₂' commutator_g₁_g₂; native_decide

/-- IsThreeCycle for n=2, k=2, m=2 -/
theorem isThreeCycle_n2_k2_m2 : ((iteratedComm_g₂' 2 2 2) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle iteratedComm_g₂' commutator_g₁_g₂; native_decide

/-- IsThreeCycle for n=1, k=2, m=1 -/
theorem isThreeCycle_n1_k2_m1 : ((iteratedComm_g₂' 1 2 1) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle iteratedComm_g₂' commutator_g₁_g₂; native_decide

/-- IsThreeCycle for n=0, k=3, m=0 -/
theorem isThreeCycle_n0_k3_m0 : ((iteratedComm_g₂' 0 3 0) ^ 2).IsThreeCycle := by
  unfold IsThreeCycle iteratedComm_g₂' commutator_g₁_g₂; native_decide

end LemmaFeld.GroupTheory.AF.SymmetricCase2
