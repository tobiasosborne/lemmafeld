/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_CycleSupport
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_SupportCover
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_FixedPoints
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_3
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_OrbitContinuation
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Lemma 11.5 Case 2: Helper Lemmas

Helper lemmas showing B subset tailA and g1(a1) computation for Case 2 analysis.
-/

open Equiv Equiv.Perm Set
variable {n k m : ℕ}

theorem elem5_in_support_g₃ : (⟨5, by omega⟩ : Omega n k m) ∈ (g₃ n k m).support := by
  have hNodup := g₃_list_nodup n k m
  have hNotSingleton : ∀ x, g₃CoreList n k m ++ tailCList n k m ≠ [x] := by
    intro x h
    have : (g₃CoreList n k m ++ tailCList n k m).length = 1 := by rw [h]; simp
    have := g₃_cycle_length n k m; omega
  rw [g₃, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₃CoreList, List.mem_cons]; tauto

theorem elem3_in_support_g₂' : (⟨3, by omega⟩ : Omega n k m) ∈ (g₂ n k m).support := by
  have hNodup := g₂_list_nodup n k m
  have hNotSingleton : ∀ x, g₂CoreList n k m ++ tailBList n k m ≠ [x] := by
    intro x h
    have : (g₂CoreList n k m ++ tailBList n k m).length = 1 := by rw [h]; simp
    have := g₂_cycle_length n k m; omega
  rw [g₂, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₂CoreList, List.mem_cons]; tauto

theorem core_in_support_g₂_or_g₃ (x : Omega n k m) (hCore : isCore x) :
    x ∈ (g₂ n k m).support ∨ x ∈ (g₃ n k m).support := by
  obtain ⟨v, hv⟩ := x
  simp only [isCore] at hCore
  have : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · left; convert elem0_in_support_g₂ (n := n) (k := k) (m := m)
  · left; convert elem1_in_support_g₂ (n := n) (k := k) (m := m)
  · right; convert elem2_in_support_g₃ (n := n) (k := k) (m := m)
  · left; convert elem3_in_support_g₂' (n := n) (k := k) (m := m)
  · left; convert elem4_in_support_g₂ (n := n) (k := k) (m := m)
  · right; convert elem5_in_support_g₃ (n := n) (k := k) (m := m)

theorem case2_B_subset_tailA (B : Set (Omega n k m))
    (hDisj₂ : Disjoint (↑(g₂ n k m).support) B)
    (hDisj₃ : Disjoint (↑(g₃ n k m).support) B) :
    ∀ x ∈ B, isTailA x := by
  intro x hx
  rcases Omega.partition x with hCore | hA | hB | hC
  · rcases core_in_support_g₂_or_g₃ x hCore with h2 | h3
    · exact (Set.disjoint_iff.mp hDisj₂ ⟨h2, hx⟩).elim
    · exact (Set.disjoint_iff.mp hDisj₃ ⟨h3, hx⟩).elim
  · exact hA
  · have h_in_supp : x ∈ (g₂ n k m).support := by
      simp only [isTailB] at hB; obtain ⟨hLo, hHi⟩ := hB
      have hi : x.val - 6 - n < k := by have := x.isLt; omega
      convert tailB_in_support_g₂ (⟨x.val - 6 - n, hi⟩ : Fin k) using 1
      simp only [Fin.ext_iff]; omega
    exact (Set.disjoint_iff.mp hDisj₂ ⟨h_in_supp, hx⟩).elim
  · have h_in_supp : x ∈ (g₃ n k m).support := by
      simp only [isTailC] at hC; obtain ⟨hLo, hHi⟩ := hC
      have hi : x.val - 6 - n - k < m := by have := x.isLt; omega
      convert tailC_in_support_g₃ (⟨x.val - 6 - n - k, hi⟩ : Fin m) using 1
      simp only [Fin.ext_iff]; omega
    exact (Set.disjoint_iff.mp hDisj₃ ⟨h_in_supp, hx⟩).elim

lemma g₁_list_length' (n k m : ℕ) :
    (g₁CoreList n k m ++ tailAList n k m).length = 4 + n := by
  simp only [g₁CoreList, tailAList, List.length_append, List.length_cons, List.length_nil,
    List.length_map, List.length_finRange]

lemma g₁_list_idx_4 (n k m : ℕ) (hn : n ≥ 1) :
    (g₁CoreList n k m ++ tailAList n k m)[4]'(by rw [g₁_list_length']; omega) =
    (⟨6, by omega⟩ : Omega n k m) := by
  have h2 : (g₁CoreList n k m).length ≤ 4 := by simp [g₁CoreList]
  rw [List.getElem_append_right h2]
  simp only [g₁CoreList, List.length_cons, List.length_nil, Nat.sub_self]
  simp only [tailAList, List.getElem_map, List.getElem_finRange]; rfl

lemma g₁_list_idx_5 (n k m : ℕ) (hn : n ≥ 2) :
    (g₁CoreList n k m ++ tailAList n k m)[5]'(by rw [g₁_list_length']; omega) =
    (⟨7, by omega⟩ : Omega n k m) := by
  have h2 : (g₁CoreList n k m).length ≤ 5 := by simp [g₁CoreList]
  rw [List.getElem_append_right h2]
  simp only [g₁CoreList, List.length_cons, List.length_nil]
  simp only [tailAList, List.getElem_map, List.getElem_finRange]; rfl

/-- For n >= 2, g₁(a₁) = element 7 -/
theorem g₁_a₁_eq_7 (hn2 : n ≥ 2) :
    g₁ n k m (⟨6, by omega⟩ : Omega n k m) = ⟨7, by omega⟩ := by
  unfold g₁
  have hNodup := g₁_list_nodup n k m
  have h_len := g₁_list_length' n k m
  have h_4_lt : 4 < (g₁CoreList n k m ++ tailAList n k m).length := by omega
  have h_idx4 := g₁_list_idx_4 n k m (by omega : n ≥ 1)
  rw [← h_idx4, List.formPerm_apply_getElem _ hNodup 4 h_4_lt]
  have h_5_lt' : 5 < 4 + n := by omega
  have h_mod_eq : (4 + 1) % (4 + n) = 5 := Nat.mod_eq_of_lt h_5_lt'
  simp only [h_len, h_mod_eq]; exact g₁_list_idx_5 n k m hn2

lemma g₁_a₁_eq_elem7 (hn : n ≥ 1) (hn2 : n ≥ 2) :
    g₁ n k m (a₁ n k m hn) = (⟨7, by omega⟩ : Omega n k m) := by
  unfold a₁; exact g₁_a₁_eq_7 hn2

-- NOTE: The old `case2_B_ncard_le_one` theorem was DELETED because it was FALSE for n ≥ 3.
-- Counterexample: B = {6, 8} for n = 3 satisfies all hypotheses but |B| = 2.
-- The correct approach requires B to be a proper block (with block dichotomy for g₁ powers).
-- See case2_impossible_B and case2_impossible_C in SymmetricMain.lean for the correct pattern.

/-- Core elements {0,1,2,3,4,5} are in supp(g₁) or supp(g₃) -/
theorem core_in_support_g₁_or_g₃ (x : Omega n k m) (hCore : isCore x) :
    x ∈ (g₁ n k m).support ∨ x ∈ (g₃ n k m).support := by
  obtain ⟨v, hv⟩ := x
  simp only [isCore] at hCore
  have : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · left; convert elem0_in_support_g₁ (n := n) (k := k) (m := m)
  · right; convert elem1_in_support_g₃ (n := n) (k := k) (m := m)
  · right; convert elem2_in_support_g₃ (n := n) (k := k) (m := m)
  · left; convert elem3_in_support_g₁ (n := n) (k := k) (m := m)
  · right; convert elem4_in_support_g₃ (n := n) (k := k) (m := m)
  · left; convert elem5_in_support_g₁ (n := n) (k := k) (m := m)

/-- Tail C elements are not in supp(g₂) -/
theorem tailC_not_in_support_g₂' (_ : m ≥ 1) (i : Fin m) :
    (⟨6 + n + k + i.val, by omega⟩ : Omega n k m) ∉ (g₂ n k m).support := by
  simp only [g₂, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h; simp only [List.mem_append, g₂CoreList, tailBList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
  · obtain ⟨j, _, hj⟩ := h; simp only [Fin.ext_iff] at hj; have := j.isLt; have := i.isLt; omega

/-- If B ⊆ supp(g₂), B ∩ supp(g₁) = ∅, and B ∩ supp(g₃) = ∅, then B ⊆ tailB -/
theorem case2_B_subset_tailB (B : Set (Omega n k m))
    (hSubG₂ : B ⊆ ↑(g₂ n k m).support)
    (hDisj₁ : Disjoint (↑(g₁ n k m).support) B)
    (hDisj₃ : Disjoint (↑(g₃ n k m).support) B) :
    ∀ x ∈ B, isTailB x := by
  intro x hx
  rcases Omega.partition x with hCore | hA | hB | hC
  · -- Core element: in supp(g₁) or supp(g₃), contradicts disjointness
    rcases core_in_support_g₁_or_g₃ x hCore with h1 | h3
    · exact (Set.disjoint_iff.mp hDisj₁ ⟨h1, hx⟩).elim
    · exact (Set.disjoint_iff.mp hDisj₃ ⟨h3, hx⟩).elim
  · -- TailA: not in supp(g₂), contradicts B ⊆ supp(g₂)
    simp only [isTailA] at hA; obtain ⟨hLo, hHi⟩ := hA
    have hi : x.val - 6 < n := by omega
    have hn1 : n ≥ 1 := by omega
    have hNotSupp : x ∉ (g₂ n k m).support := by
      have hEq : (⟨6 + (x.val - 6), by have := x.isLt; omega⟩ : Omega n k m) = x := by
        apply Fin.ext; simp only [Fin.val_mk]; omega
      rw [← hEq]
      exact tailA_not_in_support_g₂ hn1 ⟨x.val - 6, hi⟩
    exact (hNotSupp (hSubG₂ hx)).elim
  · exact hB
  · -- TailC: not in supp(g₂), contradicts B ⊆ supp(g₂)
    simp only [isTailC] at hC; obtain ⟨hLo, hHi⟩ := hC
    have hi : x.val - 6 - n - k < m := by have := x.isLt; omega
    have hm1 : m ≥ 1 := by omega
    have hNotSupp : x ∉ (g₂ n k m).support := by
      have hEq : (⟨6 + n + k + (x.val - 6 - n - k), by have := x.isLt; omega⟩ :
          Omega n k m) = x := by
        apply Fin.ext; simp only [Fin.val_mk]; omega
      rw [← hEq]
      exact tailC_not_in_support_g₂' hm1 ⟨x.val - 6 - n - k, hi⟩
    exact (hNotSupp (hSubG₂ hx)).elim

/-- Core elements {0,1,2,3,4,5} are in supp(g₁) or supp(g₂) -/
theorem core_in_support_g₁_or_g₂ (x : Omega n k m) (hCore : isCore x) :
    x ∈ (g₁ n k m).support ∨ x ∈ (g₂ n k m).support := by
  obtain ⟨v, hv⟩ := x
  simp only [isCore] at hCore
  have : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl
  · left; convert elem0_in_support_g₁ (n := n) (k := k) (m := m)
  · right; convert elem1_in_support_g₂ (n := n) (k := k) (m := m)
  · left; convert elem2_in_support_g₁' (n := n) (k := k) (m := m)
  · left; convert elem3_in_support_g₁ (n := n) (k := k) (m := m)
  · right; convert elem4_in_support_g₂ (n := n) (k := k) (m := m)
  · left; convert elem5_in_support_g₁ (n := n) (k := k) (m := m)

/-- If B ⊆ supp(g₃), B ∩ supp(g₁) = ∅, and B ∩ supp(g₂) = ∅, then B ⊆ tailC -/
theorem case2_C_subset_tailC (B : Set (Omega n k m))
    (hSubG₃ : B ⊆ ↑(g₃ n k m).support)
    (hDisj₁ : Disjoint (↑(g₁ n k m).support) B)
    (hDisj₂ : Disjoint (↑(g₂ n k m).support) B) :
    ∀ x ∈ B, isTailC x := by
  intro x hx
  rcases Omega.partition x with hCore | hA | hB | hC
  · -- Core element: in supp(g₁) or supp(g₂), contradicts disjointness
    rcases core_in_support_g₁_or_g₂ x hCore with h1 | h2
    · exact (Set.disjoint_iff.mp hDisj₁ ⟨h1, hx⟩).elim
    · exact (Set.disjoint_iff.mp hDisj₂ ⟨h2, hx⟩).elim
  · -- TailA: in supp(g₁), contradicts B ∩ supp(g₁) = ∅
    simp only [isTailA] at hA; obtain ⟨hLo, hHi⟩ := hA
    have hi : x.val - 6 < n := by omega
    have h_in_supp : x ∈ (g₁ n k m).support := by
      have hEq : (⟨6 + (x.val - 6), by have := x.isLt; omega⟩ : Omega n k m) = x := by
        apply Fin.ext; simp only [Fin.val_mk]; omega
      rw [← hEq]; exact tailA_in_support_g₁ ⟨x.val - 6, hi⟩
    exact (Set.disjoint_iff.mp hDisj₁ ⟨h_in_supp, hx⟩).elim
  · -- TailB: in supp(g₂), contradicts B ∩ supp(g₂) = ∅
    simp only [isTailB] at hB; obtain ⟨hLo, hHi⟩ := hB
    have hi : x.val - 6 - n < k := by have := x.isLt; omega
    have h_in_supp : x ∈ (g₂ n k m).support := by
      have hEq : (⟨6 + n + (x.val - 6 - n), by have := x.isLt; omega⟩ : Omega n k m) = x := by
        apply Fin.ext; simp only [Fin.val_mk]; omega
      rw [← hEq]; exact tailB_in_support_g₂ ⟨x.val - 6 - n, hi⟩
    exact (Set.disjoint_iff.mp hDisj₂ ⟨h_in_supp, hx⟩).elim
  · exact hC

