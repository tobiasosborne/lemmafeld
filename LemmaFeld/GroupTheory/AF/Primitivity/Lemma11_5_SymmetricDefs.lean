/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_2
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_FixedPoints
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_CycleSupport
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_Defs
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_SupportCover
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_Case2

/-!
# Lemma 11.5: Symmetric Cases - Definitions and Basic Lemmas

Defines b₁, c₁ and their basic properties for symmetric case analysis.

## Main Results

* `b₁`, `c₁`: First tail B and C elements
* `b₁_mem_support_g₂`, `c₁_mem_support_g₃`: Support membership
* `lemma11_3_tail_B_in_block`, `lemma11_3_tail_C_in_block`: Tail in block
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

-- ============================================
-- SECTION 1: FIRST TAIL B AND C ELEMENTS
-- ============================================

/-- The first B-tail element b₁ (index 6+n in 0-indexed). -/
def b₁ (n k m : ℕ) (hk : k ≥ 1) : Omega n k m := ⟨6 + n, by omega⟩

/-- The first C-tail element c₁ (index 6+n+k in 0-indexed). -/
def c₁ (n k m : ℕ) (hm : m ≥ 1) : Omega n k m := ⟨6 + n + k, by omega⟩

/-- A set contains b₁ -/
def containsB₁ (B : Set (Omega n k m)) (hk : k ≥ 1) : Prop := b₁ n k m hk ∈ B

/-- A set contains c₁ -/
def containsC₁ (B : Set (Omega n k m)) (hm : m ≥ 1) : Prop := c₁ n k m hm ∈ B

-- ============================================
-- SECTION 2: b₁ AND c₁ IN SUPPORTS
-- ============================================

/-- b₁ is in the support of g₂ -/
theorem b₁_mem_support_g₂ (hk : k ≥ 1) : b₁ n k m hk ∈ (g₂ n k m).support := by
  have hNodup := g₂_list_nodup n k m
  have hNotSingleton : ∀ x, g₂CoreList n k m ++ tailBList n k m ≠ [x] := by
    intro x h; have : (g₂CoreList n k m ++ tailBList n k m).length = 1 := by rw [h]; simp
    have := g₂_cycle_length n k m; omega
  rw [b₁, g₂, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, tailBList, List.mem_map, List.mem_finRange]
  right; exact ⟨⟨0, hk⟩, trivial, by simp⟩

/-- c₁ is in the support of g₃ -/
theorem c₁_mem_support_g₃ (hm : m ≥ 1) : c₁ n k m hm ∈ (g₃ n k m).support := by
  have hNodup := g₃_list_nodup n k m
  have hNotSingleton : ∀ x, g₃CoreList n k m ++ tailCList n k m ≠ [x] := by
    intro x h; have : (g₃CoreList n k m ++ tailCList n k m).length = 1 := by rw [h]; simp
    have := g₃_cycle_length n k m; omega
  rw [c₁, g₃, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, tailCList, List.mem_map, List.mem_finRange]
  right; exact ⟨⟨0, hm⟩, trivial, by simp⟩

-- ============================================
-- SECTION 3: TAIL B/C IN BLOCK LEMMAS
-- ============================================

/-- If B contains b₁ and g₂(B) = B, then supp(g₂) ⊆ B -/
theorem lemma11_3_tail_B_in_block (hk : k ≥ 1) (B : Set (Omega n k m))
    (hB₁ : containsB₁ B hk) (hB : PreservesSet (g₂ n k m) B) :
    ((g₂ n k m).support : Set (Omega n k m)) ⊆ B := by
  have hCycle : (g₂ n k m).IsCycle := g₂_isCycle n k m
  have hMeet : ((g₂ n k m).support : Set (Omega n k m)) ∩ B ≠ ∅ := by
    rw [Set.nonempty_iff_ne_empty.symm]; use b₁ n k m hk; exact ⟨b₁_mem_support_g₂ hk, hB₁⟩
  rcases cycle_support_subset_or_disjoint hCycle hB with hSub | hDisj
  · exact hSub
  · exfalso; rw [Set.disjoint_iff_inter_eq_empty] at hDisj; exact hMeet hDisj

/-- If B contains c₁ and g₃(B) = B, then supp(g₃) ⊆ B -/
theorem lemma11_3_tail_C_in_block (hm : m ≥ 1) (B : Set (Omega n k m))
    (hC₁ : containsC₁ B hm) (hB : PreservesSet (g₃ n k m) B) :
    ((g₃ n k m).support : Set (Omega n k m)) ⊆ B := by
  have hCycle : (g₃ n k m).IsCycle := g₃_isCycle n k m
  have hMeet : ((g₃ n k m).support : Set (Omega n k m)) ∩ B ≠ ∅ := by
    rw [Set.nonempty_iff_ne_empty.symm]; use c₁ n k m hm; exact ⟨c₁_mem_support_g₃ hm, hC₁⟩
  rcases cycle_support_subset_or_disjoint hCycle hB with hSub | hDisj
  · exact hSub
  · exfalso; rw [Set.disjoint_iff_inter_eq_empty] at hDisj; exact hMeet hDisj

-- ============================================
-- SECTION 4: FIXED POINT LEMMAS FOR B/C
-- ============================================

/-- Tail B elements are not in supp(g₁) -/
theorem tailB_not_in_support_g₁ (_ : k ≥ 1) (i : Fin k) :
    (⟨6 + n + i.val, by omega⟩ : Omega n k m) ∉ (g₁ n k m).support := by
  simp only [g₁, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h; simp only [List.mem_append, g₁CoreList, tailAList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
  · obtain ⟨j, _, hj⟩ := h; simp only [Fin.ext_iff] at hj; have := j.isLt; omega

/-- Tail B elements are not in supp(g₃) -/
theorem tailB_not_in_support_g₃ (_ : k ≥ 1) (i : Fin k) :
    (⟨6 + n + i.val, by omega⟩ : Omega n k m) ∉ (g₃ n k m).support := by
  simp only [g₃, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h; simp only [List.mem_append, g₃CoreList, tailCList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
  · obtain ⟨j, _, hj⟩ := h; simp only [Fin.ext_iff] at hj; have := j.isLt; have := i.isLt; omega

/-- g₁ fixes b₁ -/
theorem g₁_fixes_b₁ (hk : k ≥ 1) : g₁ n k m (b₁ n k m hk) = b₁ n k m hk := by
  unfold b₁; exact fixed_outside_support _ _ (tailB_not_in_support_g₁ hk ⟨0, hk⟩)

/-- g₃ fixes b₁ -/
theorem g₃_fixes_b₁ (hk : k ≥ 1) : g₃ n k m (b₁ n k m hk) = b₁ n k m hk := by
  unfold b₁; exact fixed_outside_support _ _ (tailB_not_in_support_g₃ hk ⟨0, hk⟩)

/-- Tail C elements are not in supp(g₁) -/
theorem tailC_not_in_support_g₁ (_ : m ≥ 1) (i : Fin m) :
    (⟨6 + n + k + i.val, by omega⟩ : Omega n k m) ∉ (g₁ n k m).support := by
  simp only [g₁, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h; simp only [List.mem_append, g₁CoreList, tailAList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
  · obtain ⟨j, _, hj⟩ := h; simp only [Fin.ext_iff] at hj; have := j.isLt; omega

/-- Tail C elements are not in supp(g₂) -/
theorem tailC_not_in_support_g₂ (_ : m ≥ 1) (i : Fin m) :
    (⟨6 + n + k + i.val, by omega⟩ : Omega n k m) ∉ (g₂ n k m).support := by
  simp only [g₂, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h; simp only [List.mem_append, g₂CoreList, tailBList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
  · obtain ⟨j, _, hj⟩ := h; simp only [Fin.ext_iff] at hj; have := j.isLt; have := i.isLt; omega

/-- g₁ fixes c₁ -/
theorem g₁_fixes_c₁ (hm : m ≥ 1) : g₁ n k m (c₁ n k m hm) = c₁ n k m hm := by
  unfold c₁; exact fixed_outside_support _ _ (tailC_not_in_support_g₁ hm ⟨0, hm⟩)

/-- g₂ fixes c₁ -/
theorem g₂_fixes_c₁ (hm : m ≥ 1) : g₂ n k m (c₁ n k m hm) = c₁ n k m hm := by
  unfold c₁; exact fixed_outside_support _ _ (tailC_not_in_support_g₂ hm ⟨0, hm⟩)

-- ============================================
-- SECTION 5: CASE 2 STABILIZATION (k ≥ 1 and m ≥ 1)
-- ============================================

/-- **Case 2 Stabilization for k ≥ 1**: g₂(B) ≠ B forces g₁(B) = B and g₃(B) = B. -/
theorem case2_forces_stabilization_B (hk : k ≥ 1) (B : Set (Omega n k m))
    (hB₁ : b₁ n k m hk ∈ B)
    (h₁Disj : ¬PreservesSet (g₁ n k m) B → Disjoint (g₁ n k m '' B) B)
    (h₃Disj : ¬PreservesSet (g₃ n k m) B → Disjoint (g₃ n k m '' B) B) :
    PreservesSet (g₁ n k m) B ∧ PreservesSet (g₃ n k m) B := by
  constructor
  · by_contra hNotPres
    have hDisj := h₁Disj hNotPres
    have hFix : g₁ n k m (b₁ n k m hk) = b₁ n k m hk := g₁_fixes_b₁ hk
    have h_in_both := fixed_point_blocks_intersect (g₁ n k m) B (b₁ n k m hk) hB₁ hFix
    exact Set.disjoint_iff.mp hDisj h_in_both
  · by_contra hNotPres
    have hDisj := h₃Disj hNotPres
    have hFix : g₃ n k m (b₁ n k m hk) = b₁ n k m hk := g₃_fixes_b₁ hk
    have h_in_both := fixed_point_blocks_intersect (g₃ n k m) B (b₁ n k m hk) hB₁ hFix
    exact Set.disjoint_iff.mp hDisj h_in_both

/-- **Case 2 Stabilization for m ≥ 1**: g₃(B) ≠ B forces g₁(B) = B and g₂(B) = B. -/
theorem case2_forces_stabilization_C (hm : m ≥ 1) (B : Set (Omega n k m))
    (hC₁ : c₁ n k m hm ∈ B)
    (h₁Disj : ¬PreservesSet (g₁ n k m) B → Disjoint (g₁ n k m '' B) B)
    (h₂Disj : ¬PreservesSet (g₂ n k m) B → Disjoint (g₂ n k m '' B) B) :
    PreservesSet (g₁ n k m) B ∧ PreservesSet (g₂ n k m) B := by
  constructor
  · by_contra hNotPres
    have hDisj := h₁Disj hNotPres
    have hFix : g₁ n k m (c₁ n k m hm) = c₁ n k m hm := g₁_fixes_c₁ hm
    have h_in_both := fixed_point_blocks_intersect (g₁ n k m) B (c₁ n k m hm) hC₁ hFix
    exact Set.disjoint_iff.mp hDisj h_in_both
  · by_contra hNotPres
    have hDisj := h₂Disj hNotPres
    have hFix : g₂ n k m (c₁ n k m hm) = c₁ n k m hm := g₂_fixes_c₁ hm
    have h_in_both := fixed_point_blocks_intersect (g₂ n k m) B (c₁ n k m hm) hC₁ hFix
    exact Set.disjoint_iff.mp hDisj h_in_both

-- ============================================
-- SECTION 6: CASE 1b IMPOSSIBILITY (k ≥ 1 and m ≥ 1)
-- ============================================

theorem case1b_impossible_g₃ (B : Set (Omega n k m))
    (hSupp₂ : ((g₂ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₃ n k m '' B) B) : False := by
  have h0_in_B : (⟨0, by omega⟩ : Omega n k m) ∈ B := hSupp₂ elem0_in_support_g₂
  have hFix : g₃ n k m (⟨0, by omega⟩ : Omega n k m) = ⟨0, by omega⟩ := g₃_fixes_elem0
  have h0_in_both := fixed_point_blocks_intersect (g₃ n k m) B _ h0_in_B hFix
  exact Set.disjoint_iff.mp hDisj h0_in_both

theorem case1b_impossible_g₁_from_g₂ (B : Set (Omega n k m))
    (hSupp₂ : ((g₂ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₁ n k m '' B) B) : False := by
  have h4_in_B : (⟨4, by omega⟩ : Omega n k m) ∈ B := hSupp₂ elem4_in_support_g₂
  have hFix : g₁ n k m (⟨4, by omega⟩ : Omega n k m) = ⟨4, by omega⟩ := g₁_fixes_elem4
  have h4_in_both := fixed_point_blocks_intersect (g₁ n k m) B _ h4_in_B hFix
  exact Set.disjoint_iff.mp hDisj h4_in_both

theorem case1b_impossible_g₁ (B : Set (Omega n k m))
    (hSupp₃ : ((g₃ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₁ n k m '' B) B) : False := by
  have h1_in_B : (⟨1, by omega⟩ : Omega n k m) ∈ B := hSupp₃ elem1_in_support_g₃
  have hFix : g₁ n k m (⟨1, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ := g₁_fixes_elem1
  have h1_in_both := fixed_point_blocks_intersect (g₁ n k m) B _ h1_in_B hFix
  exact Set.disjoint_iff.mp hDisj h1_in_both

theorem case1b_impossible_g₂_from_g₃ (B : Set (Omega n k m))
    (hSupp₃ : ((g₃ n k m).support : Set _) ⊆ B)
    (hDisj : Disjoint (g₂ n k m '' B) B) : False := by
  have h2_in_B : (⟨2, by omega⟩ : Omega n k m) ∈ B := hSupp₃ elem2_in_support_g₃
  have hFix : g₂ n k m (⟨2, by omega⟩ : Omega n k m) = ⟨2, by omega⟩ := g₂_fixes_elem2
  have h2_in_both := fixed_point_blocks_intersect (g₂ n k m) B _ h2_in_B hFix
  exact Set.disjoint_iff.mp hDisj h2_in_both
