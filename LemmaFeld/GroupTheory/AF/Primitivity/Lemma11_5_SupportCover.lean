/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_Cases

/-!
# Lemma 11.5: Support Coverage

Proves that the supports of g₁, g₂, g₃ together cover all of Omega.

## Main Results

* `supports_cover_omega`: Every element of Ω is in at least one support
* `tailA_in_support_g₁`: Tail A elements are in supp(g₁)
* `tailB_in_support_g₂`: Tail B elements are in supp(g₂)
* `tailC_in_support_g₃`: Tail C elements are in supp(g₃)
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

-- ============================================
-- SECTION 1: TAIL ELEMENTS IN SUPPORTS
-- ============================================

/-- Tail A elements (indices 6 to 6+n-1) are in supp(g₁) -/
theorem tailA_in_support_g₁ (i : Fin n) :
    (⟨6 + i.val, by omega⟩ : Omega n k m) ∈ (g₁ n k m).support := by
  have hNodup := g₁_list_nodup n k m
  have hNotSingleton : ∀ x, g₁CoreList n k m ++ tailAList n k m ≠ [x] := by
    intro x h
    have : (g₁CoreList n k m ++ tailAList n k m).length = 1 := by rw [h]; simp
    have := g₁_cycle_length n k m
    omega
  rw [g₁, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, tailAList, List.mem_map, List.mem_finRange]
  right
  exact ⟨i, trivial, rfl⟩

/-- Tail B elements (indices 6+n to 6+n+k-1) are in supp(g₂) -/
theorem tailB_in_support_g₂ (i : Fin k) :
    (⟨6 + n + i.val, by omega⟩ : Omega n k m) ∈ (g₂ n k m).support := by
  have hNodup := g₂_list_nodup n k m
  have hNotSingleton : ∀ x, g₂CoreList n k m ++ tailBList n k m ≠ [x] := by
    intro x h
    have : (g₂CoreList n k m ++ tailBList n k m).length = 1 := by rw [h]; simp
    have := g₂_cycle_length n k m
    omega
  rw [g₂, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, tailBList, List.mem_map, List.mem_finRange]
  right
  exact ⟨i, trivial, rfl⟩

/-- Tail C elements (indices 6+n+k to 6+n+k+m-1) are in supp(g₃) -/
theorem tailC_in_support_g₃ (i : Fin m) :
    (⟨6 + n + k + i.val, by omega⟩ : Omega n k m) ∈ (g₃ n k m).support := by
  have hNodup := g₃_list_nodup n k m
  have hNotSingleton : ∀ x, g₃CoreList n k m ++ tailCList n k m ≠ [x] := by
    intro x h
    have : (g₃CoreList n k m ++ tailCList n k m).length = 1 := by rw [h]; simp
    have := g₃_cycle_length n k m
    omega
  rw [g₃, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, tailCList, List.mem_map, List.mem_finRange]
  right
  exact ⟨i, trivial, rfl⟩

-- ============================================
-- SECTION 2: CORE ELEMENTS IN SUPPORTS
-- ============================================

/-- Element 2 is in supp(g₃) -/
theorem elem2_in_support_g₃ :
    (⟨2, by omega⟩ : Omega n k m) ∈ (g₃ n k m).support := by
  have hNodup := g₃_list_nodup n k m
  have hNotSingleton : ∀ x, g₃CoreList n k m ++ tailCList n k m ≠ [x] := by
    intro x h
    have : (g₃CoreList n k m ++ tailCList n k m).length = 1 := by rw [h]; simp
    have := g₃_cycle_length n k m
    omega
  rw [g₃, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₃CoreList, List.mem_cons]
  tauto

/-- Element 4 is in supp(g₂) -/
theorem elem4_in_support_g₂ :
    (⟨4, by omega⟩ : Omega n k m) ∈ (g₂ n k m).support := by
  have hNodup := g₂_list_nodup n k m
  have hNotSingleton : ∀ x, g₂CoreList n k m ++ tailBList n k m ≠ [x] := by
    intro x h
    have : (g₂CoreList n k m ++ tailBList n k m).length = 1 := by rw [h]; simp
    have := g₂_cycle_length n k m
    omega
  rw [g₂, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₂CoreList, List.mem_cons]
  tauto

/-- Element 4 is in supp(g₃) -/
theorem elem4_in_support_g₃ :
    (⟨4, by omega⟩ : Omega n k m) ∈ (g₃ n k m).support := by
  have hNodup := g₃_list_nodup n k m
  have hNotSingleton : ∀ x, g₃CoreList n k m ++ tailCList n k m ≠ [x] := by
    intro x h
    have : (g₃CoreList n k m ++ tailCList n k m).length = 1 := by rw [h]; simp
    have := g₃_cycle_length n k m
    omega
  rw [g₃, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₃CoreList, List.mem_cons]
  tauto

/-- Element 5 is in supp(g₁) -/
theorem elem5_in_support_g₁ :
    (⟨5, by omega⟩ : Omega n k m) ∈ (g₁ n k m).support := by
  have hNodup := g₁_list_nodup n k m
  have hNotSingleton : ∀ x, g₁CoreList n k m ++ tailAList n k m ≠ [x] := by
    intro x h
    have : (g₁CoreList n k m ++ tailAList n k m).length = 1 := by rw [h]; simp
    have := g₁_cycle_length n k m
    omega
  rw [g₁, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₁CoreList, List.mem_cons]
  tauto

-- ============================================
-- SECTION 3: COMPLETE COVERAGE
-- ============================================

/-- Every element of Ω is in at least one of the three generator supports.
    This is the key lemma showing the supports cover Ω. -/
theorem supports_cover_omega (x : Omega n k m) :
    x ∈ (g₁ n k m).support ∨ x ∈ (g₂ n k m).support ∨ x ∈ (g₃ n k m).support := by
  -- Case split on the value of x
  obtain ⟨v, hv⟩ := x
  by_cases h6 : v < 6
  · -- Core element: v ∈ {0, 1, 2, 3, 4, 5}
    have : v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨ v = 4 ∨ v = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl | rfl
    · left; exact elem0_in_support_g₁
    · right; left; exact elem1_in_support_g₂
    · right; right; exact elem2_in_support_g₃
    · left; exact elem3_in_support_g₁
    · right; left; exact elem4_in_support_g₂
    · left; exact elem5_in_support_g₁
  · -- Tail element: v ≥ 6
    push_neg at h6
    by_cases hn : v < 6 + n
    · -- Tail A: 6 ≤ v < 6 + n
      left
      have hi : v - 6 < n := by omega
      convert tailA_in_support_g₁ (⟨v - 6, hi⟩ : Fin n) using 1
      simp only [Fin.ext_iff]
      omega
    · push_neg at hn
      by_cases hk : v < 6 + n + k
      · -- Tail B: 6 + n ≤ v < 6 + n + k
        right; left
        have hi : v - 6 - n < k := by omega
        convert tailB_in_support_g₂ (⟨v - 6 - n, hi⟩ : Fin k) using 1
        simp only [Fin.ext_iff]
        omega
      · -- Tail C: 6 + n + k ≤ v < 6 + n + k + m
        push_neg at hk
        right; right
        have hi : v - 6 - n - k < m := by omega
        convert tailC_in_support_g₃ (⟨v - 6 - n - k, hi⟩ : Fin m) using 1
        simp only [Fin.ext_iff]
        omega

/-- Corollary: If all supports are in B, then B = Ω -/
theorem case1a_i_supports_cover_univ (B : Set (Omega n k m))
    (h1 : ↑(g₁ n k m).support ⊆ B) (h2 : ↑(g₂ n k m).support ⊆ B)
    (h3 : ↑(g₃ n k m).support ⊆ B) : B = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  rcases supports_cover_omega x with hx | hx | hx
  · exact h1 hx
  · exact h2 hx
  · exact h3 hx
