/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_2
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_FixedPoints
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Lemma 11.5: Cycle Support Lemmas

Helper lemmas showing which elements are in the supports of g₁, g₂, g₃,
and which generators fix which elements.

## Main Results

* `g₂_isCycle`, `g₃_isCycle`: The generators are cycles
* `elem0_in_support_g₁`, `elem0_in_support_g₂`: Element membership in supports
* `elem0_not_in_support_g₃`, `elem3_not_in_support_g₃`: Elements outside g₃'s support
* `g₃_fixes_elem0`, `g₃_fixes_elem3`: Fixed point lemmas
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

-- ============================================
-- SECTION 1: CYCLE PROPERTIES
-- ============================================

/-- g₂ is a cycle -/
theorem g₂_isCycle (n k m : ℕ) : (g₂ n k m).IsCycle := by
  unfold g₂
  apply List.isCycle_formPerm
  · exact g₂_list_nodup n k m
  · have := g₂_cycle_length n k m; simp only [List.length_append] at this ⊢; omega

/-- g₃ is a cycle -/
theorem g₃_isCycle (n k m : ℕ) : (g₃ n k m).IsCycle := by
  unfold g₃
  apply List.isCycle_formPerm
  · exact g₃_list_nodup n k m
  · have := g₃_cycle_length n k m; simp only [List.length_append] at this ⊢; omega

-- ============================================
-- SECTION 2: ELEMENT SUPPORT MEMBERSHIP
-- ============================================

/-- Element 0 is in supp(g₂) (it's the first element of the g₂ cycle) -/
theorem elem0_in_support_g₂ :
    (⟨0, by omega⟩ : Omega n k m) ∈ (g₂ n k m).support := by
  have hNodup := g₂_list_nodup n k m
  have hNotSingleton : ∀ x, g₂CoreList n k m ++ tailBList n k m ≠ [x] := by
    intro x h
    have : (g₂CoreList n k m ++ tailBList n k m).length = 1 := by rw [h]; simp
    have := g₂_cycle_length n k m
    omega
  rw [g₂, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₂CoreList, List.mem_cons]
  tauto

/-- Element 1 is in supp(g₂) -/
theorem elem1_in_support_g₂ :
    (⟨1, by omega⟩ : Omega n k m) ∈ (g₂ n k m).support := by
  have hNodup := g₂_list_nodup n k m
  have hNotSingleton : ∀ x, g₂CoreList n k m ++ tailBList n k m ≠ [x] := by
    intro x h
    have : (g₂CoreList n k m ++ tailBList n k m).length = 1 := by rw [h]; simp
    have := g₂_cycle_length n k m
    omega
  rw [g₂, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₂CoreList, List.mem_cons]
  tauto

/-- Element 1 is in supp(g₃) -/
theorem elem1_in_support_g₃ :
    (⟨1, by omega⟩ : Omega n k m) ∈ (g₃ n k m).support := by
  have hNodup := g₃_list_nodup n k m
  have hNotSingleton : ∀ x, g₃CoreList n k m ++ tailCList n k m ≠ [x] := by
    intro x h
    have : (g₃CoreList n k m ++ tailCList n k m).length = 1 := by rw [h]; simp
    have := g₃_cycle_length n k m
    omega
  rw [g₃, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₃CoreList, List.mem_cons]
  tauto

/-- Element 0 is in supp(g₁) -/
theorem elem0_in_support_g₁ :
    (⟨0, by omega⟩ : Omega n k m) ∈ (g₁ n k m).support := by
  have hNodup := g₁_list_nodup n k m
  have hNotSingleton : ∀ x, g₁CoreList n k m ++ tailAList n k m ≠ [x] := by
    intro x h
    have : (g₁CoreList n k m ++ tailAList n k m).length = 1 := by rw [h]; simp
    have := g₁_cycle_length n k m
    omega
  rw [g₁, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₁CoreList, List.mem_cons]
  tauto

/-- Element 3 is in supp(g₁) -/
theorem elem3_in_support_g₁ :
    (⟨3, by omega⟩ : Omega n k m) ∈ (g₁ n k m).support := by
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
-- SECTION 3: ELEMENTS NOT IN g₃ SUPPORT
-- ============================================

/-- Element 0 is NOT in supp(g₃) -/
theorem elem0_not_in_support_g₃ :
    (⟨0, by omega⟩ : Omega n k m) ∉ (g₃ n k m).support := by
  simp only [g₃, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h
  simp only [List.mem_append, g₃CoreList, tailCList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h
    all_goals simp only [Fin.ext_iff] at h; omega
  · obtain ⟨j, _, hj⟩ := h
    simp only [Fin.ext_iff] at hj
    omega

/-- g₃ fixes element 0 -/
theorem g₃_fixes_elem0 :
    g₃ n k m (⟨0, by omega⟩ : Omega n k m) = ⟨0, by omega⟩ := by
  exact fixed_outside_support _ _ elem0_not_in_support_g₃

/-- Element 3 is NOT in supp(g₃) -/
theorem elem3_not_in_support_g₃ :
    (⟨3, by omega⟩ : Omega n k m) ∉ (g₃ n k m).support := by
  simp only [g₃, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h
  simp only [List.mem_append, g₃CoreList, tailCList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h
    all_goals simp only [Fin.ext_iff] at h; omega
  · obtain ⟨j, _, hj⟩ := h
    simp only [Fin.ext_iff] at hj
    omega

/-- g₃ fixes element 3 -/
theorem g₃_fixes_elem3 :
    g₃ n k m (⟨3, by omega⟩ : Omega n k m) = ⟨3, by omega⟩ := by
  exact fixed_outside_support _ _ elem3_not_in_support_g₃

-- ============================================
-- SECTION 4: g₃ ELEMENT MAPPINGS
-- ============================================

/-- g₃ maps 2 to 4 (element 2 is at index 0 in g₃CoreList = [2,4,5,1], next is 4) -/
theorem g₃_elem2_eq_elem4 :
    g₃ n k m (⟨2, by omega⟩ : Omega n k m) = ⟨4, by omega⟩ := by
  unfold g₃
  have hNodup := g₃_list_nodup n k m
  have h_len := g₃_cycle_length n k m
  have h_core_len : (g₃CoreList n k m).length = 4 := by simp [g₃CoreList]
  have h_0_lt : 0 < (g₃CoreList n k m ++ tailCList n k m).length := by rw [h_len]; omega
  have h_idx : (g₃CoreList n k m ++ tailCList n k m)[0]'h_0_lt =
      (⟨2, by omega⟩ : Omega n k m) := by
    rw [List.getElem_append_left (by omega : 0 < (g₃CoreList n k m).length)]
    simp [g₃CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 0 h_0_lt]
  simp only [h_len]
  have h_mod : (0 + 1) % (4 + m) = 1 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  rw [List.getElem_append_left (by omega : 1 < (g₃CoreList n k m).length)]
  simp [g₃CoreList]

/-- g₃ maps 4 to 5 (element 4 is at index 1, next is 5) -/
theorem g₃_elem4_eq_elem5 :
    g₃ n k m (⟨4, by omega⟩ : Omega n k m) = ⟨5, by omega⟩ := by
  unfold g₃
  have hNodup := g₃_list_nodup n k m
  have h_len := g₃_cycle_length n k m
  have h_core_len : (g₃CoreList n k m).length = 4 := by simp [g₃CoreList]
  have h_1_lt : 1 < (g₃CoreList n k m ++ tailCList n k m).length := by rw [h_len]; omega
  have h_idx : (g₃CoreList n k m ++ tailCList n k m)[1]'h_1_lt =
      (⟨4, by omega⟩ : Omega n k m) := by
    rw [List.getElem_append_left (by omega : 1 < (g₃CoreList n k m).length)]
    simp [g₃CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 1 h_1_lt]
  simp only [h_len]
  have h_mod : (1 + 1) % (4 + m) = 2 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  rw [List.getElem_append_left (by omega : 2 < (g₃CoreList n k m).length)]
  simp [g₃CoreList]

/-- g₃ maps 5 to 1 (element 5 is at index 2, next is 1) -/
theorem g₃_elem5_eq_elem1 :
    g₃ n k m (⟨5, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ := by
  unfold g₃
  have hNodup := g₃_list_nodup n k m
  have h_len := g₃_cycle_length n k m
  have h_core_len : (g₃CoreList n k m).length = 4 := by simp [g₃CoreList]
  have h_2_lt : 2 < (g₃CoreList n k m ++ tailCList n k m).length := by rw [h_len]; omega
  have h_idx : (g₃CoreList n k m ++ tailCList n k m)[2]'h_2_lt =
      (⟨5, by omega⟩ : Omega n k m) := by
    rw [List.getElem_append_left (by omega : 2 < (g₃CoreList n k m).length)]
    simp [g₃CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 2 h_2_lt]
  simp only [h_len]
  have h_mod : (2 + 1) % (4 + m) = 3 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  rw [List.getElem_append_left (by omega : 3 < (g₃CoreList n k m).length)]
  simp [g₃CoreList]
