/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_Defs
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_CycleSupport
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_OrbitContinuation
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_Case2

/-!
# Core Orbit Helper Lemmas

Basic lemmas about element mappings under g₁ and g₂.
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

namespace OrbitCore

/-- g₁²(0) = 3 (composition of g₁(0) = 5 and g₁(5) = 3) -/
theorem g₁_sq_elem0_eq_elem3 :
    g₁ n k m (g₁ n k m (⟨0, by omega⟩ : Omega n k m)) = ⟨3, by omega⟩ := by
  rw [g₁_elem0_eq_elem5, g₁_elem5_eq_elem3]

/-- Element 4 is not in tailA -/
theorem elem4_not_tailA : ¬isTailA (⟨4, by omega⟩ : Omega n k m) := by simp [isTailA]

/-- Element 1 is not in tailA (re-export for convenience) -/
theorem elem1_not_tailA' : ¬isTailA (⟨1, by omega⟩ : Omega n k m) := elem1_not_tailA

/-- g₁ fixes element 1 -/
theorem g₁_fixes_elem1' : g₁ n k m (⟨1, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ :=
  g₁_fixes_elem1

/-- g₁^j fixes element 1 for any natural j -/
theorem g₁_pow_fixes_elem1 (j : ℕ) :
    (g₁ n k m ^ j) (⟨1, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ := by
  induction j with
  | zero => simp
  | succ j' ih =>
    rw [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply, ih, g₁_fixes_elem1']

/-- g₂ maps 4 to 0 (element 4 is at index 2 in g₂CoreList = [1,3,4,0], next is 0) -/
theorem g₂_elem4_eq_elem0' :
    g₂ n k m (⟨4, by omega⟩ : Omega n k m) = ⟨0, by omega⟩ := by
  unfold g₂
  have hNodup := g₂_list_nodup n k m
  have h_len := g₂_cycle_length n k m
  have h_core_len : (g₂CoreList n k m).length = 4 := by simp [g₂CoreList]
  have h_2_lt : 2 < (g₂CoreList n k m ++ tailBList n k m).length := by rw [h_len]; omega
  have h_2_lt_core : 2 < (g₂CoreList n k m).length := by rw [h_core_len]; omega
  have h_idx : (g₂CoreList n k m ++ tailBList n k m)[2]'h_2_lt =
      (⟨4, by omega⟩ : Omega n k m) := by
    rw [List.getElem_append_left h_2_lt_core]
    simp [g₂CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 2 h_2_lt]
  simp only [h_len]
  have h_mod : (2 + 1) % (4 + k) = 3 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  have h_3_lt_core : 3 < (g₂CoreList n k m).length := by rw [h_core_len]; omega
  rw [List.getElem_append_left h_3_lt_core]
  simp [g₂CoreList]

/-- g₂ maps 1 to 3 (element 1 is at index 0, next is 3) -/
theorem g₂_elem1_eq_elem3 :
    g₂ n k m (⟨1, by omega⟩ : Omega n k m) = ⟨3, by omega⟩ := by
  unfold g₂
  have hNodup := g₂_list_nodup n k m
  have h_len := g₂_cycle_length n k m
  have h_core_len : (g₂CoreList n k m).length = 4 := by simp [g₂CoreList]
  have h_0_lt : 0 < (g₂CoreList n k m ++ tailBList n k m).length := by rw [h_len]; omega
  have h_idx : (g₂CoreList n k m ++ tailBList n k m)[0]'h_0_lt =
      (⟨1, by omega⟩ : Omega n k m) := by
    rw [List.getElem_append_left (by omega : 0 < (g₂CoreList n k m).length)]
    simp [g₂CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 0 h_0_lt]
  simp only [h_len]
  have h_mod : (0 + 1) % (4 + k) = 1 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  rw [List.getElem_append_left (by omega : 1 < (g₂CoreList n k m).length)]
  simp [g₂CoreList]

/-- g₂ maps 3 to 4 (element 3 is at index 1, next is 4) -/
theorem g₂_elem3_eq_elem4 :
    g₂ n k m (⟨3, by omega⟩ : Omega n k m) = ⟨4, by omega⟩ := by
  unfold g₂
  have hNodup := g₂_list_nodup n k m
  have h_len := g₂_cycle_length n k m
  have h_core_len : (g₂CoreList n k m).length = 4 := by simp [g₂CoreList]
  have h_1_lt : 1 < (g₂CoreList n k m ++ tailBList n k m).length := by rw [h_len]; omega
  have h_idx : (g₂CoreList n k m ++ tailBList n k m)[1]'h_1_lt =
      (⟨3, by omega⟩ : Omega n k m) := by
    rw [List.getElem_append_left (by omega : 1 < (g₂CoreList n k m).length)]
    simp [g₂CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 1 h_1_lt]
  simp only [h_len]
  have h_mod : (1 + 1) % (4 + k) = 2 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  rw [List.getElem_append_left (by omega : 2 < (g₂CoreList n k m).length)]
  simp [g₂CoreList]

/-- g₁² applied to element 0 gives element 3 -/
theorem g₁_pow2_elem0_eq_elem3 :
    (g₁ n k m ^ (2 : ℕ)) (⟨0, by omega⟩ : Omega n k m) = ⟨3, by omega⟩ := by
  simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
  exact g₁_sq_elem0_eq_elem3

/-- g₃ maps c₁ to c₂ (c₁ is at index 4 in cycle, next is c₂ at index 5). Requires m ≥ 2. -/
theorem g₃_c₁_eq_c₂ (hm : m ≥ 2) :
    g₃ n k m (⟨6 + n + k, by omega⟩ : Omega n k m) = ⟨6 + n + k + 1, by have := hm; omega⟩ := by
  unfold g₃
  have hNodup := g₃_list_nodup n k m
  have h_len := g₃_cycle_length n k m
  have h_core_len : (g₃CoreList n k m).length = 4 := by simp [g₃CoreList]
  have h_4_lt : 4 < (g₃CoreList n k m ++ tailCList n k m).length := by rw [h_len]; have := hm; omega
  have h_idx : (g₃CoreList n k m ++ tailCList n k m)[4]'h_4_lt =
      (⟨6 + n + k, by omega⟩ : Omega n k m) := by
    rw [List.getElem_append_right (by omega : 4 ≥ (g₃CoreList n k m).length)]
    simp only [h_core_len, Nat.sub_self, tailCList, List.getElem_map, List.getElem_finRange]
    rfl
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 4 h_4_lt]
  simp only [h_len]
  have h_mod : (4 + 1) % (4 + m) = 5 := Nat.mod_eq_of_lt (by have := hm; omega)
  simp only [h_mod]
  have h_5_lt : 5 < (g₃CoreList n k m ++ tailCList n k m).length := by rw [h_len]; have := hm; omega
  rw [List.getElem_append_right (by omega : 5 ≥ (g₃CoreList n k m).length)]
  simp only [h_core_len, tailCList, List.getElem_map, List.getElem_finRange]
  rfl

/-- g₃ maps c₂ to c₃ (c₂ is at index 5 in cycle, next is c₃ at index 6). Requires m ≥ 3. -/
theorem g₃_c₂_eq_c₃ (hm : m ≥ 3) :
    g₃ n k m (⟨6 + n + k + 1, by have := hm; omega⟩ : Omega n k m) =
    ⟨6 + n + k + 2, by have := hm; omega⟩ := by
  unfold g₃
  have hNodup := g₃_list_nodup n k m
  have h_len := g₃_cycle_length n k m
  have h_core_len : (g₃CoreList n k m).length = 4 := by simp [g₃CoreList]
  have h_5_lt : 5 < (g₃CoreList n k m ++ tailCList n k m).length := by rw [h_len]; have := hm; omega
  have h_idx : (g₃CoreList n k m ++ tailCList n k m)[5]'h_5_lt =
      (⟨6 + n + k + 1, by have := hm; omega⟩ : Omega n k m) := by
    rw [List.getElem_append_right (by omega : 5 ≥ (g₃CoreList n k m).length)]
    simp only [h_core_len, tailCList, List.getElem_map, List.getElem_finRange]
    rfl
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 5 h_5_lt]
  simp only [h_len]
  have h_mod : (5 + 1) % (4 + m) = 6 := Nat.mod_eq_of_lt (by have := hm; omega)
  simp only [h_mod]
  have h_6_lt : 6 < (g₃CoreList n k m ++ tailCList n k m).length := by rw [h_len]; have := hm; omega
  rw [List.getElem_append_right (by omega : 6 ≥ (g₃CoreList n k m).length)]
  simp only [h_core_len, tailCList, List.getElem_map, List.getElem_finRange]
  rfl

/-- g₃²(c₁) = c₃ for m ≥ 3 -/
theorem g₃_pow2_c₁_eq_c₃ (hm : m ≥ 3) :
    (g₃ n k m ^ (2 : ℕ)) (⟨6 + n + k, by omega⟩ : Omega n k m) =
    ⟨6 + n + k + 2, by have := hm; omega⟩ := by
  simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
  rw [g₃_c₁_eq_c₂ (by omega : m ≥ 2), g₃_c₂_eq_c₃ hm]

/-- g₃ maps c₂ to 2 when m = 2 (c₂ is at index 5 in cycle of length 6, wraps to 0).
    For m = 2: cycle is (2 4 5 1 c₁ c₂), so g₃(c₂) = 2. -/
theorem g₃_c₂_eq_elem2_m2 (hm : m = 2) :
    g₃ n k m (⟨6 + n + k + 1, by omega⟩ : Omega n k m) = ⟨2, by omega⟩ := by
  unfold g₃
  have hNodup := g₃_list_nodup n k m
  have h_len := g₃_cycle_length n k m
  have h_core_len : (g₃CoreList n k m).length = 4 := by simp [g₃CoreList]
  have h_5_lt : 5 < (g₃CoreList n k m ++ tailCList n k m).length := by rw [h_len, hm]; omega
  have h_idx : (g₃CoreList n k m ++ tailCList n k m)[5]'h_5_lt =
      (⟨6 + n + k + 1, by omega⟩ : Omega n k m) := by
    rw [List.getElem_append_right (by omega : 5 ≥ (g₃CoreList n k m).length)]
    simp only [h_core_len, tailCList, List.getElem_map, List.getElem_finRange]
    rfl
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 5 h_5_lt]
  simp only [h_len, hm]
  have h_mod : (5 + 1) % (4 + 2) = 0 := by native_decide
  simp only [h_mod]
  rw [List.getElem_append_left (by omega : 0 < (g₃CoreList n k m).length)]
  simp [g₃CoreList]

/-- g₃²(c₁) = 2 for m = 2. Combines g₃(c₁) = c₂ and g₃(c₂) = 2. -/
theorem g₃_pow2_c₁_eq_elem2 (hm : m = 2) :
    (g₃ n k m ^ (2 : ℕ)) (⟨6 + n + k, by omega⟩ : Omega n k m) = ⟨2, by omega⟩ := by
  simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
  rw [g₃_c₁_eq_c₂ (by omega : m ≥ 2), g₃_c₂_eq_elem2_m2 hm]

end OrbitCore
