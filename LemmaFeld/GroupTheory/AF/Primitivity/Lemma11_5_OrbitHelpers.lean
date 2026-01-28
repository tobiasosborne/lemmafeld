/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_OrbitHelpers_Core

/-!
# Orbit Helpers Aggregator

Re-exports helpers from Core, plus additional lemmas for orbit analysis.
-/

open Equiv Equiv.Perm Set OrbitCore

variable {n k m : ℕ}

/-- g₁^j fixes element 1 for integer j -/
theorem g₁_zpow_fixes_elem1 (j : ℤ) :
    (g₁ n k m ^ j) (⟨1, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ := by
  have hFix : g₁ n k m (⟨1, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ := g₁_fixes_elem1'
  exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hFix j

/-- Element outside supp(g₁) is either 1, 4, tailB, or tailC -/
theorem elem_not_in_support_g₁_cases (x : Omega n k m)
    (hx : x ∉ (g₁ n k m).support) :
    x.val = 1 ∨ x.val = 4 ∨ isTailB x ∨ isTailC x := by
  rcases Omega.partition x with hCore | hA | hB | hC
  · simp only [isCore] at hCore
    have hCases : x.val = 0 ∨ x.val = 1 ∨ x.val = 2 ∨ x.val = 3 ∨ x.val = 4 ∨ x.val = 5 :=
      by omega
    rcases hCases with h0 | h1 | h2 | h3 | h4 | h5
    · exfalso; have heq : x = ⟨0, by omega⟩ := Fin.ext h0
      rw [heq] at hx; exact hx elem0_in_support_g₁
    · left; exact h1
    · exfalso; have heq : x = ⟨2, by omega⟩ := Fin.ext h2
      rw [heq] at hx; exact hx elem2_in_support_g₁'
    · exfalso; have heq : x = ⟨3, by omega⟩ := Fin.ext h3
      rw [heq] at hx; exact hx elem3_in_support_g₁
    · right; left; exact h4
    · exfalso; have heq : x = ⟨5, by omega⟩ := Fin.ext h5
      rw [heq] at hx; exact hx elem5_in_support_g₁
  · exfalso
    simp only [isTailA] at hA
    have hi : x.val - 6 < n := by have := x.isLt; omega
    have hx_supp : x ∈ (g₁ n k m).support := by
      convert tailA_in_support_g₁ (⟨x.val - 6, hi⟩ : Fin n) using 1
      simp only [Fin.ext_iff]; omega
    exact hx hx_supp
  · right; right; left; exact hB
  · right; right; right; exact hC

/-- g₂ maps tailB elements to either tailB or element 1 (last tailB wraps) -/
theorem g₂_tailB_to_tailB_or_1 (x : Omega n k m) (hx : isTailB x) :
    isTailB (g₂ n k m x) ∨ g₂ n k m x = ⟨1, by omega⟩ := by
  simp only [isTailB] at hx ⊢
  -- x.val = 6 + n + i for some 0 ≤ i < k
  have hi : x.val - (6 + n) < k := by omega
  set i := x.val - (6 + n) with hi_def
  have hx_val : x.val = 6 + n + i := by omega
  have hx_eq : x = ⟨6 + n + i, by have := x.isLt; omega⟩ := Fin.ext hx_val
  unfold g₂
  have hnd := g₂_list_nodup n k m; have hlen := g₂_cycle_length n k m
  -- x is at index 4 + i in the g₂ cycle list
  have h_idx_lt : 4 + i < (g₂CoreList n k m ++ tailBList n k m).length := by rw [hlen]; omega
  have h_at_idx : (g₂CoreList n k m ++ tailBList n k m)[4 + i]'h_idx_lt = x := by
    rw [List.getElem_append_right (by simp [g₂CoreList] : 4 + i ≥ (g₂CoreList n k m).length)]
    simp only [g₂CoreList, tailBList, List.length_cons, List.length_nil,
      List.getElem_map, List.getElem_finRange, Fin.coe_cast]
    rw [hx_eq]; congr 1; omega
  rw [← h_at_idx, List.formPerm_apply_getElem _ hnd (4 + i) h_idx_lt]
  simp only [hlen]
  by_cases h_last : i = k - 1
  · -- Last tailB element: wraps to element 1
    right
    have hk_pos : k ≥ 1 := by omega
    have h_mod : (4 + i + 1) % (4 + k) = 0 := by
      have : 4 + i + 1 = 4 + k := by omega
      simp only [this, Nat.mod_self]
    simp only [h_mod]
    rw [List.getElem_append_left (by simp [g₂CoreList] : 0 < (g₂CoreList n k m).length)]
    simp [g₂CoreList]
  · -- Not last: next tailB element
    left
    have h_i_lt_k1 : i + 1 < k := by omega
    have h_mod : (4 + i + 1) % (4 + k) = 5 + i := by
      have h5i_lt : 5 + i < 4 + k := by omega
      have heq : 4 + i + 1 = 5 + i := by ring
      rw [heq]; exact Nat.mod_eq_of_lt h5i_lt
    simp only [h_mod]
    have h_next_lt : 5 + i < (g₂CoreList n k m ++ tailBList n k m).length := by rw [hlen]; omega
    rw [List.getElem_append_right (by simp [g₂CoreList]; omega : 5 + i ≥ (g₂CoreList n k m).length)]
    simp only [g₂CoreList, tailBList, List.length_cons, List.length_nil,
      List.getElem_map, List.getElem_finRange, Fin.coe_cast]
    constructor <;> omega

/-- g₂ applied to element outside supp(g₁) never gives 6 (needs n ≥ 1) -/
theorem g₂_image_not_6 (hn : n ≥ 1) (y : Omega n k m)
    (hy : y.val = 1 ∨ y.val = 4 ∨ isTailB y ∨ isTailC y) :
    (g₂ n k m y).val ≠ 6 := by
  rcases hy with h1 | h4 | hB | hC
  · have heq : y = ⟨1, by omega⟩ := Fin.ext h1
    rw [heq, g₂_elem1_eq_elem3]; simp
  · have heq : y = ⟨4, by omega⟩ := Fin.ext h4
    rw [heq, g₂_elem4_eq_elem0']; simp
  · rcases g₂_tailB_to_tailB_or_1 y hB with hB' | h1'
    · simp only [isTailB] at hB'; omega
    · rw [h1']; simp
  · have hFix := g₂_fixes_tailC y hC
    rw [hFix]; simp only [isTailC] at hC; omega

/-- g₁^j preserves tailC elements for integer j (since g₁ fixes tailC) -/
theorem g₁_zpow_fixes_tailC (j : ℤ) (x : Omega n k m) (hx : isTailC x) :
    (g₁ n k m ^ j) x = x := by
  have hFix : g₁ n k m x = x := g₁_fixes_tailC x hx
  exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hFix j

/-- g₁⁻²(0) is not in {1} ∪ tailB ∪ tailC (used for j≤-3 case) -/
theorem g₁_inv2_elem0_not_fixed_region :
    let x := (g₁ n k m ^ (2 : ℕ)).symm (⟨0, by omega⟩ : Omega n k m)
    x.val ≠ 1 ∧ ¬isTailB x ∧ ¬isTailC x := by
  -- Key: If y is fixed by g₁, then g₁²(y) = y, so y ≠ g₁⁻²(0) since g₁²(g₁⁻²(0)) = 0
  set x := (g₁ n k m ^ (2 : ℕ)).symm (⟨0, by omega⟩ : Omega n k m) with hx_def
  have hx_apply : (g₁ n k m ^ (2 : ℕ)) x = ⟨0, by omega⟩ :=
    (g₁ n k m ^ (2 : ℕ)).apply_symm_apply _
  constructor
  · -- x.val ≠ 1
    intro h
    have heq : x = ⟨1, by omega⟩ := Fin.ext h
    rw [heq] at hx_apply
    have h1_fixed : (g₁ n k m ^ (2 : ℕ)) (⟨1, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ := by
      simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
      rw [g₁_fixes_elem1', g₁_fixes_elem1']
    simp only [Fin.ext_iff] at hx_apply h1_fixed; omega
  constructor
  · -- ¬isTailB x
    intro hB
    have hB_fixed : (g₁ n k m ^ (2 : ℕ)) x = x := by
      simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
      rw [g₁_fixes_tailB _ hB, g₁_fixes_tailB _ hB]
    rw [hB_fixed] at hx_apply
    simp only [isTailB, Fin.ext_iff] at hB hx_apply; omega
  · -- ¬isTailC x
    intro hC
    have hC_fixed : (g₁ n k m ^ (2 : ℕ)) x = x := by
      simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
      rw [g₁_fixes_tailC _ hC, g₁_fixes_tailC _ hC]
    rw [hC_fixed] at hx_apply
    simp only [isTailC, Fin.ext_iff] at hC hx_apply; omega

-- ============================================
-- SECTION: g₂ element mappings for k ≥ 2 case
-- ============================================

/-- g₂(0) = 6+n (first tailB element) for k ≥ 1. Element 0 is at index 3 in g₂ cycle. -/
theorem g₂_elem0_eq_firstTailB (hk : k ≥ 1) :
    g₂ n k m ⟨0, by omega⟩ = ⟨6 + n, by omega⟩ := by
  unfold g₂
  have hnd := g₂_list_nodup n k m; have hlen := g₂_cycle_length n k m
  have h_3_lt : 3 < (g₂CoreList n k m ++ tailBList n k m).length := by rw [hlen]; omega
  have h_idx : (g₂CoreList n k m ++ tailBList n k m)[3]'h_3_lt = ⟨0, by omega⟩ := by
    rw [List.getElem_append_left (by simp [g₂CoreList] : 3 < (g₂CoreList n k m).length)]
    simp [g₂CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hnd 3 h_3_lt]
  simp only [hlen]
  have h_mod : (3 + 1) % (4 + k) = 4 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  have h_4_lt : 4 < (g₂CoreList n k m ++ tailBList n k m).length := by rw [hlen]; omega
  rw [List.getElem_append_right (by simp [g₂CoreList] : 4 ≥ (g₂CoreList n k m).length)]
  simp only [g₂CoreList, tailBList, List.length_cons, List.length_nil, List.length_map,
    List.length_finRange, Nat.add_zero, List.getElem_map, List.getElem_finRange]
  rfl

/-- g₂(6+n) = 6+n+1 (second tailB element) for k ≥ 2. -/
theorem g₂_firstTailB_eq_secondTailB (hk : k ≥ 2) :
    g₂ n k m ⟨6 + n, by omega⟩ = ⟨6 + n + 1, by omega⟩ := by
  unfold g₂
  have hnd := g₂_list_nodup n k m; have hlen := g₂_cycle_length n k m
  have h_4_lt : 4 < (g₂CoreList n k m ++ tailBList n k m).length := by rw [hlen]; omega
  have h_idx : (g₂CoreList n k m ++ tailBList n k m)[4]'h_4_lt = ⟨6 + n, by omega⟩ := by
    rw [List.getElem_append_right (by simp [g₂CoreList] : 4 ≥ (g₂CoreList n k m).length)]
    simp only [g₂CoreList, tailBList, List.length_cons, List.length_nil,
      List.getElem_map, List.getElem_finRange]
    rfl
  rw [← h_idx, List.formPerm_apply_getElem _ hnd 4 h_4_lt]
  simp only [hlen]
  have h_mod : (4 + 1) % (4 + k) = 5 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  have h_5_lt : 5 < (g₂CoreList n k m ++ tailBList n k m).length := by rw [hlen]; omega
  rw [List.getElem_append_right (by simp [g₂CoreList] : 5 ≥ (g₂CoreList n k m).length)]
  simp only [g₂CoreList, tailBList, List.length_cons, List.length_nil,
    List.getElem_map, List.getElem_finRange]
  rfl

/-- g₂²(0) = 6+n+1 for k ≥ 2. -/
theorem g₂_pow2_elem0_eq_secondTailB (hk : k ≥ 2) :
    (g₂ n k m ^ (2 : ℕ)) ⟨0, by omega⟩ = ⟨6 + n + 1, by omega⟩ := by
  simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
  rw [g₂_elem0_eq_firstTailB (by omega : k ≥ 1), g₂_firstTailB_eq_secondTailB hk]

/-- g₂²(3) = 0 (g₂(3) = 4, g₂(4) = 0). -/
theorem g₂_pow2_elem3_eq_elem0 :
    (g₂ n k m ^ (2 : ℕ)) ⟨3, by omega⟩ = ⟨0, by omega⟩ := by
  simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
  rw [g₂_elem3_eq_elem4, g₂_elem4_eq_elem0']

/-- For k ≥ 2, ∃ x ∈ {0, 3}, g₂²(x) ∉ {0, 3}. Witness: x = 0, g₂²(0) = 6+n+1 ≥ 7 > 3. -/
theorem set_0_3_not_g₂_closed (hk : k ≥ 2) :
    ∃ x : Omega n k m, x ∈ ({⟨0, by omega⟩, ⟨3, by omega⟩} : Set (Omega n k m)) ∧
      (g₂ n k m ^ (2 : ℕ)) x ∉ ({⟨0, by omega⟩, ⟨3, by omega⟩} : Set (Omega n k m)) := by
  use ⟨0, by omega⟩
  constructor
  · exact Set.mem_insert _ _
  · rw [g₂_pow2_elem0_eq_secondTailB hk]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff]; omega
