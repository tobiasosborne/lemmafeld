/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_Defs
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_SupportCover
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_FixedPoints

/-!
# Lemma 11.5: Orbit Infrastructure

Infrastructure lemmas for the orbit-based arguments in Case 2 (n ≥ 3).

## Main Results

* `BlockSystemOn.orbit_subset_blocks`: σ^j(B) is a block when σ preserves blocks
* `g₂_fixes_in_supp_g₁_not_0_3`: CORRECT fixed-point lemma (g₂ fixes {2,5} ∪ tailA)
* `g₂_map_3_not_in_supp_g₁`: g₂(3) = 4 ∉ supp(g₁)
* `g₂_map_0_not_in_supp_g₁`: g₂(0) ∉ supp(g₁)

## Critical Support Intersection Facts

```
supp(g₁) = {0, 2, 3, 5} ∪ tailA
supp(g₂) = {0, 1, 3, 4} ∪ tailB
supp(g₁) ∩ supp(g₂) = {0, 3}  ← g₂ moves ONLY these in supp(g₁)
```

Therefore: x ∈ supp(g₁) ∧ x ≠ 0 ∧ x ≠ 3 → g₂(x) = x
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

-- ============================================
-- SECTION 1: ORBIT MEMBERSHIP IN BLOCK SYSTEM
-- ============================================

/-- If B ∈ BS.blocks and σ preserves the block system, then σ^j(B) ∈ BS.blocks -/
theorem BlockSystemOn.orbit_subset_blocks (BS : BlockSystemOn n k m)
    (σ : Perm (Omega n k m)) (hB : B ∈ BS.blocks)
    (hInv : BlockSystemInvariant σ BS.blocks)
    (B' : Set (Omega n k m)) (hB'_orbit : ∃ j : ℕ, B' = (σ ^ j) '' B) :
    B' ∈ BS.blocks := by
  obtain ⟨j, rfl⟩ := hB'_orbit
  induction j with
  | zero => simp only [pow_zero, Equiv.Perm.coe_one, Set.image_id]; exact hB
  | succ j ih =>
    rw [pow_succ', Equiv.Perm.coe_mul, Set.image_comp]
    exact hInv _ ih

-- ============================================
-- SECTION 2: ELEMENT 3 MAPPING (KEY LEMMA)
-- ============================================

/-- g₂(3) = 4 (computed from cycle structure)
    g₂CoreList = [1, 3, 4, 0], so 3 is at index 1, next is 4 at index 2 -/
theorem g₂_of_3 : g₂ n k m (⟨3, by omega⟩ : Omega n k m) = ⟨4, by omega⟩ := by
  unfold g₂
  have hNodup := g₂_list_nodup n k m
  have hLen := g₂_cycle_length n k m
  have h_core_len : (g₂CoreList n k m).length = 4 := by simp [g₂CoreList]
  -- 3 is at index 1 in g₂CoreList = [1, 3, 4, 0]
  have h_1_lt : 1 < (g₂CoreList n k m ++ tailBList n k m).length := by rw [hLen]; omega
  have h_idx : (g₂CoreList n k m ++ tailBList n k m)[1]'h_1_lt =
      (⟨3, by omega⟩ : Omega n k m) := by
    rw [List.getElem_append_left (by omega : 1 < (g₂CoreList n k m).length)]
    simp [g₂CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 1 h_1_lt]
  simp only [hLen]
  have h_mod : (1 + 1) % (4 + k) = 2 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  rw [List.getElem_append_left (by omega : 2 < (g₂CoreList n k m).length)]
  simp [g₂CoreList]

/-- 4 is NOT in supp(g₁) -/
theorem elem4_not_in_support_g₁' :
    (⟨4, by omega⟩ : Omega n k m) ∉ (g₁ n k m).support := by
  simp only [g₁, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h
  simp only [List.mem_append, g₁CoreList, tailAList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h
    all_goals simp only [Fin.ext_iff] at h; omega
  · obtain ⟨j, _, hj⟩ := h
    simp only [Fin.ext_iff] at hj; omega

/-- g₂(3) is NOT in supp(g₁) -/
theorem g₂_map_3_not_in_supp_g₁ :
    g₂ n k m (⟨3, by omega⟩ : Omega n k m) ∉ (g₁ n k m).support := by
  rw [g₂_of_3]
  exact elem4_not_in_support_g₁'

-- ============================================
-- SECTION 3: ELEMENT 0 MAPPING
-- ============================================

/-- 1 is NOT in supp(g₁) -/
theorem elem1_not_in_support_g₁' :
    (⟨1, by omega⟩ : Omega n k m) ∉ (g₁ n k m).support := by
  simp only [g₁, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h
  simp only [List.mem_append, g₁CoreList, tailAList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h
    all_goals simp only [Fin.ext_iff] at h; omega
  · obtain ⟨j, _, hj⟩ := h
    simp only [Fin.ext_iff] at hj; omega

/-- First tailB element is NOT in supp(g₁) -/
theorem tailB_elem_not_in_support_g₁ (hk : k ≥ 1) :
    (⟨6 + n, by omega⟩ : Omega n k m) ∉ (g₁ n k m).support := by
  simp only [g₁, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_notMem
  intro h
  simp only [List.mem_append, g₁CoreList, tailAList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h
    all_goals simp only [Fin.ext_iff] at h; omega
  · obtain ⟨j, _, hj⟩ := h
    simp only [Fin.ext_iff] at hj
    have := j.isLt; omega

/-- g₂(0) ∉ supp(g₁)
    g₂CoreList = [1, 3, 4, 0], so 0 is at index 3
    - If k = 0: g₂(0) = 1 (wraps to index 0)
    - If k ≥ 1: g₂(0) = first tailB element = 6+n -/
theorem g₂_map_0_not_in_supp_g₁ :
    g₂ n k m (⟨0, by omega⟩ : Omega n k m) ∉ (g₁ n k m).support := by
  unfold g₂
  have hNodup := g₂_list_nodup n k m
  have hLen := g₂_cycle_length n k m
  have h_core_len : (g₂CoreList n k m).length = 4 := by simp [g₂CoreList]
  -- 0 is at index 3 in g₂CoreList = [1, 3, 4, 0]
  have h_3_lt : 3 < (g₂CoreList n k m ++ tailBList n k m).length := by rw [hLen]; omega
  have h_idx : (g₂CoreList n k m ++ tailBList n k m)[3]'h_3_lt =
      (⟨0, by omega⟩ : Omega n k m) := by
    rw [List.getElem_append_left (by omega : 3 < (g₂CoreList n k m).length)]
    simp [g₂CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 3 h_3_lt]
  simp only [hLen]
  by_cases hk : k = 0
  · -- k = 0: g₂(0) = element at index (3+1) % 4 = 0, which is 1
    subst hk
    simp only [add_zero]
    have h_mod : (3 + 1) % 4 = 0 := by omega
    simp only [h_mod]
    rw [List.getElem_append_left (by omega : 0 < (g₂CoreList n 0 m).length)]
    simp only [g₂CoreList, List.getElem_cons_zero]
    exact elem1_not_in_support_g₁'
  · -- k ≥ 1: g₂(0) = first element of tailB = ⟨6+n, ...⟩
    have hk' : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
    have h_mod : (3 + 1) % (4 + k) = 4 := Nat.mod_eq_of_lt (by omega : 4 < 4 + k)
    simp only [h_mod]
    rw [List.getElem_append_right (by decide : 4 ≥ 4)]
    simp only [g₂CoreList, List.length_cons, List.length_nil]
    simp only [tailBList, List.getElem_map, List.getElem_finRange]
    exact tailB_elem_not_in_support_g₁ hk'

-- ============================================
-- SECTION 4: CORRECT FIXED-POINT LEMMA
-- ============================================

/-- Element 0 is NOT in supp(g₂) complement within supp(g₁) -/
theorem elem0_in_support_g₂' :
    (⟨0, by omega⟩ : Omega n k m) ∈ (g₂ n k m).support := elem0_in_support_g₂

/-- Element 3 is in supp(g₂) -/
theorem elem3_in_support_g₂ :
    (⟨3, by omega⟩ : Omega n k m) ∈ (g₂ n k m).support := by
  have hNodup := g₂_list_nodup n k m
  have hNotSingleton : ∀ x, g₂CoreList n k m ++ tailBList n k m ≠ [x] := by
    intro x h
    have : (g₂CoreList n k m ++ tailBList n k m).length = 1 := by rw [h]; simp
    have := g₂_cycle_length n k m; omega
  rw [g₂, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₂CoreList, List.mem_cons]; tauto

/-- CORRECT: Elements in supp(g₁) that are NOT 0 or 3 are fixed by g₂.

    supp(g₁) ∩ supp(g₂) = {0, 3}, so g₂ fixes supp(g₁) \ {0, 3} = {2, 5} ∪ tailA -/
theorem g₂_fixes_in_supp_g₁_not_0_3 (x : Omega n k m)
    (hx_supp : x ∈ (g₁ n k m).support)
    (hx_ne_0 : x ≠ ⟨0, by omega⟩)
    (hx_ne_3 : x ≠ ⟨3, by omega⟩) :
    g₂ n k m x = x := by
  -- x ∈ supp(g₁) = {0, 2, 3, 5} ∪ tailA
  -- x ≠ 0 and x ≠ 3, so x ∈ {2, 5} ∪ tailA
  -- {2, 5} ∪ tailA is disjoint from supp(g₂) = {0, 1, 3, 4} ∪ tailB
  -- Therefore x ∉ supp(g₂), so g₂(x) = x
  apply fixed_outside_support
  intro hx_in_g₂
  -- Show x ∉ supp(g₂) by case analysis
  have hNodup₁ := g₁_list_nodup n k m
  have hNotSingleton₁ : ∀ y, g₁CoreList n k m ++ tailAList n k m ≠ [y] := by
    intro y h; have : (g₁CoreList n k m ++ tailAList n k m).length = 1 := by rw [h]; simp
    have := g₁_cycle_length n k m; omega
  rw [g₁, List.support_formPerm_of_nodup _ hNodup₁ hNotSingleton₁] at hx_supp
  simp only [List.mem_toFinset, List.mem_append, g₁CoreList, tailAList,
    List.mem_cons, List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at hx_supp
  have hNodup₂ := g₂_list_nodup n k m
  have hNotSingleton₂ : ∀ y, g₂CoreList n k m ++ tailBList n k m ≠ [y] := by
    intro y h; have : (g₂CoreList n k m ++ tailBList n k m).length = 1 := by rw [h]; simp
    have := g₂_cycle_length n k m; omega
  rw [g₂, List.support_formPerm_of_nodup _ hNodup₂ hNotSingleton₂] at hx_in_g₂
  simp only [List.mem_toFinset, List.mem_append, g₂CoreList, tailBList,
    List.mem_cons, List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at hx_in_g₂
  -- x ∈ supp(g₁) means x ∈ {0, 5, 3, 2} ∪ tailA
  -- x ∈ supp(g₂) means x ∈ {1, 3, 4, 0} ∪ tailB
  rcases hx_supp with hCore | hTailA
  · -- x is a core element of g₁: x ∈ {0, 5, 3, 2}
    rcases hCore with rfl | rfl | rfl | rfl
    · exact hx_ne_0 rfl  -- x = 0, contradiction
    · -- x = 5. Check 5 ∉ supp(g₂)
      rcases hx_in_g₂ with hCore₂ | hTailB₂
      · rcases hCore₂ with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
      · obtain ⟨j, _, hj⟩ := hTailB₂; simp only [Fin.ext_iff] at hj; omega
    · exact hx_ne_3 rfl  -- x = 3, contradiction
    · -- x = 2. Check 2 ∉ supp(g₂)
      rcases hx_in_g₂ with hCore₂ | hTailB₂
      · rcases hCore₂ with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
      · obtain ⟨j, _, hj⟩ := hTailB₂; simp only [Fin.ext_iff] at hj; omega
  · -- x is in tailA: x = ⟨6 + i, ...⟩ for some i < n
    obtain ⟨i, _, hi⟩ := hTailA
    rw [← hi] at hx_in_g₂
    rcases hx_in_g₂ with hCore₂ | hTailB₂
    · rcases hCore₂ with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
    · obtain ⟨j, _, hj⟩ := hTailB₂
      simp only [Fin.ext_iff] at hj
      have := i.isLt; have := j.isLt; omega

-- ============================================
-- SECTION 5: KEY INSIGHT FOR n ≥ 3 CASE
-- ============================================

/-!
## Why {0, 3} Cannot Be a Block

The key insight for the n ≥ 3 case is that {0, 3} cannot be a valid block for g₁.

Computation:
- g₁(0) = 5, g₁(5) = 3, so g₁²(0) = 3
- g₁(3) = 2, g₁(2) = a₁ = 6, so g₁²(3) = 6

Therefore g₁²({0, 3}) = {3, 6}, which:
- Intersects {0, 3} at element 3
- Is not equal to {0, 3} (since 6 ≠ 0)

This violates the block property: for a valid block B, g^j(B) must be either
equal to B or disjoint from B for all j.

Consequence: Any block B' containing 0 must also contain some element y ≠ 3.
Since y ∈ supp(g₁) \ {0, 3} = {2, 5} ∪ tailA, we have g₂(y) = y (g₂-fixed).
This gives the contradiction in the n ≥ 3 proof.
-/

-- ============================================
-- SECTION 6: {0, 3} NOT A VALID g₁-BLOCK
-- ============================================

/-- g₁(3) = 2 (inline proof for use in set_0_3_not_g₁_closed) -/
private theorem g₁_of_3_eq_2 : g₁ n k m (⟨3, by omega⟩ : Omega n k m) = ⟨2, by omega⟩ := by
  unfold g₁
  have hNodup := g₁_list_nodup n k m
  have h_len := g₁_cycle_length n k m
  have h_2_lt : 2 < (g₁CoreList n k m ++ tailAList n k m).length := by rw [h_len]; omega
  have h_idx : (g₁CoreList n k m ++ tailAList n k m)[2]'h_2_lt =
      (⟨3, by omega⟩ : Omega n k m) := by simp [g₁CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 2 h_2_lt]
  simp only [h_len]
  have h_mod : (2 + 1) % (4 + n) = 3 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  rw [List.getElem_append_left (by simp [g₁CoreList] : 3 < (g₁CoreList n k m).length)]
  simp [g₁CoreList]

/-- g₁(2) = 6 (first tailA element) when n ≥ 1 (inline proof) -/
private theorem g₁_of_2_eq_6 (hn : n ≥ 1) :
    g₁ n k m (⟨2, by omega⟩ : Omega n k m) = ⟨6, by omega⟩ := by
  unfold g₁
  have hNodup := g₁_list_nodup n k m
  have h_len := g₁_cycle_length n k m
  have h_3_lt : 3 < (g₁CoreList n k m ++ tailAList n k m).length := by rw [h_len]; omega
  have h_idx : (g₁CoreList n k m ++ tailAList n k m)[3]'h_3_lt =
      (⟨2, by omega⟩ : Omega n k m) := by simp [g₁CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 3 h_3_lt]
  simp only [h_len]
  have h_mod : (3 + 1) % (4 + n) = 4 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  have h_core_len : (g₁CoreList n k m).length = 4 := by simp [g₁CoreList]
  rw [List.getElem_append_right (by rw [h_core_len] : (g₁CoreList n k m).length ≤ 4)]
  simp only [h_core_len, tailAList, List.getElem_map, List.getElem_finRange, Nat.sub_self]
  simp only [Fin.coe_cast, Fin.val_mk, add_zero]

/-- {0, 3} is not closed under g₁²: g₁²(3) = 6 ∉ {0, 3} when n ≥ 1.

    This means {0, 3} cannot be a valid block for g₁, since blocks must satisfy:
    for all j, g₁ʲ(B) is either equal to B or disjoint from B. -/
theorem set_0_3_not_g₁_closed (hn : n ≥ 1) :
    ∃ x : Omega n k m, x ∈ ({⟨0, by omega⟩, ⟨3, by omega⟩} : Set (Omega n k m)) ∧
      g₁ n k m (g₁ n k m x) ∉ ({⟨0, by omega⟩, ⟨3, by omega⟩} : Set (Omega n k m)) := by
  use ⟨3, by omega⟩
  constructor
  · exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  · rw [g₁_of_3_eq_2, g₁_of_2_eq_6 hn]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Fin.ext_iff]
    omega

