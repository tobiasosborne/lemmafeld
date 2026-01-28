/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Transitivity.Lemma05ListProps
import Mathlib.Tactic.FinCases

/-!
# Lemma 5: Generator Actions on Core Elements

For the general case with arbitrary n, k, m, the generators act on core elements {0,1,2,3,4,5}.

## Main Results

* `g₁_general_action_*` - g₁ actions on core elements
* `g₂_inv_general_action_*` - g₂⁻¹ actions on core elements
* `reach_from_0_general` - Reaching any core element from 0
* `core_connected` - Core vertices are connected in the support graph
-/

namespace LemmaFeld.GroupTheory.AF.Transitivity

open Equiv Equiv.Perm

/-! ### g₁ Actions on Core Elements -/

/-- g₁ maps 0 to 5 for any n, k, m -/
theorem g₁_general_action_0 (n k m : ℕ) :
    (g₁ n k m) (Fin.mk 0 (by omega)) = Fin.mk 5 (by omega) := by
  unfold g₁
  have hnd := g₁_list_nodup n k m
  have h0 : 0 < (g₁CoreList n k m ++ tailAList n k m).length := by simp [g₁CoreList, tailAList]
  have hlt : 0 + 1 < (g₁CoreList n k m ++ tailAList n k m).length := by simp [g₁CoreList, tailAList]
  conv_lhs => rw [← g₁_list_getElem_0 n k m h0]
  rw [List.formPerm_apply_lt_getElem _ hnd 0 hlt]
  exact g₁_list_getElem_1 n k m hlt

/-- g₁ maps 5 to 3 for any n, k, m -/
theorem g₁_general_action_5 (n k m : ℕ) :
    (g₁ n k m) (Fin.mk 5 (by omega)) = Fin.mk 3 (by omega) := by
  unfold g₁
  have hnd := g₁_list_nodup n k m
  have h1 : 1 < (g₁CoreList n k m ++ tailAList n k m).length := by simp [g₁CoreList, tailAList]
  have hlt : 1 + 1 < (g₁CoreList n k m ++ tailAList n k m).length := by simp [g₁CoreList, tailAList]
  conv_lhs => rw [← g₁_list_getElem_1 n k m h1]
  rw [List.formPerm_apply_lt_getElem _ hnd 1 hlt]
  exact g₁_list_getElem_2 n k m hlt

/-- g₁ maps 3 to 2 for any n, k, m -/
theorem g₁_general_action_3 (n k m : ℕ) :
    (g₁ n k m) (Fin.mk 3 (by omega)) = Fin.mk 2 (by omega) := by
  unfold g₁
  have hnd := g₁_list_nodup n k m
  have h2 : 2 < (g₁CoreList n k m ++ tailAList n k m).length := by simp [g₁CoreList, tailAList]
  have hlt : 2 + 1 < (g₁CoreList n k m ++ tailAList n k m).length := by simp [g₁CoreList, tailAList]
  conv_lhs => rw [← g₁_list_getElem_2 n k m h2]
  rw [List.formPerm_apply_lt_getElem _ hnd 2 hlt]
  exact g₁_list_getElem_3 n k m hlt

/-! ### g₂⁻¹ Actions on Core Elements -/

/-- g₂⁻¹ maps 0 to 4 for any n, k, m (since g₂ maps 4 to 0) -/
theorem g₂_inv_general_action_0 (n k m : ℕ) :
    (g₂ n k m)⁻¹ (Fin.mk 0 (by omega)) = Fin.mk 4 (by omega) := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  unfold g₂
  have hnd := g₂_list_nodup n k m
  have h2 : 2 < (g₂CoreList n k m ++ tailBList n k m).length := by simp [g₂CoreList, tailBList]
  have hlt : 2 + 1 < (g₂CoreList n k m ++ tailBList n k m).length := by simp [g₂CoreList, tailBList]
  conv_rhs => rw [← g₂_list_getElem_2 n k m h2]
  rw [List.formPerm_apply_lt_getElem _ hnd 2 hlt]
  exact g₂_list_getElem_3 n k m hlt

/-- g₂⁻¹ maps 4 to 3 for any n, k, m (since g₂ maps 3 to 4) -/
theorem g₂_inv_general_action_4 (n k m : ℕ) :
    (g₂ n k m)⁻¹ (Fin.mk 4 (by omega)) = Fin.mk 3 (by omega) := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  unfold g₂
  have hnd := g₂_list_nodup n k m
  have h1 : 1 < (g₂CoreList n k m ++ tailBList n k m).length := by simp [g₂CoreList, tailBList]
  have hlt : 1 + 1 < (g₂CoreList n k m ++ tailBList n k m).length := by simp [g₂CoreList, tailBList]
  conv_rhs => rw [← g₂_list_getElem_1 n k m h1]
  rw [List.formPerm_apply_lt_getElem _ hnd 1 hlt]
  exact g₂_list_getElem_2 n k m hlt

/-- g₂⁻¹ maps 3 to 1 for any n, k, m (since g₂ maps 1 to 3) -/
theorem g₂_inv_general_action_3 (n k m : ℕ) :
    (g₂ n k m)⁻¹ (Fin.mk 3 (by omega)) = Fin.mk 1 (by omega) := by
  rw [Equiv.Perm.inv_eq_iff_eq]
  unfold g₂
  have hnd := g₂_list_nodup n k m
  have h0 : 0 < (g₂CoreList n k m ++ tailBList n k m).length := by simp [g₂CoreList, tailBList]
  have hlt : 0 + 1 < (g₂CoreList n k m ++ tailBList n k m).length := by simp [g₂CoreList, tailBList]
  conv_rhs => rw [← g₂_list_getElem_0 n k m h0]
  rw [List.formPerm_apply_lt_getElem _ hnd 0 hlt]
  exact g₂_list_getElem_1 n k m hlt

/-! ### Reaching Core Elements from 0 -/

/-- From 0, reach any core element using g₁, g₂, g₂⁻¹ -/
theorem reach_from_0_general (n k m : ℕ) (x : Fin 6) :
    ∃ h : H n k m, h.val (Fin.mk 0 (by omega)) = Fin.mk x.val (by omega) := by
  fin_cases x
  · exact ⟨1, rfl⟩  -- x = 0: identity
  · -- x = 1: g₂⁻³(0)
    use ⟨(g₂ n k m)⁻¹ ^ 3, Subgroup.pow_mem _ (Subgroup.inv_mem _ (g₂_mem_H n k m)) 3⟩
    simp only [Equiv.Perm.coe_pow, Function.iterate_succ, Function.comp_apply,
      Function.iterate_zero, id_eq]
    rw [g₂_inv_general_action_0, g₂_inv_general_action_4, g₂_inv_general_action_3]
  · -- x = 2: g₁³(0)
    use ⟨(g₁ n k m) ^ 3, Subgroup.pow_mem _ (g₁_mem_H n k m) 3⟩
    simp only [Equiv.Perm.coe_pow, Function.iterate_succ, Function.comp_apply,
      Function.iterate_zero, id_eq]
    rw [g₁_general_action_0, g₁_general_action_5, g₁_general_action_3]
  · -- x = 3: g₁²(0)
    use ⟨(g₁ n k m) ^ 2, Subgroup.pow_mem _ (g₁_mem_H n k m) 2⟩
    simp only [Equiv.Perm.coe_pow, Function.iterate_succ, Function.comp_apply,
      Function.iterate_zero, id_eq]
    rw [g₁_general_action_0, g₁_general_action_5]
  · -- x = 4: g₂⁻¹(0)
    use ⟨(g₂ n k m)⁻¹, Subgroup.inv_mem _ (g₂_mem_H n k m)⟩
    exact g₂_inv_general_action_0 n k m
  · -- x = 5: g₁(0)
    use ⟨g₁ n k m, g₁_mem_H n k m⟩
    exact g₁_general_action_0 n k m

/-- The Core vertices {0,1,2,3,4,5} are connected in the support graph. -/
theorem core_connected (n k m : ℕ) :
    ∀ x y : Fin 6, ∃ h : H n k m, (h.val (Fin.castLE (by omega : 6 ≤ 6 + n + k + m) x) =
      Fin.castLE (by omega : 6 ≤ 6 + n + k + m) y) := by
  intro x y
  obtain ⟨h₁, hh₁⟩ := reach_from_0_general n k m x
  obtain ⟨h₂, hh₂⟩ := reach_from_0_general n k m y
  use h₂ * h₁⁻¹
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.coe_mul, Function.comp_apply]
  have hinv : h₁.val⁻¹ (Fin.mk x.val (by omega)) = Fin.mk 0 (by omega) := by
    rw [← hh₁]; simp only [Equiv.Perm.inv_apply_self]
  have hcast_x : Fin.castLE (by omega : 6 ≤ 6 + n + k + m) x = Fin.mk x.val (by omega) := rfl
  have hcast_y : Fin.castLE (by omega : 6 ≤ 6 + n + k + m) y = Fin.mk y.val (by omega) := rfl
  rw [hcast_x, hcast_y, hinv, hh₂]

end LemmaFeld.GroupTheory.AF.Transitivity
