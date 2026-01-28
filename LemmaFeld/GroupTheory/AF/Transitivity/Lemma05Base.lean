/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.Tactic.FinCases

/-!
# Lemma 5 Base Case: Transitivity of H₆ on Fin 6

The group H₆ = ⟨g₁, g₂, g₃⟩ with n=k=m=0 acts transitively on Fin 6.

## Main Results

* `H₆_isPretransitive` - H₆ acts transitively on Fin 6
-/

namespace LemmaFeld.GroupTheory.AF.Transitivity

open Equiv Equiv.Perm

/-! ### Generator Actions for Base Case

For the base case, H₆ acts transitively on Fin 6.
The generators are:
- g₁ = (0 5 3 2): 0→5→3→2→0
- g₂ = (1 3 4 0): 1→3→4→0→1, so 0→1
- g₃ = (2 4 5 1): 2→4→5→1→2
-/

/-- g₁(0) = 5 -/
theorem g₁_action_0 : (g₁ 0 0 0 : Perm (Fin 6)) 0 = 5 := by native_decide

/-- g₁(5) = 3 -/
theorem g₁_action_5 : (g₁ 0 0 0 : Perm (Fin 6)) 5 = 3 := by native_decide

/-- g₁(3) = 2 -/
theorem g₁_action_3 : (g₁ 0 0 0 : Perm (Fin 6)) 3 = 2 := by native_decide

/-- g₂(0) = 1 -/
theorem g₂_action_0 : (g₂ 0 0 0 : Perm (Fin 6)) 0 = 1 := by native_decide

/-- g₂(1) = 3 -/
theorem g₂_action_1 : (g₂ 0 0 0 : Perm (Fin 6)) 1 = 3 := by native_decide

/-- g₂(3) = 4 -/
theorem g₂_action_3 : (g₂ 0 0 0 : Perm (Fin 6)) 3 = 4 := by native_decide

/-! ### Reaching Each Element from 0 -/

/-- From 0, we can reach 1 using g₂ -/
theorem reach_1_from_0 : ∃ h : H₆, h.val 0 = 1 :=
  ⟨⟨g₂ 0 0 0, g₂_mem_H 0 0 0⟩, g₂_action_0⟩

/-- From 0, we can reach 5 using g₁ -/
theorem reach_5_from_0 : ∃ h : H₆, h.val 0 = 5 :=
  ⟨⟨g₁ 0 0 0, g₁_mem_H 0 0 0⟩, g₁_action_0⟩

/-- From 0, we can reach 3 using g₁² -/
theorem reach_3_from_0 : ∃ h : H₆, h.val 0 = 3 := by
  use ⟨(g₁ 0 0 0) ^ 2, Subgroup.pow_mem _ (g₁_mem_H 0 0 0) 2⟩
  native_decide

/-- From 0, we can reach 2 using g₁³ -/
theorem reach_2_from_0 : ∃ h : H₆, h.val 0 = 2 := by
  use ⟨(g₁ 0 0 0) ^ 3, Subgroup.pow_mem _ (g₁_mem_H 0 0 0) 3⟩
  native_decide

/-- From 0, we can reach 4 using g₂³ -/
theorem reach_4_from_0 : ∃ h : H₆, h.val 0 = 4 := by
  use ⟨(g₂ 0 0 0) ^ 3, Subgroup.pow_mem _ (g₂_mem_H 0 0 0) 3⟩
  native_decide

/-! ### Base Case Transitivity -/

/-- In the base case, every element of Fin 6 is reachable from 0 under H₆. -/
theorem H₆_orbit_of_zero : ∀ x : Fin 6, ∃ h : H₆, h.val 0 = x := by
  intro x
  fin_cases x
  · exact ⟨1, rfl⟩  -- 0: identity
  · exact reach_1_from_0
  · exact reach_2_from_0
  · exact reach_3_from_0
  · exact reach_4_from_0
  · exact reach_5_from_0

/-- For any two elements x, y in Fin 6, there exists h ∈ H₆ with h(x) = y -/
theorem H₆_orbit_exists (x y : Fin 6) : ∃ h : H₆, h.val x = y := by
  obtain ⟨h₁, hh₁⟩ := H₆_orbit_of_zero x
  obtain ⟨h₂, hh₂⟩ := H₆_orbit_of_zero y
  use h₂ * h₁⁻¹
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Perm.coe_mul]
  have hinv : h₁.val⁻¹ x = 0 := by rw [← hh₁]; simp only [Perm.inv_apply_self]
  simp only [Function.comp_apply, hinv, hh₂]

/-- The base case group H₆ acts transitively on Fin 6 -/
theorem H₆_isPretransitive : MulAction.IsPretransitive H₆ (Fin 6) := by
  constructor
  intro x y
  obtain ⟨h, hh⟩ := H₆_orbit_exists x y
  exact ⟨h, hh⟩

end LemmaFeld.GroupTheory.AF.Transitivity
