/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Lemma 3 Helper: Explicit H₆ Elements

Provides an explicit enumeration of all 24 elements of H₆, verified computationally.
This establishes that H₆_subgroup_explicit = H₆ and has cardinality 24.
-/

namespace LemmaFeld.GroupTheory.AF.BaseCase

open Equiv Equiv.Perm

set_option linter.style.nativeDecide false

/-- All 24 elements of H₆ enumerated explicitly as a List -/
def H₆_list : List (Perm (Fin 6)) :=
  [1, c[0, 5, 3, 2], c[0, 1, 3, 4], c[1, 2, 4, 5], c[0, 2, 3, 5], c[0, 4, 3, 1],
   c[1, 5, 4, 2], c[0, 3] * c[2, 5], c[0, 1, 2] * c[3, 4, 5], c[0, 5, 1] * c[2, 4, 3],
   c[0, 4, 2] * c[1, 5, 3], c[0, 5, 4] * c[1, 3, 2], c[0, 3] * c[1, 4],
   c[0, 2, 4] * c[1, 3, 5], c[0, 1, 5] * c[2, 3, 4], c[1, 4] * c[2, 5],
   c[0, 4, 5] * c[1, 2, 3], c[0, 2, 1] * c[3, 5, 4], c[0, 1] * c[2, 5] * c[3, 4],
   c[0, 3] * c[1, 5] * c[2, 4], c[0, 4] * c[1, 3] * c[2, 5], c[0, 3] * c[1, 2] * c[4, 5],
   c[0, 2] * c[1, 4] * c[3, 5], c[0, 5] * c[1, 4] * c[2, 3]]

/-- Convert to Finset -/
def H₆_explicit : Finset (Perm (Fin 6)) := H₆_list.toFinset

/-- The explicit list has 24 distinct elements -/
theorem H₆_list_length : H₆_list.length = 24 := by native_decide

/-- The list has no duplicates -/
theorem H₆_list_nodup : H₆_list.Nodup := by native_decide

/-- The explicit set has exactly 24 elements -/
theorem H₆_explicit_card : H₆_explicit.card = 24 := by
  simp only [H₆_explicit, List.toFinset_card_of_nodup H₆_list_nodup, H₆_list_length]

/-- H₆_explicit is closed under multiplication -/
theorem H₆_explicit_mul_mem :
    ∀ a ∈ H₆_explicit, ∀ b ∈ H₆_explicit, a * b ∈ H₆_explicit := by native_decide

/-- The identity is in H₆_explicit -/
theorem H₆_explicit_one_mem : (1 : Perm (Fin 6)) ∈ H₆_explicit := by native_decide

/-- H₆_explicit is closed under inverse -/
theorem H₆_explicit_inv_mem : ∀ a ∈ H₆_explicit, a⁻¹ ∈ H₆_explicit := by native_decide

/-- H₆_explicit forms a subgroup -/
def H₆_subgroup_explicit : Subgroup (Perm (Fin 6)) where
  carrier := {g | g ∈ H₆_explicit}
  mul_mem' := fun ha hb => H₆_explicit_mul_mem _ ha _ hb
  one_mem' := H₆_explicit_one_mem
  inv_mem' := fun ha => H₆_explicit_inv_mem _ ha

/-- g₁ is in H₆_explicit -/
theorem g₁_in_explicit : g₁ 0 0 0 ∈ H₆_explicit := by native_decide

/-- g₂ is in H₆_explicit -/
theorem g₂_in_explicit : g₂ 0 0 0 ∈ H₆_explicit := by native_decide

/-- g₃ is in H₆_explicit -/
theorem g₃_in_explicit : g₃ 0 0 0 ∈ H₆_explicit := by native_decide

/-- The closure is contained in H₆_subgroup_explicit -/
theorem closure_le_explicit :
    Subgroup.closure {g₁ 0 0 0, g₂ 0 0 0, g₃ 0 0 0} ≤ H₆_subgroup_explicit := by
  rw [Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · exact g₁_in_explicit
  · exact g₂_in_explicit
  · exact g₃_in_explicit

-- Helper definitions for proving elements are in the closure
private def gensList : List (Perm (Fin 6)) :=
  [g₁ 0 0 0, g₂ 0 0 0, g₃ 0 0 0, (g₁ 0 0 0)⁻¹, (g₂ 0 0 0)⁻¹, (g₃ 0 0 0)⁻¹]

private def words2List : List (Perm (Fin 6)) :=
  gensList.flatMap (fun a => gensList.map (fun b => a * b))

private def words3List : List (Perm (Fin 6)) :=
  words2List.flatMap (fun ab => gensList.map (fun c => ab * c))

private lemma gensList_subset_closure :
    ∀ x ∈ gensList, x ∈ Subgroup.closure {g₁ 0 0 0, g₂ 0 0 0, g₃ 0 0 0} := by
  intro x hx
  simp only [gensList, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  · exact Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure (Set.mem_insert _ _))
  · exact Subgroup.inv_mem _
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))
  · exact Subgroup.inv_mem _ (Subgroup.subset_closure
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

private lemma words2List_subset_closure :
    ∀ x ∈ words2List, x ∈ Subgroup.closure {g₁ 0 0 0, g₂ 0 0 0, g₃ 0 0 0} := by
  intro x hx
  simp only [words2List, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  exact Subgroup.mul_mem _ (gensList_subset_closure a ha) (gensList_subset_closure b hb)

private lemma words3List_subset_closure :
    ∀ x ∈ words3List, x ∈ Subgroup.closure {g₁ 0 0 0, g₂ 0 0 0, g₃ 0 0 0} := by
  intro x hx
  simp only [words3List, List.mem_flatMap, List.mem_map] at hx
  obtain ⟨ab, hab, c, hc, rfl⟩ := hx
  exact Subgroup.mul_mem _ (words2List_subset_closure ab hab) (gensList_subset_closure c hc)

-- All H₆ elements are in word lists (verified computationally)
private lemma H₆_list_in_words : ∀ x ∈ H₆_list,
    x = 1 ∨ x ∈ gensList ∨ x ∈ words2List ∨ x ∈ words3List := by native_decide

/-- Every element in H₆_explicit is in the closure -/
theorem explicit_le_closure :
    H₆_subgroup_explicit ≤ Subgroup.closure {g₁ 0 0 0, g₂ 0 0 0, g₃ 0 0 0} := by
  intro x hx
  simp only [H₆_subgroup_explicit, H₆_explicit, List.mem_toFinset] at hx
  rcases H₆_list_in_words x hx with rfl | hgens | hwords2 | hwords3
  · exact Subgroup.one_mem _
  · exact gensList_subset_closure x hgens
  · exact words2List_subset_closure x hwords2
  · exact words3List_subset_closure x hwords3

/-- H₆_subgroup_explicit equals the closure -/
theorem explicit_eq_closure :
    H₆_subgroup_explicit = Subgroup.closure {g₁ 0 0 0, g₂ 0 0 0, g₃ 0 0 0} :=
  le_antisymm explicit_le_closure closure_le_explicit

/-- H₆ equals H₆_subgroup_explicit -/
theorem H₆_eq_explicit : H₆ = H₆_subgroup_explicit := by
  unfold H₆ H
  exact explicit_eq_closure.symm

end LemmaFeld.GroupTheory.AF.BaseCase
