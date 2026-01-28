/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.BaseCase.Lemma01
import LemmaFeld.GroupTheory.AF.BaseCase.Lemma02
import LemmaFeld.GroupTheory.AF.BaseCase.Lemma03_Explicit
import LemmaFeld.GroupTheory.AF.BaseCase.Lemma03_IsoS4
import Mathlib.GroupTheory.Perm.Subgroup
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! # Lemma 3: H₆ ≅ S₄ with |H₆| = 24, acting imprimitively on {1,...,6} -/

namespace LemmaFeld.GroupTheory.AF.BaseCase

open Equiv Equiv.Perm

/-- Kernel elements: V₄ = {id, (0 3)(1 4), (0 3)(2 5), (1 4)(2 5)} -/
def kernelElements : Finset (Perm (Fin 6)) :=
  { 1, swap (0 : Fin 6) 3 * swap 1 4, swap (0 : Fin 6) 3 * swap 2 5, swap (1 : Fin 6) 4 * swap 2 5 }

theorem kernelElements_card : kernelElements.card = 4 := by native_decide

theorem one_preserves_B₀ : ∀ B ∈ B₀, B.image (1 : Perm (Fin 6)) ∈ B₀ := by
  intro B hB; convert hB using 1; ext x
  simp only [Finset.mem_image, coe_one, id_eq, exists_eq_right]

theorem inv_preserves_B₀ (g : Perm (Fin 6)) (hg : ∀ B ∈ B₀, B.image g ∈ B₀) :
    ∀ B ∈ B₀, B.image (g⁻¹ : Perm (Fin 6)) ∈ B₀ := by
  intro B hB
  have maps : Set.MapsTo (Finset.image g) B₀ B₀ := fun B hB => hg B hB
  have inj : Set.InjOn (Finset.image g) B₀ := by
    intro B₁ hB₁ B₂ hB₂ heq; ext x; constructor
    · intro hx; have h1 := Finset.mem_image_of_mem g hx; rw [heq] at h1
      obtain ⟨y, hy, heq'⟩ := Finset.mem_image.mp h1; exact g.injective heq' ▸ hy
    · intro hx; have h2 := Finset.mem_image_of_mem g hx; rw [← heq] at h2
      obtain ⟨y, hy, heq'⟩ := Finset.mem_image.mp h2; exact g.injective heq' ▸ hy
  have surj : Set.SurjOn (Finset.image g) B₀ B₀ :=
    Finset.surjOn_of_injOn_of_card_le _ maps inj (le_refl _)
  obtain ⟨B', hB', heq⟩ := surj hB
  convert hB' using 1; rw [← heq]; ext x; simp only [Finset.mem_image, coe_inv]
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩; simp only [symm_apply_apply]; exact hz
  · intro hx; exact ⟨g x, ⟨x, hx, rfl⟩, g.symm_apply_apply x⟩

theorem mul_preserves_B₀ (g h : Perm (Fin 6)) (hg : ∀ B ∈ B₀, B.image g ∈ B₀)
    (hh : ∀ B ∈ B₀, B.image h ∈ B₀) : ∀ B ∈ B₀, B.image (g * h) ∈ B₀ := by
  intro B hB
  have : B.image (g * h) = (B.image h).image g := by
    ext x; simp only [Finset.mem_image, coe_mul, Function.comp_apply]; constructor
    · rintro ⟨y, hy, rfl⟩; exact ⟨h y, ⟨y, hy, rfl⟩, rfl⟩
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩; exact ⟨y, hy, rfl⟩
  rw [this]; exact hg _ (hh B hB)

/-- H₆ acts imprimitively: it preserves the non-trivial block partition B₀ -/
theorem H₆_imprimitive : ∀ (g : H₆), ∀ B ∈ B₀, B.image g.val ∈ B₀ := by
  intro ⟨g, hg⟩
  -- Use closure_induction
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact g₁_preserves_B₀
    · exact g₂_preserves_B₀
    · exact g₃_preserves_B₀
  | one => exact one_preserves_B₀
  | mul x y _ _ hx hy => exact mul_preserves_B₀ x y hx hy
  | inv x _ hx => exact inv_preserves_B₀ x hx

-- ============================================
-- KERNEL ANALYSIS: ker(φ) = V₄ (Klein 4-group)
-- ============================================

set_option linter.style.nativeDecide false

/-- g₁² = (0 3)(2 5) - the square of g₁ is a double transposition -/
theorem g₁_sq : (g₁ 0 0 0)^2 = Equiv.swap (0 : Fin 6) 3 * Equiv.swap 2 5 := by
  native_decide

/-- g₂² = (0 3)(1 4) - the square of g₂ is a double transposition -/
theorem g₂_sq : (g₂ 0 0 0)^2 = Equiv.swap (0 : Fin 6) 3 * Equiv.swap 1 4 := by
  native_decide

/-- g₃² = (1 4)(2 5) - the square of g₃ is a double transposition -/
theorem g₃_sq : (g₃ 0 0 0)^2 = Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5 := by
  native_decide

/-- g₁² is in H₆ -/
theorem g₁_sq_mem : (g₁ 0 0 0)^2 ∈ H₆ := Subgroup.pow_mem _ (g₁_mem_H 0 0 0) 2

/-- g₂² is in H₆ -/
theorem g₂_sq_mem : (g₂ 0 0 0)^2 ∈ H₆ := Subgroup.pow_mem _ (g₂_mem_H 0 0 0) 2

/-- g₃² is in H₆ -/
theorem g₃_sq_mem : (g₃ 0 0 0)^2 ∈ H₆ := Subgroup.pow_mem _ (g₃_mem_H 0 0 0) 2

/-- All kernel elements are in H₆ -/
theorem kernelElements_subset_H₆ : ∀ g ∈ kernelElements, g ∈ H₆ := by
  intro g hg
  simp only [kernelElements, Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · have : g₂ 0 0 0 ^ 2 = Equiv.swap (0 : Fin 6) 3 * Equiv.swap 1 4 := g₂_sq
    rw [← this]; exact g₂_sq_mem
  · have : g₁ 0 0 0 ^ 2 = Equiv.swap (0 : Fin 6) 3 * Equiv.swap 2 5 := g₁_sq
    rw [← this]; exact g₁_sq_mem
  · have : g₃ 0 0 0 ^ 2 = Equiv.swap (1 : Fin 6) 4 * Equiv.swap 2 5 := g₃_sq
    rw [← this]; exact g₃_sq_mem

/-- Each kernel element fixes blocks (maps each block to itself) -/
theorem kernelElements_fix_blocks (g : Equiv.Perm (Fin 6)) (hg : g ∈ kernelElements) :
    blockAction g = (1 : Equiv.Perm (Fin 3)) := by
  simp only [kernelElements, Finset.mem_insert, Finset.mem_singleton] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · -- identity
    ext i
    simp only [blockAction, Equiv.Perm.coe_one, id_eq]
    fin_cases i <;> native_decide
  · -- (0 3)(1 4)
    ext i
    simp only [blockAction, Equiv.Perm.coe_one]
    fin_cases i <;> native_decide
  · -- (0 3)(2 5)
    ext i
    simp only [blockAction, Equiv.Perm.coe_one]
    fin_cases i <;> native_decide
  · -- (1 4)(2 5)
    ext i
    simp only [blockAction, Equiv.Perm.coe_one]
    fin_cases i <;> native_decide

/-- The group H₆ is isomorphic to S₄ -/
theorem H₆_iso_S4 : Nonempty (H₆ ≃* Equiv.Perm (Fin 4)) := H₆_iso_S4_exists

/-- H₆ is finite with cardinality 24 -/
noncomputable instance : Fintype H₆ :=
  -- H₆ is a subgroup of the finite group Perm(Fin 6), so it's finite
  -- We use classical logic to decide membership
  @Subgroup.instFintypeSubtypeMemOfDecidablePred _ _ H₆
    (Classical.decPred _) inferInstance

/-- H₆ has cardinality 24 (as a subgroup) -/
theorem H₆_card_eq_24 : Fintype.card H₆ = 24 := by
  -- Use the explicit enumeration from Lemma03_Explicit
  have h_eq : H₆ = H₆_subgroup_explicit := H₆_eq_explicit
  -- Build a membership equivalence for Fintype.card_of_subtype
  have mem_iff : ∀ x, x ∈ H₆_explicit ↔ x ∈ H₆ := fun x => by
    rw [h_eq]
    rfl
  rw [Fintype.card_of_subtype H₆_explicit mem_iff]
  exact H₆_explicit_card

end LemmaFeld.GroupTheory.AF.BaseCase
