/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.ThreeCycle.Case1ProductLemmas

/-!
# Commutator and Product Lemmas for Case 1: m ≥ 1, k = 0

This file contains c₂₃ action lemmas and the product (c₁₃ * c₂₃⁻¹) lemmas.

## Key Results

- c₂₃(4) = 3, c₂₃(2) = 4, c₂₃(0) = 5
- Product lemmas: prod(3) = 5, prod(4) = 3, prod(5) = 4
- Squared actions: sq(3) = 4, sq(4) = 5, sq(5) = 3
-/

open Equiv Perm

namespace LemmaFeld.GroupTheory.AF.Case1CommutatorLemmas

-- ============================================
-- SECTION 1: c₂₃ actions on core elements
-- ============================================

/-- c₂₃(4) = 3: g₃(4)=5, g₂(5)=5, g₃⁻¹(5)=4, g₂⁻¹(4)=3 -/
theorem c₂₃_4_eq_3 (n m : ℕ) : commutator_g₂_g₃ n 0 m ⟨4, by omega⟩ = ⟨3, by omega⟩ := by
  unfold commutator_g₂_g₃; simp only [Perm.mul_apply]
  rw [Case1ProductLemmas.g₃_4_eq_5, Case1ProductLemmas.g₂_k0_fixes_5,
      Case1ProductLemmas.g₃_inv_5_eq_4, Case1ProductLemmas.g₂_k0_inv_4_eq_3]

/-- c₂₃(2) = 4: g₃(2)=4, g₂(4)=0, g₃⁻¹(0)=0, g₂⁻¹(0)=4 -/
theorem c₂₃_2_eq_4 (n m : ℕ) : commutator_g₂_g₃ n 0 m ⟨2, by omega⟩ = ⟨4, by omega⟩ := by
  unfold commutator_g₂_g₃; simp only [Perm.mul_apply]
  rw [Case1ProductLemmas.g₃_2_eq_4, Case1ProductLemmas.g₂_k0_4_eq_0,
      Case1ProductLemmas.g₃_inv_fixes_0, Case1ProductLemmas.g₂_k0_inv_0_eq_4]

/-- c₂₃(0) = 5: g₃(0)=0, g₂(0)=1, g₃⁻¹(1)=5, g₂⁻¹(5)=5 -/
theorem c₂₃_0_eq_5 (n m : ℕ) : commutator_g₂_g₃ n 0 m ⟨0, by omega⟩ = ⟨5, by omega⟩ := by
  unfold commutator_g₂_g₃; simp only [Perm.mul_apply]
  rw [Case1ProductLemmas.g₃_fixes_0, Case1ProductLemmas.g₂_k0_0_eq_1,
      Case1ProductLemmas.g₃_inv_1_eq_5, Case1ProductLemmas.g₂_k0_inv_fixes_5]

-- c₂₃⁻¹ lemmas (derived from above)
theorem c₂₃_inv_3_eq_4 (n m : ℕ) : (commutator_g₂_g₃ n 0 m)⁻¹ ⟨3, by omega⟩ = ⟨4, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (c₂₃_4_eq_3 n m).symm

theorem c₂₃_inv_4_eq_2 (n m : ℕ) : (commutator_g₂_g₃ n 0 m)⁻¹ ⟨4, by omega⟩ = ⟨2, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (c₂₃_2_eq_4 n m).symm

theorem c₂₃_inv_5_eq_0 (n m : ℕ) : (commutator_g₂_g₃ n 0 m)⁻¹ ⟨5, by omega⟩ = ⟨0, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (c₂₃_0_eq_5 n m).symm

-- ============================================
-- SECTION 2: c₁₃ actions on core elements
-- ============================================

/-- g₁ fixes 1 -/
theorem g₁_fixes_1 (n m : ℕ) : g₁ n 0 m ⟨1, by omega⟩ = ⟨1, by omega⟩ := by
  unfold g₁; apply List.formPerm_apply_of_notMem
  simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false, List.mem_map, List.mem_finRange, not_or]
  constructor
  · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
  · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega

/-- g₁(5) = 3 -/
theorem g₁_5_eq_3 (n m : ℕ) : g₁ n 0 m ⟨5, by omega⟩ = ⟨3, by omega⟩ := by
  unfold g₁; have hnd := g₁_list_nodup n 0 m; have hlen := g₁_cycle_length n 0 m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 1 (by rw [hlen]; omega)
  simp only [g₁CoreList, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  exact h_fp

/-- g₁(3) = 2 -/
theorem g₁_3_eq_2 (n m : ℕ) : g₁ n 0 m ⟨3, by omega⟩ = ⟨2, by omega⟩ := by
  unfold g₁; have hnd := g₁_list_nodup n 0 m; have hlen := g₁_cycle_length n 0 m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 2 (by rw [hlen]; omega)
  simp only [g₁CoreList, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  exact h_fp

/-- g₁(0) = 5 -/
theorem g₁_0_eq_5 (n m : ℕ) : g₁ n 0 m ⟨0, by omega⟩ = ⟨5, by omega⟩ := by
  unfold g₁; have hnd := g₁_list_nodup n 0 m; have hlen := g₁_cycle_length n 0 m
  have h_fp := List.formPerm_apply_lt_getElem _ hnd 0 (by rw [hlen]; omega)
  simp only [g₁CoreList, List.cons_append, List.getElem_cons_succ, List.getElem_cons_zero] at h_fp
  exact h_fp

-- Inverse lemmas
theorem g₁_inv_3_eq_5 (n m : ℕ) : (g₁ n 0 m)⁻¹ ⟨3, by omega⟩ = ⟨5, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₁_5_eq_3 n m).symm

theorem g₁_inv_2_eq_3 (n m : ℕ) : (g₁ n 0 m)⁻¹ ⟨2, by omega⟩ = ⟨3, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₁_3_eq_2 n m).symm

theorem g₁_inv_5_eq_0 (n m : ℕ) : (g₁ n 0 m)⁻¹ ⟨5, by omega⟩ = ⟨0, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; exact (g₁_0_eq_5 n m).symm

theorem g₁_inv_fixes_1 (n m : ℕ) : (g₁ n 0 m)⁻¹ ⟨1, by omega⟩ = ⟨1, by omega⟩ := by
  have h := g₁_fixes_1 n m; conv_lhs => rw [← h]; rw [Perm.inv_apply_self]

/-- c₁₃(4) = 5: g₃(4)=5, g₁(5)=3, g₃⁻¹(3)=3, g₁⁻¹(3)=5 -/
theorem c₁₃_4_eq_5 (n m : ℕ) : commutator_g₁_g₃ n 0 m ⟨4, by omega⟩ = ⟨5, by omega⟩ := by
  unfold commutator_g₁_g₃; simp only [Perm.mul_apply]
  rw [Case1ProductLemmas.g₃_4_eq_5, g₁_5_eq_3,
      Case1ProductLemmas.g₃_inv_fixes_3, g₁_inv_3_eq_5]

/-- c₁₃(2) = 3: g₃(2)=4, g₁(4)=4, g₃⁻¹(4)=2, g₁⁻¹(2)=3 -/
theorem c₁₃_2_eq_3 (n m : ℕ) : commutator_g₁_g₃ n 0 m ⟨2, by omega⟩ = ⟨3, by omega⟩ := by
  unfold commutator_g₁_g₃; simp only [Perm.mul_apply]
  have hg₁_4 : g₁ n 0 m ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
    unfold g₁; apply List.formPerm_apply_of_notMem
    simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false, List.mem_map, List.mem_finRange, not_or]
    constructor
    · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
    · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega
  rw [Case1ProductLemmas.g₃_2_eq_4, hg₁_4,
      Case1ProductLemmas.g₃_inv_4_eq_2, g₁_inv_2_eq_3]

/-- c₁₃(0) = 4: g₃(0)=0, g₁(0)=5, g₃⁻¹(5)=4, g₁⁻¹(4)=4 -/
theorem c₁₃_0_eq_4 (n m : ℕ) : commutator_g₁_g₃ n 0 m ⟨0, by omega⟩ = ⟨4, by omega⟩ := by
  unfold commutator_g₁_g₃; simp only [Perm.mul_apply]
  have hg₁_inv_4 : (g₁ n 0 m)⁻¹ ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
    have hg₁_4 : g₁ n 0 m ⟨4, by omega⟩ = ⟨4, by omega⟩ := by
      unfold g₁; apply List.formPerm_apply_of_notMem
      simp only [g₁CoreList, tailAList, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, List.mem_map, List.mem_finRange, not_or]
      constructor
      · refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [Fin.ext_iff] <;> omega
      · intro ⟨i, _, hi⟩; simp only [Fin.ext_iff] at hi; omega
    conv_lhs => rw [← hg₁_4]; rw [Perm.inv_apply_self]
  rw [Case1ProductLemmas.g₃_fixes_0, g₁_0_eq_5,
      Case1ProductLemmas.g₃_inv_5_eq_4, hg₁_inv_4]

-- ============================================
-- SECTION 3: Product (c₁₃ * c₂₃⁻¹) lemmas
-- ============================================

/-- (c₁₃ * c₂₃⁻¹)(3) = 5 -/
theorem product_3_eq_5 (n m : ℕ) :
    SymmetricCase1.c₁₃_times_c₂₃_inv n m ⟨3, by omega⟩ = ⟨5, by omega⟩ := by
  unfold SymmetricCase1.c₁₃_times_c₂₃_inv; simp only [Perm.mul_apply]
  rw [c₂₃_inv_3_eq_4, c₁₃_4_eq_5]

/-- (c₁₃ * c₂₃⁻¹)(4) = 3 -/
theorem product_4_eq_3 (n m : ℕ) :
    SymmetricCase1.c₁₃_times_c₂₃_inv n m ⟨4, by omega⟩ = ⟨3, by omega⟩ := by
  unfold SymmetricCase1.c₁₃_times_c₂₃_inv; simp only [Perm.mul_apply]
  rw [c₂₃_inv_4_eq_2, c₁₃_2_eq_3]

/-- (c₁₃ * c₂₃⁻¹)(5) = 4 -/
theorem product_5_eq_4 (n m : ℕ) :
    SymmetricCase1.c₁₃_times_c₂₃_inv n m ⟨5, by omega⟩ = ⟨4, by omega⟩ := by
  unfold SymmetricCase1.c₁₃_times_c₂₃_inv; simp only [Perm.mul_apply]
  rw [c₂₃_inv_5_eq_0, c₁₃_0_eq_4]

-- ============================================
-- SECTION 4: Squared action lemmas
-- ============================================

/-- (c₁₃ * c₂₃⁻¹)²(3) = 4 -/
theorem sq_3_eq_4 (n m : ℕ) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) ⟨3, by omega⟩ = ⟨4, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [product_3_eq_5, product_5_eq_4]

/-- (c₁₃ * c₂₃⁻¹)²(4) = 5 -/
theorem sq_4_eq_5 (n m : ℕ) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) ⟨4, by omega⟩ = ⟨5, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [product_4_eq_3, product_3_eq_5]

/-- (c₁₃ * c₂₃⁻¹)²(5) = 3 -/
theorem sq_5_eq_3 (n m : ℕ) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) ⟨5, by omega⟩ = ⟨3, by omega⟩ := by
  simp only [sq, Perm.mul_apply]
  rw [product_5_eq_4, product_4_eq_3]

end LemmaFeld.GroupTheory.AF.Case1CommutatorLemmas
