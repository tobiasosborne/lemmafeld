/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.ThreeCycle.CoreElementLemmas

/-!
# Product Lemmas for Core Elements

Single-application (c₁₂ * c₁₃⁻¹) lemmas on core elements {0,1,2,3,4,5}.
-/

open Equiv Perm

namespace LemmaFeld.GroupTheory.AF.ProductLemmas

-- ============================================
-- SECTION 1: c₁₃⁻¹ actions on core elements
-- ============================================

/-- c₁₃⁻¹(0) = 5: proof that c₁₃(5) = 0 via g₃(5)=1, g₁(1)=1, g₃⁻¹(1)=5, g₁⁻¹(5)=0 -/
theorem c₁₃_inv_0_eq_5 (n k : ℕ) :
    (commutator_g₁_g₃ n k 0)⁻¹ ⟨0, by omega⟩ = ⟨5, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; unfold commutator_g₁_g₃; simp only [Perm.mul_apply]
  -- Goal: ⟨0, _⟩ = g₁⁻¹(g₃⁻¹(g₁(g₃(5))))
  rw [CoreElementLemmas.g₃_5_eq_1, TailLemmas.g₁_fixes_1, CoreElementLemmas.g₃_inv_1_eq_5,
      TailALast.g₁_inv_5_eq_0]

/-- c₁₃⁻¹(1) = 3: proof that c₁₃(3) = 1 via g₃(3)=3, g₁(3)=2, g₃⁻¹(2)=1, g₁⁻¹(1)=1 -/
theorem c₁₃_inv_1_eq_3 (n k : ℕ) :
    (commutator_g₁_g₃ n k 0)⁻¹ ⟨1, by omega⟩ = ⟨3, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; unfold commutator_g₁_g₃; simp only [Perm.mul_apply]
  -- Goal: ⟨1, _⟩ = g₁⁻¹(g₃⁻¹(g₁(g₃(3))))
  rw [CoreElementLemmas.g₃_fixes_3, CoreElementLemmas.g₁_3_eq_2,
      CoreElementLemmas.g₃_inv_2_eq_1, TailLemmas.g₁_inv_fixes_1]

/-- c₁₃⁻¹(2) = 1: proof that c₁₃(1) = 2 via g₃(1)=2, g₁(2)=6, g₃⁻¹(6)=6, g₁⁻¹(6)=2 (requires n ≥ 1) -/
theorem c₁₃_inv_2_eq_1 (n k : ℕ) (hn : n ≥ 1) :
    (commutator_g₁_g₃ n k 0)⁻¹ ⟨2, by omega⟩ = ⟨1, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; unfold commutator_g₁_g₃; simp only [Perm.mul_apply]
  -- Goal: ⟨2, _⟩ = g₁⁻¹(g₃⁻¹(g₁(g₃(1))))
  have hg₃_6 : g₃ n k 0 ⟨6, by omega⟩ = ⟨6, by omega⟩ :=
    ThreeCycleExtract.g₃_fixes_val_ge_6 n k ⟨6, by omega⟩ (by omega : 6 ≥ 6)
  have hg₃_inv_6 : (g₃ n k 0)⁻¹ ⟨6, by omega⟩ = ⟨6, by omega⟩ := by
    conv_lhs => rw [← hg₃_6]; rw [Perm.inv_apply_self]
  rw [CoreElementLemmas.g₃_1_eq_2, CoreElementLemmas.g₁_2_eq_6 n k hn, hg₃_inv_6,
      CoreElementLemmas.g₁_inv_6_eq_2 n k hn]

/-- c₁₃⁻¹(3) = 2: proof that c₁₃(2) = 3 via g₃(2)=4, g₁(4)=4, g₃⁻¹(4)=2, g₁⁻¹(2)=3 -/
theorem c₁₃_inv_3_eq_2 (n k : ℕ) :
    (commutator_g₁_g₃ n k 0)⁻¹ ⟨3, by omega⟩ = ⟨2, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; unfold commutator_g₁_g₃; simp only [Perm.mul_apply]
  -- Goal: ⟨3, _⟩ = g₁⁻¹(g₃⁻¹(g₁(g₃(2))))
  have hg₃_2_eq_4 : g₃ n k 0 ⟨2, by omega⟩ = ⟨4, by omega⟩ := by
    rw [ThreeCycleExtract.g₃_m0_eq]; unfold g₃CoreList
    have hnd : ([⟨2, by omega⟩, ⟨4, by omega⟩, ⟨5, by omega⟩, ⟨1, by omega⟩] :
        List (Omega n k 0)).Nodup := by
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, Fin.mk.injEq, or_false, not_or]
      refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_, ⟨not_false, List.nodup_nil⟩⟩ <;> omega
    have h_fp := List.formPerm_apply_lt_getElem _ hnd 0 (by simp)
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h_fp; exact h_fp
  have hg₃_inv_4_eq_2 : (g₃ n k 0)⁻¹ ⟨4, by omega⟩ = ⟨2, by omega⟩ := by
    rw [Perm.inv_eq_iff_eq]; exact hg₃_2_eq_4.symm
  rw [hg₃_2_eq_4, TailALast.g₁_fixes_4, hg₃_inv_4_eq_2, CoreElementLemmas.g₁_inv_2_eq_3]

/-- c₁₃⁻¹(5) = 4: proof that c₁₃(4) = 5 via g₃(4)=5, g₁(5)=3, g₃⁻¹(3)=3, g₁⁻¹(3)=5 -/
theorem c₁₃_inv_5_eq_4 (n k : ℕ) :
    (commutator_g₁_g₃ n k 0)⁻¹ ⟨5, by omega⟩ = ⟨4, by omega⟩ := by
  rw [Perm.inv_eq_iff_eq]; unfold commutator_g₁_g₃; simp only [Perm.mul_apply]
  -- Goal: ⟨5, _⟩ = g₁⁻¹(g₃⁻¹(g₁(g₃(4))))
  have hg₃_inv_3 : (g₃ n k 0)⁻¹ ⟨3, by omega⟩ = ⟨3, by omega⟩ := by
    have := CoreElementLemmas.g₃_fixes_3 n k
    conv_lhs => rw [← this]; rw [Perm.inv_apply_self]
  rw [TailALast.g₃_4_eq_5, CoreElementLemmas.g₁_5_eq_3, hg₃_inv_3, CoreElementLemmas.g₁_inv_3_eq_5]

-- ============================================
-- SECTION 2: c₁₂ actions on core elements
-- ============================================

/-- c₁₂(5) = 1: g₂(5)=5, g₁(5)=3, g₂⁻¹(3)=1, g₁⁻¹(1)=1 -/
theorem c₁₂_5_eq_1 (n k : ℕ) :
    commutator_g₁_g₂ n k 0 ⟨5, by omega⟩ = ⟨1, by omega⟩ := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  rw [CoreElementLemmas.g₂_fixes_5, CoreElementLemmas.g₁_5_eq_3,
      CoreElementLemmas.g₂_inv_3_eq_1, TailLemmas.g₁_inv_fixes_1]

/-- c₁₂(3) = 5: g₂(3)=4, g₁(4)=4, g₂⁻¹(4)=3, g₁⁻¹(3)=5 -/
theorem c₁₂_3_eq_5 (n k : ℕ) :
    commutator_g₁_g₂ n k 0 ⟨3, by omega⟩ = ⟨5, by omega⟩ := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  rw [CoreElementLemmas.g₂_3_eq_4, TailALast.g₁_fixes_4, CoreElementLemmas.g₂_inv_4_eq_3,
      CoreElementLemmas.g₁_inv_3_eq_5]

/-- c₁₂(1) = 3: g₂(1)=3, g₁(3)=2, g₂⁻¹(2)=2, g₁⁻¹(2)=3 -/
theorem c₁₂_1_eq_3 (n k : ℕ) :
    commutator_g₁_g₂ n k 0 ⟨1, by omega⟩ = ⟨3, by omega⟩ := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  rw [CoreElementLemmas.g₂_1_eq_3, CoreElementLemmas.g₁_3_eq_2,
      CoreElementLemmas.g₂_inv_fixes_2, CoreElementLemmas.g₁_inv_2_eq_3]

/-- c₁₂(2) = 2: g₂(2)=2, g₁(2)=6, g₂⁻¹(6)=6, g₁⁻¹(6)=2 (requires n ≥ 1) -/
theorem c₁₂_2_eq_2 (n k : ℕ) (hn : n ≥ 1) :
    commutator_g₁_g₂ n k 0 ⟨2, by omega⟩ = ⟨2, by omega⟩ := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  rw [CoreElementLemmas.g₂_fixes_2, CoreElementLemmas.g₁_2_eq_6 n k hn]
  have h6_tailA : 6 ≤ 6 ∧ (6 : ℕ) < 6 + n := ⟨le_refl 6, by omega⟩
  rw [TailAFixing.g₂_inv_fixes_tailA n k ⟨6, by omega⟩ h6_tailA,
      CoreElementLemmas.g₁_inv_6_eq_2 n k hn]

/-- c₁₂(4) = 0: g₂(4)=0, g₁(0)=5, g₂⁻¹(5)=5, g₁⁻¹(5)=0 -/
theorem c₁₂_4_eq_0 (n k : ℕ) :
    commutator_g₁_g₂ n k 0 ⟨4, by omega⟩ = ⟨0, by omega⟩ := by
  unfold commutator_g₁_g₂; simp only [Perm.mul_apply]
  rw [CoreElementLemmas.g₂_4_eq_0, TailALast.g₁_0_eq_5,
      CoreElementLemmas.g₂_inv_fixes_5, TailALast.g₁_inv_5_eq_0]

-- ============================================
-- SECTION 3: Product (c₁₂ * c₁₃⁻¹) on core elements
-- ============================================

/-- (c₁₂ * c₁₃⁻¹)(0) = 1 -/
theorem product_0_eq_1 (n k : ℕ) :
    c₁₂_times_c₁₃_inv n k 0 ⟨0, by omega⟩ = ⟨1, by omega⟩ := by
  unfold c₁₂_times_c₁₃_inv c₁₂ c₁₃; simp only [Perm.mul_apply]
  rw [c₁₃_inv_0_eq_5, c₁₂_5_eq_1]

/-- (c₁₂ * c₁₃⁻¹)(1) = 5 -/
theorem product_1_eq_5 (n k : ℕ) :
    c₁₂_times_c₁₃_inv n k 0 ⟨1, by omega⟩ = ⟨5, by omega⟩ := by
  unfold c₁₂_times_c₁₃_inv c₁₂ c₁₃; simp only [Perm.mul_apply]
  rw [c₁₃_inv_1_eq_3, c₁₂_3_eq_5]

/-- (c₁₂ * c₁₃⁻¹)(2) = 3 (requires n ≥ 1) -/
theorem product_2_eq_3 (n k : ℕ) (hn : n ≥ 1) :
    c₁₂_times_c₁₃_inv n k 0 ⟨2, by omega⟩ = ⟨3, by omega⟩ := by
  unfold c₁₂_times_c₁₃_inv c₁₂ c₁₃; simp only [Perm.mul_apply]
  rw [c₁₃_inv_2_eq_1 n k hn, c₁₂_1_eq_3]

/-- (c₁₂ * c₁₃⁻¹)(3) = 2 (requires n ≥ 1) -/
theorem product_3_eq_2 (n k : ℕ) (hn : n ≥ 1) :
    c₁₂_times_c₁₃_inv n k 0 ⟨3, by omega⟩ = ⟨2, by omega⟩ := by
  unfold c₁₂_times_c₁₃_inv c₁₂ c₁₃; simp only [Perm.mul_apply]
  rw [c₁₃_inv_3_eq_2, c₁₂_2_eq_2 n k hn]

/-- (c₁₂ * c₁₃⁻¹)(5) = 0 -/
theorem product_5_eq_0 (n k : ℕ) :
    c₁₂_times_c₁₃_inv n k 0 ⟨5, by omega⟩ = ⟨0, by omega⟩ := by
  unfold c₁₂_times_c₁₃_inv c₁₂ c₁₃; simp only [Perm.mul_apply]
  rw [c₁₃_inv_5_eq_4, c₁₂_4_eq_0]

end LemmaFeld.GroupTheory.AF.ProductLemmas
