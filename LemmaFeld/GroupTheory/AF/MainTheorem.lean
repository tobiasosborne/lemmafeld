import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.Transitivity.Lemma05
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma08
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma09
import LemmaFeld.GroupTheory.AF.ThreeCycle.ThreeCycleExtractHelpers
import LemmaFeld.GroupTheory.AF.ThreeCycle.ThreeCycleProof
import LemmaFeld.GroupTheory.AF.ThreeCycle.ThreeCycleSymmetric
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11
import LemmaFeld.GroupTheory.AF.SignAnalysis.Lemma12
import LemmaFeld.GroupTheory.AF.SignAnalysis.Lemma14
import LemmaFeld.GroupTheory.AF.SignAnalysis.Lemma15
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-! # Main Theorem: H = Aₙ or Sₙ. For n+k+m≥1, H=Aₙ if all odd, H=Sₙ otherwise. -/

namespace LemmaFeld.GroupTheory.AF.MainTheorem
open Equiv Equiv.Perm Subgroup

-- SECTION 1: Prerequisites
theorem omega_card_ge_seven (n k m : ℕ) (h : n + k + m ≥ 1) :
    Fintype.card (Omega n k m) ≥ 7 := by simp only [Omega, Fintype.card_fin]; omega

instance omega_nontrivial' (n k m : ℕ) : Nontrivial (Omega n k m) :=
  Fin.nontrivial_iff_two_le.mpr (by omega : 6 + n + k + m ≥ 2)

-- SECTION 2: 3-cycle in H
theorem commutator_g₁_g₂_mem_H (n k m : ℕ) : commutator_g₁_g₂ n k m ∈ H n k m := by
  unfold commutator_g₁_g₂; apply Subgroup.mul_mem
  · apply Subgroup.mul_mem; apply Subgroup.mul_mem
    · exact Subgroup.inv_mem _ (g₁_mem_H n k m)
    · exact Subgroup.inv_mem _ (g₂_mem_H n k m)
    · exact g₁_mem_H n k m
  · exact g₂_mem_H n k m

theorem commutator_g₁_g₃_mem_H (n k m : ℕ) : commutator_g₁_g₃ n k m ∈ H n k m := by
  unfold commutator_g₁_g₃; apply Subgroup.mul_mem
  · apply Subgroup.mul_mem; apply Subgroup.mul_mem
    · exact Subgroup.inv_mem _ (g₁_mem_H n k m)
    · exact Subgroup.inv_mem _ (g₃_mem_H n k m)
    · exact g₁_mem_H n k m
  · exact g₃_mem_H n k m

theorem commutator_g₂_g₃_mem_H' (n k m : ℕ) : commutator_g₂_g₃ n k m ∈ H n k m := by
  unfold commutator_g₂_g₃; apply Subgroup.mul_mem
  · apply Subgroup.mul_mem; apply Subgroup.mul_mem
    · exact Subgroup.inv_mem _ (g₂_mem_H n k m)
    · exact Subgroup.inv_mem _ (g₃_mem_H n k m)
    · exact g₂_mem_H n k m
  · exact g₃_mem_H n k m

theorem c₁₂_times_c₁₃_inv_mem_H (n k m : ℕ) : c₁₂_times_c₁₃_inv n k m ∈ H n k m := by
  unfold c₁₂_times_c₁₃_inv c₁₂ c₁₃; apply Subgroup.mul_mem
  · exact commutator_g₁_g₂_mem_H n k m
  · exact Subgroup.inv_mem _ (commutator_g₁_g₃_mem_H n k m)

theorem c₁₂_times_c₁₃_inv_squared_mem_H (n k m : ℕ) :
    (c₁₂_times_c₁₃_inv n k m) ^ 2 ∈ H n k m :=
  Subgroup.pow_mem _ (c₁₂_times_c₁₃_inv_mem_H n k m) 2

/-- (c₁₂ * c₁₃⁻¹)² is a 3-cycle when n ≥ 1 AND m = 0.
    When n ≥ 1, cycleType of c₁₂*c₁₃⁻¹ is {3,2,2}; squaring gives {3}.
    See ThreeCycleExtractHelpers.lean for computational verification.

    **Structural Proof Outline:**
    1. c₁₂ * c₁₃⁻¹ has cycleType {3,2,2} (one 3-cycle on {0,1,5}, two 2-cycles)
    2. Disjoint cycles commute, so σ² = c₃² * c₂² * c₂'²
    3. 2-cycles squared = identity, so σ² = c₃²
    4. c₃² is a 3-cycle (3-cycles squared remain 3-cycles)
    5. Therefore cycleType of σ² = {3}, which is IsThreeCycle by definition -/
theorem c₁₂_times_c₁₃_inv_squared_isThreeCycle_n_m0 (n k : ℕ) (hn : n ≥ 1) :
    ((c₁₂_times_c₁₃_inv n k 0) ^ 2).IsThreeCycle :=
  ThreeCycleProof.sq_isThreeCycle_n_ge1_m0 n k hn

/-- (c₁₃ * c₂₃⁻¹)² is a 3-cycle when m ≥ 1 AND k = 0.
    Symmetric to the n≥1 case: when k=0, g₂ has no tail, cycle structure is {3,2,2}. -/
theorem c₁₃_times_c₂₃_inv_squared_isThreeCycle_m_k0 (n m : ℕ) (hm : m ≥ 1) :
    ((commutator_g₁_g₃ n 0 m * (commutator_g₂_g₃ n 0 m)⁻¹) ^ 2).IsThreeCycle :=
  ThreeCycleSymmetric.isThreeCycle_m_ge1_k0 n m hm

/-- Iterated commutator [[g₁,g₂], g₂] for extracting 3-cycles when k ≥ 1.
    This construction: [c₁₂, g₂] = c₁₂⁻¹ * g₂⁻¹ * c₁₂ * g₂ where c₁₂ = [g₁,g₂].
    Squaring ([[g₁,g₂], g₂])² gives cycleType {3} when k ≥ 1. -/
def iteratedComm_g₂ (n k m : ℕ) : Perm (Omega n k m) :=
  (commutator_g₁_g₂ n k m)⁻¹ * (g₂ n k m)⁻¹ * commutator_g₁_g₂ n k m * g₂ n k m

/-- The iterated commutator is in H -/
theorem iteratedComm_g₂_mem_H (n k m : ℕ) : iteratedComm_g₂ n k m ∈ H n k m := by
  unfold iteratedComm_g₂
  apply Subgroup.mul_mem; apply Subgroup.mul_mem; apply Subgroup.mul_mem
  · exact Subgroup.inv_mem _ (commutator_g₁_g₂_mem_H n k m)
  · exact Subgroup.inv_mem _ (g₂_mem_H n k m)
  · exact commutator_g₁_g₂_mem_H n k m
  · exact g₂_mem_H n k m

/-- ([[g₁,g₂], g₂])² is a 3-cycle when k ≥ 1.
    When k≥1, iteratedComm has cycleType {3,2,...}, squaring yields {3}. -/
theorem iteratedComm_g₂_squared_isThreeCycle (n k m : ℕ) (hk : k ≥ 1) :
    ((iteratedComm_g₂ n k m) ^ 2).IsThreeCycle := by
  -- iteratedComm_g₂ = iteratedComm_g₂' by definition
  have h : iteratedComm_g₂ n k m = ThreeCycleSymmetric.iteratedComm_g₂' n k m := rfl
  rw [h]
  exact ThreeCycleSymmetric.isThreeCycle_k_ge1 n k m hk

/-- H contains a 3-cycle when n + k + m ≥ 1. Case analysis:
    • n≥1, m=0: (c₁₂*c₁₃⁻¹)²  • m≥1, k=0: (c₁₃*c₂₃⁻¹)²  • k≥1: [[g₁,g₂],g₂]² -/
theorem H_contains_threecycle (n k m : ℕ) (h : n + k + m ≥ 1) :
    ∃ σ : Perm (Omega n k m), σ.IsThreeCycle ∧ σ ∈ H n k m := by
  by_cases hm : m = 0
  · by_cases hn : n ≥ 1
    · -- n ≥ 1, m = 0: use (c₁₂ * c₁₃⁻¹)²
      subst hm
      exact ⟨(c₁₂_times_c₁₃_inv n k 0) ^ 2,
             c₁₂_times_c₁₃_inv_squared_isThreeCycle_n_m0 n k hn,
             c₁₂_times_c₁₃_inv_squared_mem_H n k 0⟩
    · -- n = 0, m = 0, k ≥ 1: use [[g₁,g₂], g₂]²
      subst hm; push_neg at hn
      have hk : k ≥ 1 := by omega
      exact ⟨(iteratedComm_g₂ n k 0) ^ 2,
             iteratedComm_g₂_squared_isThreeCycle n k 0 hk,
             Subgroup.pow_mem _ (iteratedComm_g₂_mem_H n k 0) 2⟩
  · by_cases hk : k = 0
    · -- m ≥ 1, k = 0: use (c₁₃ * c₂₃⁻¹)²
      subst hk
      have hm' : m ≥ 1 := Nat.one_le_iff_ne_zero.mpr hm
      refine ⟨(commutator_g₁_g₃ n 0 m * (commutator_g₂_g₃ n 0 m)⁻¹) ^ 2,
              c₁₃_times_c₂₃_inv_squared_isThreeCycle_m_k0 n m hm', ?_⟩
      apply Subgroup.pow_mem; apply Subgroup.mul_mem
      · exact commutator_g₁_g₃_mem_H n 0 m
      · exact Subgroup.inv_mem _ (commutator_g₂_g₃_mem_H' n 0 m)
    · -- m ≥ 1, k ≥ 1: use [[g₁,g₂], g₂]²
      have hk' : k ≥ 1 := Nat.one_le_iff_ne_zero.mpr hk
      exact ⟨(iteratedComm_g₂ n k m) ^ 2,
             iteratedComm_g₂_squared_isThreeCycle n k m hk',
             Subgroup.pow_mem _ (iteratedComm_g₂_mem_H n k m) 2⟩

-- SECTION 3: Main theorem components
theorem step1_transitive (n k m : ℕ) : MulAction.IsPretransitive (H n k m) (Omega n k m) :=
  LemmaFeld.GroupTheory.AF.Transitivity.H_isPretransitive n k m

theorem step2_primitive (n k m : ℕ) (h : n + k + m ≥ 1) :
    MulAction.IsPreprimitive (H n k m) (Omega n k m) :=
  LemmaFeld.GroupTheory.AF.Primitivity.lemma11_H_isPrimitive h

theorem step3_threecycle (n k m : ℕ) (h : n + k + m ≥ 1) :
    ∃ σ : Perm (Omega n k m), σ.IsThreeCycle ∧ σ ∈ H n k m := H_contains_threecycle n k m h

theorem step4_jordan (n k m : ℕ) (h : n + k + m ≥ 1) : alternatingGroup (Omega n k m) ≤ H n k m :=
  SignAnalysis.H_contains_alternating n k m h (step3_threecycle n k m h)

theorem step5_parity (n k m : ℕ) : (Perm.sign (g₁ n k m) = 1 ↔ Odd n) ∧
    (Perm.sign (g₂ n k m) = 1 ↔ Odd k) ∧ (Perm.sign (g₃ n k m) = 1 ↔ Odd m) :=
  ⟨SignAnalysis.g₁_even_iff_n_odd n k m, SignAnalysis.g₂_even_iff_k_odd n k m,
   SignAnalysis.g₃_even_iff_m_odd n k m⟩

-- SECTION 4: Main theorem
theorem main_theorem_alternating (n k m : ℕ) (hPrim : n + k + m ≥ 1)
    (hOdd : Odd n ∧ Odd k ∧ Odd m) : H n k m = alternatingGroup (Omega n k m) :=
  SignAnalysis.lemma15_H_eq_alternating n k m hPrim hOdd (step3_threecycle n k m hPrim)

theorem main_theorem_symmetric (n k m : ℕ) (hPrim : n + k + m ≥ 1)
    (hNotAllOdd : ¬(Odd n ∧ Odd k ∧ Odd m)) : H n k m = ⊤ :=
  SignAnalysis.lemma15_H_eq_symmetric n k m hPrim hNotAllOdd (step3_threecycle n k m hPrim)

theorem main_theorem (n k m : ℕ) (hPrim : n + k + m ≥ 1) :
    (H n k m = alternatingGroup (Omega n k m) ↔ (Odd n ∧ Odd k ∧ Odd m)) ∧
    (H n k m = ⊤ ↔ ¬(Odd n ∧ Odd k ∧ Odd m)) :=
  SignAnalysis.lemma15_H_classification n k m hPrim (step3_threecycle n k m hPrim)

-- SECTION 5: Examples
theorem H_1_1_1_eq_alternating : H 1 1 1 = alternatingGroup (Omega 1 1 1) :=
  main_theorem_alternating 1 1 1 (by omega) ⟨⟨0, rfl⟩, ⟨0, rfl⟩, ⟨0, rfl⟩⟩

theorem H_2_1_1_eq_symmetric : H 2 1 1 = ⊤ :=
  main_theorem_symmetric 2 1 1 (by omega) (fun ⟨hn, _, _⟩ => by obtain ⟨k, hk⟩ := hn; omega)

theorem H_1_2_1_eq_symmetric : H 1 2 1 = ⊤ :=
  main_theorem_symmetric 1 2 1 (by omega) (fun ⟨_, hk, _⟩ => by obtain ⟨j, hj⟩ := hk; omega)

theorem H_1_1_2_eq_symmetric : H 1 1 2 = ⊤ :=
  main_theorem_symmetric 1 1 2 (by omega) (fun ⟨_, _, hm⟩ => by obtain ⟨j, hj⟩ := hm; omega)

end LemmaFeld.GroupTheory.AF.MainTheorem
