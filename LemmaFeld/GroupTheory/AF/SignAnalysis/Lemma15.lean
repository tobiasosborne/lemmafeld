/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.SignAnalysis.Lemma12
import LemmaFeld.GroupTheory.AF.SignAnalysis.Lemma14

/-!
# Lemma 15: Aₙ vs Sₙ

Determines whether H equals Aₙ or Sₙ based on generator parity.

## Main Results

* `lemma15_H_eq_alternating` - H = Aₙ when n, k, m all odd
* `lemma15_H_eq_symmetric` - H = Sₙ when not all of n, k, m are odd

## Proof Strategy

1. **Index-2 Dichotomy**: Since [Sₙ : Aₙ] = 2, any G with Aₙ ≤ G ≤ Sₙ satisfies
   G = Aₙ or G = Sₙ (by Lagrange's theorem).

2. **Sign Characterization**:
   - G = Aₙ ⟺ G ⊆ Aₙ ⟺ all elements even ⟺ all generators even
   - G = Sₙ ⟺ G ⊄ Aₙ ⟺ some element odd ⟺ some generator odd

3. **Application to H**:
   - By Lemma 14: sign(gᵢ) = 1 iff tail length is odd
   - H = Aₙ ⟺ n, k, m all odd
   - H = Sₙ ⟺ not all of n, k, m are odd

## Reference

See `examples/lemmas/lemma15_an_vs_sn.md` for the natural language proof.
-/

namespace LemmaFeld.GroupTheory.AF.SignAnalysis

open Equiv Equiv.Perm Subgroup

/-- The alternating group has index 2 in the symmetric group. -/
theorem alternatingGroup_index_two (α : Type*) [Fintype α] [DecidableEq α] [Nontrivial α] :
    (alternatingGroup α).index = 2 := alternatingGroup.index_eq_two

/-- If G contains Aₙ, then G.index ∈ {1, 2} (Lagrange). -/
theorem index_of_supergroup_alternating (α : Type*) [Fintype α] [DecidableEq α] [Nontrivial α]
    {G : Subgroup (Perm α)} (hG : alternatingGroup α ≤ G) :
    G.index = 1 ∨ G.index = 2 := by
  have hDiv := index_dvd_of_le hG
  rw [alternatingGroup_index_two] at hDiv
  -- Divisors of 2 are exactly {1, 2} by Nat.dvd_prime
  rw [Nat.dvd_prime Nat.prime_two] at hDiv
  exact hDiv

/-- **Index-2 Dichotomy**: If Aₙ ≤ G ≤ Sₙ, then G = Aₙ or G = Sₙ -/
theorem alternating_or_symmetric (α : Type*) [Fintype α] [DecidableEq α] [Nontrivial α]
    {G : Subgroup (Perm α)} (hG : alternatingGroup α ≤ G) :
    G = alternatingGroup α ∨ G = ⊤ := by
  rcases index_of_supergroup_alternating α hG with hIdx | hIdx
  · right
    exact index_eq_one.mp hIdx
  · left
    -- Both have index 2, so they're equal via relIndex argument
    have hIdx' := alternatingGroup_index_two α
    have hRel : (alternatingGroup α).relIndex G = 1 := by
      have h := relIndex_mul_index hG; rw [hIdx, hIdx'] at h; omega
    exact le_antisymm (relIndex_eq_one.mp hRel) hG

/-- G ⊆ Aₙ iff generators have sign 1 (for closure-generated subgroups) -/
theorem closure_le_alternating_iff {α : Type*} [Fintype α] [DecidableEq α]
    (S : Set (Perm α)) :
    closure S ≤ alternatingGroup α ↔ ∀ g ∈ S, Perm.sign g = 1 := by
  rw [closure_le]
  exact ⟨fun h g hg => mem_alternatingGroup.mp (h hg),
         fun h g hg => mem_alternatingGroup.mpr (h g hg)⟩

/-- H is contained in Aₙ iff all three generators are even -/
theorem H_le_alternating_iff (n k m : ℕ) :
    H n k m ≤ alternatingGroup (Omega n k m) ↔
    (Perm.sign (g₁ n k m) = 1 ∧ Perm.sign (g₂ n k m) = 1 ∧ Perm.sign (g₃ n k m) = 1) := by
  rw [H, closure_le_alternating_iff]
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro h
    exact ⟨h (g₁ n k m) (Or.inl rfl),
           h (g₂ n k m) (Or.inr (Or.inl rfl)),
           h (g₃ n k m) (Or.inr (Or.inr rfl))⟩
  · intro ⟨h1, h2, h3⟩ g hg
    rcases hg with rfl | rfl | rfl
    · exact h1
    · exact h2
    · exact h3

/-- H is contained in Aₙ iff n, k, m are all odd -/
theorem H_le_alternating_iff_all_odd (n k m : ℕ) :
    H n k m ≤ alternatingGroup (Omega n k m) ↔ (Odd n ∧ Odd k ∧ Odd m) := by
  rw [H_le_alternating_iff, all_generators_even_iff]

-- ============================================
-- SECTION 4: MAIN THEOREMS
-- ============================================

/-- **Lemma 15a: H = Aₙ when all generators are even**

    If n, k, m are all odd, then H = Aₙ. -/
theorem lemma15_H_eq_alternating (n k m : ℕ) (hPrim : n + k + m ≥ 1)
    (hOdd : Odd n ∧ Odd k ∧ Odd m)
    (h3cycle : ∃ σ : Perm (Omega n k m), σ.IsThreeCycle ∧ σ ∈ H n k m) :
    H n k m = alternatingGroup (Omega n k m) := by
  have hLe : alternatingGroup (Omega n k m) ≤ H n k m :=
    H_contains_alternating n k m hPrim h3cycle
  have hLe' : H n k m ≤ alternatingGroup (Omega n k m) :=
    H_le_alternating_iff_all_odd n k m |>.mpr hOdd
  exact le_antisymm hLe' hLe

/-- **Lemma 15b: H = Sₙ when some generator is odd**

    If not all of n, k, m are odd, then H = Sₙ. -/
theorem lemma15_H_eq_symmetric (n k m : ℕ) (hPrim : n + k + m ≥ 1)
    (hNotAllOdd : ¬(Odd n ∧ Odd k ∧ Odd m))
    (h3cycle : ∃ σ : Perm (Omega n k m), σ.IsThreeCycle ∧ σ ∈ H n k m) :
    H n k m = ⊤ := by
  have hLe : alternatingGroup (Omega n k m) ≤ H n k m :=
    H_contains_alternating n k m hPrim h3cycle
  have hNontriv : Nontrivial (Omega n k m) := by
    simp only [Omega]
    exact Fin.nontrivial_iff_two_le.mpr (by omega)
  rcases alternating_or_symmetric (Omega n k m) hLe with hAlt | hSym
  · -- Case H = Aₙ contradicts that some generator is odd
    exfalso
    have hAllOdd := H_le_alternating_iff_all_odd n k m |>.mp (le_of_eq hAlt)
    exact hNotAllOdd hAllOdd
  · exact hSym

-- ============================================
-- SECTION 5: COMBINED MAIN THEOREM
-- ============================================

/-- **Lemma 15: H = Aₙ or H = Sₙ**

    Combined statement: H equals Aₙ iff n, k, m are all odd;
    otherwise H = Sₙ. -/
theorem lemma15_H_classification (n k m : ℕ) (hPrim : n + k + m ≥ 1)
    (h3cycle : ∃ σ : Perm (Omega n k m), σ.IsThreeCycle ∧ σ ∈ H n k m) :
    (H n k m = alternatingGroup (Omega n k m) ↔ (Odd n ∧ Odd k ∧ Odd m)) ∧
    (H n k m = ⊤ ↔ ¬(Odd n ∧ Odd k ∧ Odd m)) := by
  have hNontriv : Nontrivial (Omega n k m) := by
    simp only [Omega]
    exact Fin.nontrivial_iff_two_le.mpr (by omega)
  have hLe : alternatingGroup (Omega n k m) ≤ H n k m :=
    H_contains_alternating n k m hPrim h3cycle
  have hDichotomy := alternating_or_symmetric (Omega n k m) hLe
  constructor
  · constructor
    · intro hEq
      exact H_le_alternating_iff_all_odd n k m |>.mp (le_of_eq hEq)
    · intro hOdd
      exact lemma15_H_eq_alternating n k m hPrim hOdd h3cycle
  · constructor
    · intro hEq hOdd
      have hAlt := lemma15_H_eq_alternating n k m hPrim hOdd h3cycle
      rw [hEq] at hAlt
      -- ⊤ = Aₙ contradicts index_alternating = 2 ≠ 1 = index_top
      have hIdx : (alternatingGroup (Omega n k m)).index = 2 := alternatingGroup_index_two _
      rw [← hAlt, index_top] at hIdx
      omega
    · intro hNotOdd
      exact lemma15_H_eq_symmetric n k m hPrim hNotOdd h3cycle

end LemmaFeld.GroupTheory.AF.SignAnalysis
