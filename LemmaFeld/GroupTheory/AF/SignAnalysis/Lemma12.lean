/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11
import Mathlib.GroupTheory.GroupAction.Jordan
import Mathlib.GroupTheory.SpecificGroups.Alternating

/-!
# Lemma 12: Jordan's Theorem

Let G ≤ Sₙ be primitive with n ≥ 5. If G contains a 3-cycle, then G ≥ Aₙ.

## Main Results

* `lemma12_jordan` - Jordan's theorem for H: primitive + 3-cycle → contains Aₙ

## Mathlib Reference

Mathlib provides this as `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`
in `Mathlib.GroupTheory.GroupAction.Jordan`.

## Historical Note

Jordan's Theorem was first proven by Camille Jordan in 1873.
- Jordan 1873, Bull. Soc. Math. France
- Wielandt 1964, Finite Permutation Groups, Thm 13.9
- Dixon-Mortimer 1996, Permutation Groups, Thm 3.3A

## Reference

See `examples/lemmas/lemma12_jordan_theorem.md` for the natural language proof.
-/

namespace LemmaFeld.GroupTheory.AF.SignAnalysis

open Equiv Equiv.Perm MulAction

-- ============================================
-- SECTION 1: MATHLIB'S JORDAN THEOREM
-- ============================================

/-- Mathlib's Jordan Theorem: If G is a primitive permutation group containing
    a 3-cycle, then G contains the alternating group.

    This is `Equiv.Perm.alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem`. -/
theorem jordan_from_mathlib {α : Type*} [Fintype α] [DecidableEq α]
    {G : Subgroup (Perm α)} (hPrim : IsPreprimitive G α)
    {g : Perm α} (hg : g.IsThreeCycle) (hgG : g ∈ G) :
    alternatingGroup α ≤ G :=
  alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hPrim hg hgG

-- ============================================
-- SECTION 2: THREE-CYCLE PROPERTIES
-- ============================================

/-- A 3-cycle is an even permutation -/
theorem threeCycle_is_even {α : Type*} [Fintype α] [DecidableEq α]
    {σ : Perm α} (hσ : σ.IsThreeCycle) : σ ∈ alternatingGroup α :=
  hσ.mem_alternatingGroup

-- ============================================
-- SECTION 3: APPLICATION TO H
-- ============================================

/-- Size constraint: We need |Ω| ≥ 5 for Jordan's theorem to apply.
    Since |Ω| = 6 + n + k + m ≥ 6 > 5, this is always satisfied. -/
theorem omega_card_ge_five (n k m : ℕ) : Fintype.card (Omega n k m) ≥ 5 := by
  simp only [Omega, Fintype.card_fin]
  omega

/-- **Lemma 12: Jordan's Theorem for H**

    If H acts primitively on Ω and contains a 3-cycle, then H ≥ Aₙ.

    Combined with:
    - Lemma 11: H is primitive when n + k + m ≥ 1
    - Lemma 9: H contains a 3-cycle (from commutators)

    This allows us to conclude H ≥ Aₙ. -/
theorem lemma12_jordan (n k m : ℕ) (hPrim : n + k + m ≥ 1)
    {σ : Perm (Omega n k m)} (hσ : σ.IsThreeCycle) (hσH : σ ∈ H n k m) :
    alternatingGroup (Omega n k m) ≤ H n k m := by
  have hP : IsPreprimitive (H n k m) (Omega n k m) :=
    LemmaFeld.GroupTheory.AF.Primitivity.lemma11_H_isPrimitive hPrim
  exact alternatingGroup_le_of_isPreprimitive_of_isThreeCycle_mem hP hσ hσH

-- ============================================
-- SECTION 4: CONSEQUENCE FOR MAIN THEOREM
-- ============================================

/-- If H is primitive and contains a 3-cycle, then H contains all even permutations -/
theorem H_contains_alternating (n k m : ℕ) (hPrim : n + k + m ≥ 1)
    (h3cycle : ∃ σ : Perm (Omega n k m), σ.IsThreeCycle ∧ σ ∈ H n k m) :
    alternatingGroup (Omega n k m) ≤ H n k m := by
  obtain ⟨σ, hσ, hσH⟩ := h3cycle
  exact lemma12_jordan n k m hPrim hσ hσH

/-- Equivalent formulation: every even permutation on Ω is in H -/
theorem even_perm_in_H (n k m : ℕ) (hPrim : n + k + m ≥ 1)
    (h3cycle : ∃ σ : Perm (Omega n k m), σ.IsThreeCycle ∧ σ ∈ H n k m)
    (τ : Perm (Omega n k m)) (hτ : τ ∈ alternatingGroup (Omega n k m)) :
    τ ∈ H n k m := by
  exact H_contains_alternating n k m hPrim h3cycle hτ

end LemmaFeld.GroupTheory.AF.SignAnalysis
