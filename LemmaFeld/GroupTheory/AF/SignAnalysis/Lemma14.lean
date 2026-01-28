/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.SignAnalysis.Lemma13
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Lemma 14: Generator Parity

Each generator g₁, g₂, g₃ has a specific sign depending on n, k, m:
- sign(g₁) = (-1)^{n+3}
- sign(g₂) = (-1)^{k+3}
- sign(g₃) = (-1)^{m+3}

## Main Results

* `lemma14_sign_g₁` - sign(g₁) = (-1)^{n+3}
* `lemma14_sign_g₂` - sign(g₂) = (-1)^{k+3}
* `lemma14_sign_g₃` - sign(g₃) = (-1)^{m+3}

## Proof Strategy

Each generator gᵢ is a single cycle of length 4 + (tail length).
By Lemma 13, an l-cycle has sign (-1)^{l-1}.
- g₁ is a (4+n)-cycle, so sign = (-1)^{4+n-1} = (-1)^{n+3}
- g₂ is a (4+k)-cycle, so sign = (-1)^{4+k-1} = (-1)^{k+3}
- g₃ is a (4+m)-cycle, so sign = (-1)^{4+m-1} = (-1)^{m+3}

## Reference

See `examples/lemmas/lemma14_generator_parity.md` for the natural language proof.
-/

namespace LemmaFeld.GroupTheory.AF.SignAnalysis

open Equiv Equiv.Perm

-- ============================================
-- SECTION 1: GENERATORS ARE CYCLES
-- ============================================

/-- g₁ is a cycle -/
theorem g₁_isCycle (n k m : ℕ) : (g₁ n k m).IsCycle := by
  unfold g₁
  apply List.isCycle_formPerm
  · exact g₁_list_nodup n k m
  · have := g₁_cycle_length n k m; simp only [List.length_append] at this ⊢; omega

/-- g₂ is a cycle -/
theorem g₂_isCycle (n k m : ℕ) : (g₂ n k m).IsCycle := by
  unfold g₂
  apply List.isCycle_formPerm
  · exact g₂_list_nodup n k m
  · have := g₂_cycle_length n k m; simp only [List.length_append] at this ⊢; omega

/-- g₃ is a cycle -/
theorem g₃_isCycle (n k m : ℕ) : (g₃ n k m).IsCycle := by
  unfold g₃
  apply List.isCycle_formPerm
  · exact g₃_list_nodup n k m
  · have := g₃_cycle_length n k m; simp only [List.length_append] at this ⊢; omega

-- ============================================
-- SECTION 2: SUPPORT CARDINALITY
-- ============================================

/-- Helper: g₁ list is not a singleton -/
private theorem g₁_list_not_singleton (n k m : ℕ) :
    ∀ x, g₁CoreList n k m ++ tailAList n k m ≠ [x] := by
  intro x h
  have hlen := congr_arg List.length h
  rw [g₁_cycle_length, List.length_singleton] at hlen
  omega

/-- Helper: g₂ list is not a singleton -/
private theorem g₂_list_not_singleton (n k m : ℕ) :
    ∀ x, g₂CoreList n k m ++ tailBList n k m ≠ [x] := by
  intro x h
  have hlen := congr_arg List.length h
  rw [g₂_cycle_length, List.length_singleton] at hlen
  omega

/-- Helper: g₃ list is not a singleton -/
private theorem g₃_list_not_singleton (n k m : ℕ) :
    ∀ x, g₃CoreList n k m ++ tailCList n k m ≠ [x] := by
  intro x h
  have hlen := congr_arg List.length h
  rw [g₃_cycle_length, List.length_singleton] at hlen
  omega

/-- The support of g₁ has cardinality 4 + n -/
theorem g₁_support_card (n k m : ℕ) :
    (g₁ n k m).support.card = 4 + n := by
  have h := List.support_formPerm_of_nodup
    (g₁CoreList n k m ++ tailAList n k m) (g₁_list_nodup n k m) (g₁_list_not_singleton n k m)
  simp only [g₁]
  rw [h, List.toFinset_card_of_nodup (g₁_list_nodup n k m), g₁_cycle_length]

/-- The support of g₂ has cardinality 4 + k -/
theorem g₂_support_card (n k m : ℕ) :
    (g₂ n k m).support.card = 4 + k := by
  have h := List.support_formPerm_of_nodup
    (g₂CoreList n k m ++ tailBList n k m) (g₂_list_nodup n k m) (g₂_list_not_singleton n k m)
  simp only [g₂]
  rw [h, List.toFinset_card_of_nodup (g₂_list_nodup n k m), g₂_cycle_length]

/-- The support of g₃ has cardinality 4 + m -/
theorem g₃_support_card (n k m : ℕ) :
    (g₃ n k m).support.card = 4 + m := by
  have h := List.support_formPerm_of_nodup
    (g₃CoreList n k m ++ tailCList n k m) (g₃_list_nodup n k m) (g₃_list_not_singleton n k m)
  simp only [g₃]
  rw [h, List.toFinset_card_of_nodup (g₃_list_nodup n k m), g₃_cycle_length]

-- ============================================
-- SECTION 3: MAIN THEOREMS
-- ============================================

/-- **Lemma 14a: Sign of g₁**

    sign(g₁) = (-1)^{n+3}

    Proof: g₁ is a cycle of length 4 + n.
    By Lemma 13, sign = (-1)^{(4+n)-1} = (-1)^{n+3}. -/
theorem lemma14_sign_g₁ (n k m : ℕ) :
    Perm.sign (g₁ n k m) = (-1 : ℤˣ) ^ (n + 3) := by
  have hCycle := g₁_isCycle n k m
  have hCard := g₁_support_card n k m
  rw [lemma13_cycle_sign hCycle (by omega : (g₁ n k m).support.card ≥ 1)]
  rw [hCard]
  congr 1
  omega

/-- **Lemma 14b: Sign of g₂**

    sign(g₂) = (-1)^{k+3}

    Proof: g₂ is a cycle of length 4 + k.
    By Lemma 13, sign = (-1)^{(4+k)-1} = (-1)^{k+3}. -/
theorem lemma14_sign_g₂ (n k m : ℕ) :
    Perm.sign (g₂ n k m) = (-1 : ℤˣ) ^ (k + 3) := by
  have hCycle := g₂_isCycle n k m
  have hCard := g₂_support_card n k m
  rw [lemma13_cycle_sign hCycle (by omega : (g₂ n k m).support.card ≥ 1)]
  rw [hCard]
  congr 1
  omega

/-- **Lemma 14c: Sign of g₃**

    sign(g₃) = (-1)^{m+3}

    Proof: g₃ is a cycle of length 4 + m.
    By Lemma 13, sign = (-1)^{(4+m)-1} = (-1)^{m+3}. -/
theorem lemma14_sign_g₃ (n k m : ℕ) :
    Perm.sign (g₃ n k m) = (-1 : ℤˣ) ^ (m + 3) := by
  have hCycle := g₃_isCycle n k m
  have hCard := g₃_support_card n k m
  rw [lemma13_cycle_sign hCycle (by omega : (g₃ n k m).support.card ≥ 1)]
  rw [hCard]
  congr 1
  omega

/-- Helper: (-1)^(x+3) = 1 ↔ x is odd -/
private theorem neg_one_pow_add_three_eq_one_iff (x : ℕ) :
    (-1 : ℤˣ) ^ (x + 3) = 1 ↔ Odd x := by
  have h3 : (-1 : ℤˣ) ^ 3 = -1 := by decide
  rw [pow_add, h3, mul_neg, mul_one, neg_eq_iff_eq_neg]
  rw [neg_one_pow_eq_neg_one_iff_odd (by decide : (-1 : ℤˣ) ≠ 1)]

/-- g₁ is an even permutation iff n is odd -/
theorem g₁_even_iff_n_odd (n k m : ℕ) :
    Perm.sign (g₁ n k m) = 1 ↔ Odd n := by
  rw [lemma14_sign_g₁, neg_one_pow_add_three_eq_one_iff]

/-- g₂ is an even permutation iff k is odd -/
theorem g₂_even_iff_k_odd (n k m : ℕ) :
    Perm.sign (g₂ n k m) = 1 ↔ Odd k := by
  rw [lemma14_sign_g₂, neg_one_pow_add_three_eq_one_iff]

/-- g₃ is an even permutation iff m is odd -/
theorem g₃_even_iff_m_odd (n k m : ℕ) :
    Perm.sign (g₃ n k m) = 1 ↔ Odd m := by
  rw [lemma14_sign_g₃, neg_one_pow_add_three_eq_one_iff]

-- ============================================
-- SECTION 5: ALL GENERATORS EVEN IFF ALL ODD
-- ============================================

/-- All three generators are even permutations iff n, k, m are all odd -/
theorem all_generators_even_iff (n k m : ℕ) :
    (Perm.sign (g₁ n k m) = 1 ∧ Perm.sign (g₂ n k m) = 1 ∧ Perm.sign (g₃ n k m) = 1) ↔
    (Odd n ∧ Odd k ∧ Odd m) := by
  rw [g₁_even_iff_n_odd, g₂_even_iff_k_odd, g₃_even_iff_m_odd]

end LemmaFeld.GroupTheory.AF.SignAnalysis
