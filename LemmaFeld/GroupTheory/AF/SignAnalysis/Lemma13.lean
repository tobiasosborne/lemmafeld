/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Lemma 13: Cycle Sign

An l-cycle in Sₙ has sign (-1)^{l-1}.

## Main Results

* `lemma13_cycle_sign` - Sign of an l-cycle is (-1)^(l-1)

## Mathlib Reference

Mathlib provides `Equiv.Perm.IsCycle.sign` which states that for a cycle f,
`sign f = -(-1)^(f.support.card)`.

Since support.card = l for an l-cycle, and -(-1)^l = (-1)^(l+1) = (-1)^(l-1),
this is equivalent to our statement.

## Reference

See `examples/lemmas/lemma13_cycle_sign.md` for the natural language proof.
-/

namespace LemmaFeld.GroupTheory.AF.SignAnalysis

open Equiv Equiv.Perm

-- ============================================
-- SECTION 1: MATHLIB'S CYCLE SIGN THEOREM
-- ============================================

/-- Mathlib's cycle sign theorem: For a cycle f, sign f = -(-1)^(support.card).
    This is `Equiv.Perm.IsCycle.sign`. -/
theorem cycle_sign_mathlib {α : Type*} [DecidableEq α] [Fintype α]
    {f : Perm α} (hf : f.IsCycle) :
    Perm.sign f = -(-1 : ℤˣ) ^ f.support.card :=
  hf.sign

-- ============================================
-- SECTION 2: EQUIVALENCE OF FORMULATIONS
-- ============================================

/-- Key identity: -(-1)^n = (-1)^(n+1) -/
theorem neg_neg_one_pow (n : ℕ) : -(-1 : ℤˣ) ^ n = (-1) ^ (n + 1) := by
  simp [pow_succ]

/-- Key identity: (-1)^(n+1) = (-1)^(n-1) when n ≥ 1, since (-1)^2 = 1 -/
theorem neg_one_pow_add_one_eq_sub_one (n : ℕ) (hn : n ≥ 1) :
    (-1 : ℤˣ) ^ (n + 1) = (-1) ^ (n - 1) := by
  have h : n + 1 = n - 1 + 2 := by omega
  rw [h, pow_add]
  simp

-- ============================================
-- SECTION 3: MAIN THEOREM
-- ============================================

/-- **Lemma 13: Cycle Sign**

    An l-cycle has sign (-1)^{l-1}.

    The support of an l-cycle has cardinality l (the l elements it permutes).
    By mathlib's IsCycle.sign: sign = -(-1)^l = (-1)^(l+1) = (-1)^(l-1). -/
theorem lemma13_cycle_sign {α : Type*} [DecidableEq α] [Fintype α]
    {f : Perm α} (hf : f.IsCycle) (hl : f.support.card ≥ 1) :
    Perm.sign f = (-1 : ℤˣ) ^ (f.support.card - 1) := by
  rw [hf.sign, neg_neg_one_pow, neg_one_pow_add_one_eq_sub_one _ hl]

-- ============================================
-- SECTION 4: SPECIFIC CYCLE LENGTHS
-- ============================================

/-- For a 2-cycle (transposition), sign = -1 = (-1)^1 -/
theorem sign_of_transposition {α : Type*} [DecidableEq α] [Fintype α]
    (x y : α) (hxy : x ≠ y) :
    Perm.sign (Equiv.swap x y) = -1 :=
  Equiv.Perm.sign_swap hxy

/-- For a 3-cycle, sign = 1 = (-1)^2 (even permutation).
    Uses mathlib's IsThreeCycle.sign. -/
theorem sign_of_three_cycle {α : Type*} [DecidableEq α] [Fintype α]
    {f : Perm α} (hf : f.IsThreeCycle) :
    Perm.sign f = 1 :=
  hf.sign

-- ============================================
-- SECTION 5: EVEN/ODD CYCLE PARITY
-- ============================================

/-- Even-length cycles are odd permutations (sign = -1) -/
theorem even_cycle_is_odd {α : Type*} [DecidableEq α] [Fintype α]
    {f : Perm α} (hf : f.IsCycle) (heven : Even f.support.card) :
    Perm.sign f = -1 := by
  rw [hf.sign]
  obtain ⟨k, hk⟩ := heven
  simp [hk]

/-- Odd-length cycles are even permutations (sign = 1) -/
theorem odd_cycle_is_even {α : Type*} [DecidableEq α] [Fintype α]
    {f : Perm α} (hf : f.IsCycle) (hodd : Odd f.support.card) :
    Perm.sign f = 1 := by
  rw [hf.sign]
  obtain ⟨k, hk⟩ := hodd
  rw [hk, pow_add, pow_mul]
  simp

-- ============================================
-- SECTION 6: APPLICATIONS TO GENERATORS
-- ============================================

/-- Sign of a product of disjoint cycles is product of signs -/
theorem sign_disjoint_cycle_mul {α : Type*} [DecidableEq α] [Fintype α]
    (f g : Perm α) :
    Perm.sign (f * g) = Perm.sign f * Perm.sign g :=
  map_mul Perm.sign f g

/-- Generator sign depends on cycle structure -/
theorem generator_sign_from_cycles {α : Type*} [DecidableEq α] [Fintype α]
    (f : Perm α) : Perm.sign f ∈ ({1, -1} : Set ℤˣ) := by
  have h := Int.units_eq_one_or (Perm.sign f)
  rcases h with h | h <;> simp [h]

end LemmaFeld.GroupTheory.AF.SignAnalysis
