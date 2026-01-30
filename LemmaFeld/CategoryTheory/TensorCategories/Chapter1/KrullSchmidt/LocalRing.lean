/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.RingTheory.LocalRing.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Krull-Schmidt: Local Ring Lemmas

Lemmas about local rings needed for the exchange lemma:
- In a local ring, if a + b is a unit, then a or b is a unit
- If a finite sum equals 1 in a local ring, some summand is a unit
-/

namespace LemmaFeld.TensorCategories.Chapter1

/-- In a local ring, if a + b is a unit, then a is a unit or b is a unit.
This is the contrapositive form of the local ring property. -/
lemma nonunits_add_of_local {R : Type*} [Ring R] [IsLocalRing R] {a b : R}
    (ha : ¬IsUnit a) (hb : ¬IsUnit b) : ¬IsUnit (a + b) := by
  intro h
  obtain ⟨u, hu⟩ := h
  have hinv : u⁻¹ * a + u⁻¹ * b = 1 := by
    rw [← mul_add, ← hu]; exact Units.inv_mul u
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hinv with h | h
  · exact ha ((Units.isUnit_units_mul u⁻¹ a).mp h)
  · exact hb ((Units.isUnit_units_mul u⁻¹ b).mp h)

/-- In a local ring, if the sum of a finite family equals 1, then some element is a unit. -/
lemma exists_isUnit_of_finsum_eq_one {R : Type*} [Ring R] [IsLocalRing R] {n : ℕ}
    (f : Fin n → R) (hf : ∑ i, f i = 1) : ∃ i, IsUnit (f i) := by
  induction n with
  | zero => simp at hf
  | succ n ih =>
    rw [Fin.sum_univ_succ] at hf
    by_cases h0 : IsUnit (f 0)
    · exact ⟨0, h0⟩
    · have hrest : IsUnit (∑ i : Fin n, f i.succ) := by
        by_contra hnu
        have : ¬IsUnit (f 0 + ∑ i : Fin n, f i.succ) := nonunits_add_of_local h0 hnu
        rw [hf] at this; exact this isUnit_one
      obtain ⟨u, hu⟩ := hrest
      have hscaled : ∑ i : Fin n, (u⁻¹ * f i.succ) = 1 := by
        rw [← Finset.mul_sum, ← hu]; exact Units.inv_mul u
      obtain ⟨j, hj⟩ := ih (fun i => u⁻¹ * f i.succ) hscaled
      exact ⟨j.succ, (Units.isUnit_units_mul u⁻¹ (f j.succ)).mp hj⟩

end LemmaFeld.TensorCategories.Chapter1
