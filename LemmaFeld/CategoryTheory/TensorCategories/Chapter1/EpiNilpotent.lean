/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Epi Nilpotent Endomorphisms

This file proves that an epi nilpotent endomorphism on an object implies the object is zero.

## Main Results

* `isZero_of_epi_pow_eq_zero`: If g : End Y is epi and g ^ n = 0 for some n > 0, then Y is zero.

## References

* §1.5 of Etingof et al. "Tensor Categories" (AMS 2015)
-/

noncomputable section

namespace CategoryTheory

open CategoryTheory

variable {C : Type*} [Category C] [Abelian C]
variable {Y : C} (g : End Y) [hg : Epi g]

/-- An epi endomorphism that composes to zero implies the source is zero.
Key lemma: if g ^ n = 0 and g is epi, then g ^ (n-1) = 0, and by induction, Y is zero. -/
theorem isZero_of_epi_pow_eq_zero (n : ℕ) (hn : 0 < n) (heq : g ^ n = 0) : IsZero Y := by
  induction n with
  | zero => exact (Nat.not_lt_zero 0 hn).elim
  | succ m ih =>
    cases m with
    | zero =>
      -- g^1 = g = 0, and g is epi, so Y is zero
      rw [pow_one] at heq
      exact IsZero.of_epi_eq_zero g heq
    | succ k =>
      -- g^(k+2) = g^(k+1) * g = g ≫ g^(k+1) = 0
      -- Since g is epi, g^(k+1) = 0
      -- Note: End multiplication is x * y = y ≫ x, so g^(k+1) * g = g ≫ g^(k+1)
      have hpow : g^(k + 2) = g^(k + 1) * g := pow_succ g (k + 1)
      rw [hpow, End.mul_def] at heq
      -- Now heq : g ≫ g^(k+1) = 0
      have heq' : g^(k + 1) = 0 := by
        have h0 : g ≫ (0 : Y ⟶ Y) = 0 := comp_zero
        rw [← h0] at heq
        exact (cancel_epi g).mp heq
      exact ih (Nat.succ_pos k) heq'

end CategoryTheory
