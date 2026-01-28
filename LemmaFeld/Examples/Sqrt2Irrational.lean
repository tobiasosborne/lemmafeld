/-
  Proof that √2 is irrational using Mathlib
-/
import Mathlib.NumberTheory.Real.Irrational

-- The direct theorem from Mathlib
theorem sqrt2_irrational : Irrational (Real.sqrt 2) := irrational_sqrt_two

-- Alternative: derive it from the general theorem that √p is irrational for prime p
theorem sqrt2_irrational' : Irrational (Real.sqrt 2) :=
  Nat.Prime.irrational_sqrt Nat.prime_two

-- A more manual proof: 2 is not a perfect square
theorem sqrt2_irrational'' : Irrational (Real.sqrt 2) := by
  rw [irrational_sqrt_ofNat_iff]
  intro ⟨n, hn⟩
  -- n * n = 2 is impossible for natural numbers
  -- n = 0 gives 0, n = 1 gives 1, n ≥ 2 gives ≥ 4
  have h1 : n ≤ 1 ∨ n ≥ 2 := by omega
  rcases h1 with h | h
  · interval_cases n <;> simp_all
  · have : n * n ≥ 4 := by nlinarith
    omega

