/-
  Proofs that there are infinitely many primes using Mathlib
-/
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Prime.Factorial

-- Direct: The set of primes is infinite
theorem primes_infinite : {p : ℕ | p.Prime}.Infinite :=
  Nat.infinite_setOf_prime

-- Alternative formulation: For any n, there exists a prime p ≥ n
theorem exists_prime_ge (n : ℕ) : ∃ p, n ≤ p ∧ p.Prime :=
  Nat.exists_infinite_primes n

-- The set of primes is not bounded above
theorem primes_unbounded : ¬BddAbove {p : ℕ | p.Prime} :=
  Nat.not_bddAbove_setOf_prime

-- Euclid's proof: For any n, n! + 1 has a prime factor > n
theorem euclid_infinite_primes (n : ℕ) : ∃ p, n < p ∧ p.Prime := by
  -- Consider n! + 1, which is > 1
  let m := n.factorial + 1
  have hm : m ≠ 1 := by
    simp only [m]
    have := Nat.factorial_pos n
    omega
  -- m has a smallest prime factor
  use m.minFac
  constructor
  · -- Show n < m.minFac
    by_contra h
    push_neg at h
    -- If minFac ≤ n, then minFac | n!
    have hp := Nat.minFac_prime hm
    have hdiv_fac : m.minFac ∣ n.factorial :=
      (Nat.Prime.dvd_factorial hp).mpr h
    -- But minFac | m = n! + 1
    have hdiv_m : m.minFac ∣ m := Nat.minFac_dvd m
    -- So minFac | (n! + 1) - n! = 1
    have hdiv_one : m.minFac ∣ 1 := by
      have hsub : m.minFac ∣ m - n.factorial := Nat.dvd_sub hdiv_m hdiv_fac
      simp only [m, Nat.add_sub_cancel_left] at hsub
      exact hsub
    -- But minFac ≥ 2, contradiction
    have hge2 := hp.two_le
    have heq1 := Nat.eq_one_of_dvd_one hdiv_one
    omega
  · -- m.minFac is prime
    exact Nat.minFac_prime hm

