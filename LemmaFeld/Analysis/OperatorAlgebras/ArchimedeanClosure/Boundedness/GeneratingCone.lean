/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Algebra.QuadraticModule
import Mathlib.Algebra.Star.SelfAdjoint

/-! # M ∩ (A₀)_sa is Generating

This file proves that the intersection of the quadratic module M with the
self-adjoint part generates the self-adjoint part as differences.

## Main results

* `selfAdjoint_decomp` - x = ¼(1+x)² - ¼(1-x)² for self-adjoint x
* `decomp_terms_in_M` - Both terms are in M
* `quadraticModule_selfAdjoint_generating` - M ∩ (A₀)_sa generates (A₀)_sa

## Proof strategy

For any self-adjoint x, use the algebraic identity:
  x = ¼(1+x)² - ¼(1-x)²

Since (1+x)² = star(1+x)*(1+x) when x is self-adjoint, both terms are in M.
-/

namespace FreeStarAlgebra

variable {n : ℕ}

/-- Self-adjoint part of FreeStarAlgebra as a set. -/
def selfAdjointPart (n : ℕ) : Set (FreeStarAlgebra n) :=
  { a | IsSelfAdjoint a }

/-- 1 + x is self-adjoint when x is. -/
theorem isSelfAdjoint_one_add {x : FreeStarAlgebra n} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (1 + x) := by
  unfold IsSelfAdjoint at *
  simp [star_add, hx]

/-- 1 - x is self-adjoint when x is. -/
theorem isSelfAdjoint_one_sub {x : FreeStarAlgebra n} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (1 - x) := by
  unfold IsSelfAdjoint at *
  simp [star_sub, hx]

/-- For self-adjoint a, star a * a = a * a. -/
theorem star_mul_self_eq_sq {a : FreeStarAlgebra n} (ha : IsSelfAdjoint a) :
    star a * a = a * a := by
  rw [ha.star_eq]

/-- a² is self-adjoint when a is. -/
theorem isSelfAdjoint_sq {a : FreeStarAlgebra n} (ha : IsSelfAdjoint a) :
    IsSelfAdjoint (a * a) := by
  unfold IsSelfAdjoint
  simp [star_mul, ha.star_eq]

/-- Key algebraic identity: x = ¼(1+x)² - ¼(1-x)² for self-adjoint x.

This is a pure algebraic identity. The calculation:
- (1+x)² = 1 + 2x + x²
- (1-x)² = 1 - 2x + x²
- (1+x)² - (1-x)² = 4x
- ¼(1+x)² - ¼(1-x)² = x

TODO: The Lean proof requires careful handling of scalar multiplication
types. The identity is mathematically straightforward. -/
theorem selfAdjoint_decomp {x : FreeStarAlgebra n} (hx : IsSelfAdjoint x) :
    x = (1/4 : ℝ) • (star (1 + x) * (1 + x)) -
        (1/4 : ℝ) • (star (1 - x) * (1 - x)) := by
  -- Use self-adjointness: star(1+x) = 1+x, star(1-x) = 1-x
  have h1 : star (1 + x) = 1 + x := (isSelfAdjoint_one_add hx).star_eq
  have h2 : star (1 - x) = 1 - x := (isSelfAdjoint_one_sub hx).star_eq
  rw [h1, h2, ← smul_sub]
  -- Build Commute hypothesis: (1+x) and (1-x) commute
  have hcomm : Commute (1 + x) (1 - x) := by
    apply Commute.add_left
    · exact (Commute.one_left _).sub_right (Commute.one_left x)
    · exact (Commute.one_right x).sub_right (Commute.refl x)
  -- Apply difference of squares: a²-b² = (a+b)(a-b) when a,b commute
  rw [hcomm.mul_self_sub_mul_self_eq]
  -- Simplify (1+x) + (1-x) = 2
  have sum_eq : (1 : FreeStarAlgebra n) + x + (1 - x) = 2 := by
    have h : (1 : FreeStarAlgebra n) + x + (1 - x) = (2 : ℕ) • (1 : FreeStarAlgebra n) := by abel
    rw [h, nsmul_eq_mul, Nat.cast_ofNat, mul_one]
  -- Simplify (1+x) - (1-x) = 2*x
  have diff_eq : (1 : FreeStarAlgebra n) + x - (1 - x) = 2 * x := by
    have h : (1 : FreeStarAlgebra n) + x - (1 - x) = (2 : ℕ) • x := by abel
    rw [h, nsmul_eq_mul, Nat.cast_ofNat]
  rw [sum_eq, diff_eq]
  -- Simplify (1/4) • (2 * (2 * x)) = x
  simp only [← mul_assoc]
  have h_four : (2 : FreeStarAlgebra n) * 2 = 4 := by norm_num
  rw [h_four]
  have h_scalar : (4 : FreeStarAlgebra n) * x = (4 : ℝ) • x := by
    rw [Algebra.smul_def]; rfl
  rw [h_scalar, smul_smul]
  norm_num

/-- Both terms in the decomposition are in M (for any x). -/
theorem decomp_terms_in_M (x : FreeStarAlgebra n) :
    star (1 + x) * (1 + x) ∈ QuadraticModule n ∧
    star (1 - x) * (1 - x) ∈ QuadraticModule n :=
  ⟨star_mul_self_mem (1 + x), star_mul_self_mem (1 - x)⟩

/-- star(1+x)*(1+x) is self-adjoint when x is. -/
theorem decomp_term_selfAdjoint_add {x : FreeStarAlgebra n} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (star (1 + x) * (1 + x)) := by
  have h := isSelfAdjoint_one_add hx
  rw [h.star_eq]
  exact isSelfAdjoint_sq h

/-- star(1-x)*(1-x) is self-adjoint when x is. -/
theorem decomp_term_selfAdjoint_sub {x : FreeStarAlgebra n} (hx : IsSelfAdjoint x) :
    IsSelfAdjoint (star (1 - x) * (1 - x)) := by
  have h := isSelfAdjoint_one_sub hx
  rw [h.star_eq]
  exact isSelfAdjoint_sq h

/-- M ∩ (A₀)_sa generates (A₀)_sa as differences. -/
theorem quadraticModule_selfAdjoint_generating :
    ∀ x ∈ selfAdjointPart n,
      ∃ m₁ ∈ QuadraticModule n ∩ selfAdjointPart n,
      ∃ m₂ ∈ QuadraticModule n ∩ selfAdjointPart n,
        x = (1/4 : ℝ) • m₁ - (1/4 : ℝ) • m₂ := by
  intro x hx
  -- m₁ = (1+x)², m₂ = (1-x)²
  refine ⟨star (1 + x) * (1 + x), ?_, star (1 - x) * (1 - x), ?_, ?_⟩
  · exact ⟨(decomp_terms_in_M x).1, decomp_term_selfAdjoint_add hx⟩
  · exact ⟨(decomp_terms_in_M x).2, decomp_term_selfAdjoint_sub hx⟩
  · exact selfAdjoint_decomp hx

end FreeStarAlgebra
