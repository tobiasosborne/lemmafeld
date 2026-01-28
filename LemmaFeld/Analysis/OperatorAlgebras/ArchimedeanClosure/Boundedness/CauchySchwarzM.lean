/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.State.MPositiveStateProps
import Mathlib.Algebra.QuadraticDiscriminant

/-! # Cauchy-Schwarz for M-Positive States

This file proves the Cauchy-Schwarz inequality for M-positive states.

## Main results

* `MPositiveState.sesqForm_symm` - φ(star a * b) = φ(star b * a)
* `MPositiveState.cauchy_schwarz` - φ(star b * a)² ≤ φ(star a * a) · φ(star b * b)

## Proof strategy

For ℝ-valued functionals, this is the standard quadratic discriminant argument:
1. For t : ℝ, φ(star(a + t·b) * (a + t·b)) ≥ 0 since squares are in M
2. Expand to get a quadratic in t with nonnegative values
3. Apply discriminant bound to get Cauchy-Schwarz
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} (φ : MPositiveState n)

/-- star (c • a) = c • star a for c : ℝ in FreeStarAlgebra.
This is proved via the algebra structure, not StarModule. -/
private lemma star_smul_real (c : ℝ) (a : FreeStarAlgebra n) :
    star (c • a) = c • star a := by
  rw [Algebra.smul_def, Algebra.smul_def, star_mul, FreeAlgebra.star_algebraMap]
  rw [Algebra.commutes]

/-- The sesquilinear form is symmetric: φ(star a * b) = φ(star b * a).

This follows from map_star: φ(star x) = φ(x) applied to x = star a * b. -/
theorem sesqForm_symm (a b : FreeStarAlgebra n) :
    φ (star a * b) = φ (star b * a) := by
  have h : star (star a * b) = star b * a := by simp [star_mul]
  calc φ (star a * b) = φ (star (star a * b)) := (φ.apply_star _).symm
    _ = φ (star b * a) := by rw [h]

/-- The cross term simplifies: φ(star a * b + star b * a) = 2 * φ(star b * a). -/
private lemma cross_term (a b : FreeStarAlgebra n) :
    φ (star a * b + star b * a) = 2 * φ (star b * a) := by
  rw [φ.map_add, sesqForm_symm]
  ring

/-- Quadratic nonneg: φ(star(a + t·b) * (a + t·b)) ≥ 0 expands to a quadratic in t. -/
private lemma quadratic_nonneg (a b : FreeStarAlgebra n) (t : ℝ) :
    0 ≤ φ (star b * b) * t^2 + 2 * φ (star b * a) * t + φ (star a * a) := by
  -- Start from positivity of squares
  have hval := φ.apply_star_mul_self_nonneg (a + t • b)
  -- Expand star(a + t·b) * (a + t·b)
  have hexp1 : star (a + t • b) = star a + t • star b := by
    rw [star_add, star_smul_real]
  -- (star a + t•star b)*(a + t•b) = star a*a + t•star a*b + t•star b*a + t²•star b*b
  have hexp2 : (star a + t • star b) * (a + t • b) =
      star a * a + t • (star a * b) + t • (star b * a) + (t * t) • (star b * b) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
    abel
  rw [hexp1, hexp2] at hval
  -- Apply φ
  simp only [φ.map_add, φ.map_smul] at hval
  -- Use sesqForm_symm: φ(star a * b) = φ(star b * a)
  have hsymm := sesqForm_symm φ a b
  -- Now we have: 0 ≤ φ(star a * a) + t * φ(star a * b) + t * φ(star b * a) + t² * φ(star b * b)
  -- = φ(star a * a) + 2t * φ(star b * a) + t² * φ(star b * b)
  calc 0 ≤ φ (star a * a) + t * φ (star a * b) + t * φ (star b * a) +
           t * t * φ (star b * b) := hval
    _ = φ (star a * a) + 2 * t * φ (star b * a) + t * t * φ (star b * b) := by
        rw [hsymm]; ring
    _ = φ (star b * b) * t^2 + 2 * φ (star b * a) * t + φ (star a * a) := by
        simp only [sq]; ring

/-- Cauchy-Schwarz: φ(star b * a)² ≤ φ(star a * a) · φ(star b * b).

This is the real inner product Cauchy-Schwarz inequality. -/
theorem cauchy_schwarz (a b : FreeStarAlgebra n) :
    φ (star b * a) ^ 2 ≤ φ (star a * a) * φ (star b * b) := by
  have hquad := quadratic_nonneg φ a b
  -- Rewrite for discrim_le_zero: need form c * (t * t) + b * t + a ≥ 0
  have hquad' : ∀ t : ℝ, 0 ≤ φ (star b * b) * (t * t) +
      2 * φ (star b * a) * t + φ (star a * a) := by
    intro t; have := hquad t; simp only [sq] at this; exact this
  have hdiscrim := discrim_le_zero hquad'
  unfold discrim at hdiscrim
  nlinarith [sq_nonneg (φ (star b * a))]

/-- Corollary: φ(a)² ≤ φ(star a * a) when φ(1) = 1. -/
theorem apply_sq_le (a : FreeStarAlgebra n) :
    φ a ^ 2 ≤ φ (star a * a) := by
  have h := cauchy_schwarz φ a 1
  simp only [star_one, one_mul, mul_one] at h
  rwa [φ.apply_one, mul_one] at h

/-- If φ(star a * a) = 0, then φ(star b * a) = 0 for all b.
    This is a direct consequence of Cauchy-Schwarz. -/
theorem apply_star_mul_eq_zero_of_apply_star_self_eq_zero {a : FreeStarAlgebra n}
    (ha : φ (star a * a) = 0) (b : FreeStarAlgebra n) : φ (star b * a) = 0 := by
  have hcs := cauchy_schwarz φ a b
  rw [ha, zero_mul] at hcs
  exact sq_eq_zero_iff.mp (le_antisymm hcs (sq_nonneg _))

/-- If φ(star a * a) = 0, then φ(star a * x) = 0 for all x.
    This is the "swapped" version, also from Cauchy-Schwarz with reversed arguments. -/
theorem apply_mul_star_eq_zero_of_apply_star_self_eq_zero {a : FreeStarAlgebra n}
    (ha : φ (star a * a) = 0) (x : FreeStarAlgebra n) : φ (star a * x) = 0 := by
  have hcs := cauchy_schwarz φ x a
  rw [ha, mul_zero] at hcs
  exact sq_eq_zero_iff.mp (le_antisymm hcs (sq_nonneg _))

end MPositiveState

end FreeStarAlgebra
