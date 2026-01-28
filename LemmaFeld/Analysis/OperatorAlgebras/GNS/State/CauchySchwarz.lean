/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.State.Positivity
import Mathlib.Algebra.QuadraticDiscriminant

/-!
# Cauchy-Schwarz Inequality for States (Weak Form)

This file proves the weak Cauchy-Schwarz inequality for states on C*-algebras.

## Main results

* `State.inner_mul_le_norm_mul_norm_weak` - |φ(b*a)|² ≤ 2 · φ(a*a) · φ(b*b)

## Proof strategy

The proof uses the standard quadratic discriminant argument:

1. **Quadratic setup**: For t : ℝ, expand φ((a + t·b)*(a + t·b)) ≥ 0
   This gives: φ(a*a) + 2t·Re(φ(b*a)) + t²·φ(b*b) ≥ 0

2. **Discriminant bound**: By `discrim_le_zero`, since the quadratic is ≥ 0 for all t:
   (2·Re(φ(b*a)))² - 4·φ(a*a)·φ(b*b) ≤ 0
   Hence: Re(φ(b*a))² ≤ φ(a*a)·φ(b*b)

3. **Imaginary part**: Apply same argument to (a + it·b) to get:
   Im(φ(b*a))² ≤ φ(a*a)·φ(b*b)

4. **Combine**: |φ(b*a)|² = Re² + Im² ≤ 2·φ(a*a)·φ(b*b)

The tight bound (without factor 2) is in `CauchySchwarzTight.lean`.
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### Helper lemmas for weak Cauchy-Schwarz -/

lemma cross_term_conj (a b : A) :
    φ (star a * b) = starRingEnd ℂ (φ (star b * a)) :=
  sesqForm_conj_symm φ b a

private lemma expand_star_add_real_smul (a b : A) (t : ℝ) :
    star (a + (t : ℂ) • b) * (a + (t : ℂ) • b) =
    star a * a + (t : ℂ) • (star a * b + star b * a) + (t^2 : ℂ) • (star b * b) := by
  have h : star ((t : ℂ) • b) = (t : ℂ) • star b := by
    rw [star_smul, Complex.star_def, Complex.conj_ofReal]
  rw [star_add, h]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
  rw [smul_add, smul_smul]; simp only [sq]; rw [smul_add]; abel

private lemma cross_term_re (a b : A) :
    (φ (star a * b + star b * a)).re = 2 * (φ (star b * a)).re := by
  rw [φ.map_add, cross_term_conj φ a b, starRingEnd_apply, Complex.star_def]
  simp only [Complex.add_re, Complex.conj_re]; ring

private lemma cross_term_im (a b : A) :
    (φ (star a * b + star b * a)).im = 0 := by
  rw [φ.map_add, cross_term_conj φ a b, starRingEnd_apply, Complex.star_def]
  simp only [Complex.add_im, Complex.conj_im]; ring

private lemma quadratic_form (a b : A) (t : ℝ) :
    (φ (star (a + (t : ℂ) • b) * (a + (t : ℂ) • b))).re =
    (φ (star b * b)).re * t^2 + 2 * (φ (star b * a)).re * t + (φ (star a * a)).re := by
  rw [expand_star_add_real_smul a b t, φ.map_add, φ.map_add, φ.map_smul, φ.map_smul]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
             mul_zero, sub_zero, φ.apply_star_mul_self_im]
  rw [cross_term_re φ a b, cross_term_im φ a b, mul_zero, sub_zero]
  simp only [sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]; ring

private lemma re_sq_le (a b : A) :
    (φ (star b * a)).re ^ 2 ≤ (φ (star a * a)).re * (φ (star b * b)).re := by
  have hquad : ∀ t : ℝ, 0 ≤ (φ (star b * b)).re * (t * t) +
                         2 * (φ (star b * a)).re * t + (φ (star a * a)).re := by
    intro t
    have := quadratic_form φ a b t
    have hnn := φ.apply_star_mul_self_nonneg (a + (t : ℂ) • b)
    rw [this] at hnn; simp only [sq] at hnn; linarith
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith [sq_nonneg (φ (star b * a)).re]

private lemma star_I_smul (b : A) : star (Complex.I • b) = (-Complex.I) • star b := by
  rw [star_smul, Complex.star_def, Complex.conj_I]

private lemma re_star_I_smul_mul (a b : A) :
    (φ (star (Complex.I • b) * a)).re = (φ (star b * a)).im := by
  rw [star_I_smul, smul_mul_assoc, φ.map_smul]
  simp only [neg_mul, Complex.neg_re, Complex.I_mul]; ring

private lemma apply_star_I_smul_I_smul (b : A) :
    φ (star (Complex.I • b) * (Complex.I • b)) = φ (star b * b) := by
  rw [star_I_smul, smul_mul_assoc, mul_smul_comm, smul_smul]
  have : (-Complex.I) * Complex.I = 1 := by simp [Complex.I_mul_I]
  rw [this, one_smul]

private lemma im_sq_le (a b : A) :
    (φ (star b * a)).im ^ 2 ≤ (φ (star a * a)).re * (φ (star b * b)).re := by
  have h := re_sq_le φ a (Complex.I • b)
  rw [re_star_I_smul_mul φ a b, apply_star_I_smul_I_smul] at h
  exact h

/-- The Cauchy-Schwarz inequality for states (weak form with factor 2):
    |φ(b*a)|² ≤ 2 · φ(a*a) · φ(b*b).

    This is sufficient for proving the null space is closed under addition. -/
theorem inner_mul_le_norm_mul_norm_weak (a b : A) :
    Complex.normSq (φ (star b * a)) ≤ 2 * (φ (star a * a)).re * (φ (star b * b)).re := by
  have hre := re_sq_le φ a b
  have him := im_sq_le φ a b
  rw [Complex.normSq_apply]
  have := add_le_add hre him
  linarith

end State
