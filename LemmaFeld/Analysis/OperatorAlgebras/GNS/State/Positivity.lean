/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.State.Basic
import Mathlib.Algebra.Star.SelfAdjoint
import Mathlib.Algebra.Star.Module

/-!
# Positivity Properties of States

This file proves key positivity properties of states on C*-algebras.

## Main results

* `State.map_star` - φ(a*) = conj(φ(a))
* `State.apply_real_of_isSelfAdjoint` - φ(a) is real when a is self-adjoint
* `State.apply_star_mul_self_real` - φ(a*a) is a real number (Im = 0)

## Implementation notes

The key insight is that for states, the sesquilinear form ⟨a, b⟩ = φ(b*a) satisfies
conjugate symmetry: ⟨a, b⟩ = conj(⟨b, a⟩). This is equivalent to map_star.

The proof uses the polarization identity and the fact that φ(a*a) is real
(not just has non-negative real part), which is part of the State definition.
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### Polarization identity and conjugate symmetry -/

/-- The sesquilinear form defined by a state: ⟨a, b⟩ = φ(b*a). -/
def sesqForm (a b : A) : ℂ := φ (star b * a)

theorem sesqForm_self (a : A) : φ.sesqForm a a = φ (star a * a) := rfl

/-- The sesquilinear form is real on the diagonal. -/
theorem sesqForm_self_im (a : A) : (φ.sesqForm a a).im = 0 :=
  φ.apply_star_mul_self_im a

/-! #### Helper lemmas for conjugate symmetry proof -/

private lemma expand_star_add_mul_add (x y : A) :
    star (x + y) * (x + y) = star x * x + star x * y + star y * x + star y * y := by
  simp only [star_add, add_mul, mul_add]; abel

private lemma expand_star_add_I_smul (x y : A) :
    star (x + Complex.I • y) * (x + Complex.I • y)
    = star x * x + star y * y + Complex.I • (star x * y - star y * x) := by
  have star_I_smul : star (Complex.I • y) = (-Complex.I) • star y := by
    rw [star_smul, Complex.star_def, Complex.conj_I]
  rw [star_add, star_I_smul]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add]
  have I_mul_neg_I : Complex.I * (-Complex.I) = (1 : ℂ) := by rw [mul_neg, Complex.I_mul_I, neg_neg]
  rw [smul_smul, I_mul_neg_I, one_smul, smul_sub]
  rw [show (-Complex.I) • (star y * x) = -(Complex.I • (star y * x)) from neg_smul _ _]; abel

private lemma sum_im_zero (x y : A) : (φ (star y * x + star x * y)).im = 0 := by
  have hD : star y * x + star x * y = star (x + y) * (x + y) - star x * x - star y * y := by
    rw [expand_star_add_mul_add]; abel
  rw [hD, φ.map_sub, φ.map_sub]; simp only [Complex.sub_im]
  rw [φ.apply_star_mul_self_im (x + y), φ.apply_star_mul_self_im x, φ.apply_star_mul_self_im y]
  ring

private lemma diff_smul_I_im_zero (x y : A) :
    (φ (Complex.I • (star x * y - star y * x))).im = 0 := by
  have hIE : Complex.I • (star x * y - star y * x)
           = star (x + Complex.I • y) * (x + Complex.I • y) - star x * x - star y * y := by
    rw [expand_star_add_I_smul]; abel
  rw [hIE, φ.map_sub, φ.map_sub]; simp only [Complex.sub_im]
  rw [φ.apply_star_mul_self_im, φ.apply_star_mul_self_im x, φ.apply_star_mul_self_im y]
  ring

/-- Conjugate symmetry of the sesquilinear form: ⟨x, y⟩ = conj(⟨y, x⟩).

The proof uses the polarization identity. The key insight is that because
φ(z*z) is real for all z (part of the State axioms), the sesquilinear form
defined by φ is actually symmetric AND real-valued, making conjugate symmetry
automatic.

Specifically, the polarization identity shows:
  4φ(y*x) = R₁ - R₂ + i(R₃ - R₄)
where Rᵢ are real (diagonal terms). But the condition φ(z*z) ∈ ℝ for all z
implies R₃ = R₄, making φ(y*x) real. Combined with symmetry from the
polarization structure, conjugate symmetry follows. -/
theorem sesqForm_conj_symm (x y : A) :
    φ.sesqForm x y = starRingEnd ℂ (φ.sesqForm y x) := by
  -- Let P = φ(star y * x), Q = φ(star x * y). Goal: P = conj(Q)
  unfold sesqForm
  set P := φ (star y * x) with hP_def
  set Q := φ (star x * y) with hQ_def
  -- From sum_im_zero: (P + Q).im = 0, so P.im = -Q.im
  have hSum := sum_im_zero φ x y
  rw [φ.map_add] at hSum; simp only [Complex.add_im] at hSum
  -- From diff_smul_I_im_zero: (I * (Q - P)).im = 0
  -- Since (I * z).im = z.re, we get (Q - P).re = 0, i.e., P.re = Q.re
  have hDiff := diff_smul_I_im_zero φ x y
  rw [φ.map_smul, φ.map_sub] at hDiff
  have key : (Complex.I * (Q - P)).im = 0 := hDiff
  rw [Complex.I_mul, Complex.sub_re] at key
  -- Now: P.re = Q.re and P.im = -Q.im, which means P = conj(Q)
  apply Complex.ext
  · simp only [Complex.conj_re]; linarith
  · simp only [Complex.conj_im]; linarith

/-! ### Star preservation -/

/-- States preserve the star operation: φ(a*) = conj(φ(a)).

This is equivalent to conjugate symmetry of the sesquilinear form
with the second argument being 1. -/
theorem map_star (a : A) : φ (star a) = starRingEnd ℂ (φ a) := by
  have h : φ.sesqForm 1 a = starRingEnd ℂ (φ.sesqForm a 1) := sesqForm_conj_symm φ 1 a
  simp only [sesqForm, star_one, one_mul, mul_one] at h
  exact h

/-- Alternative form: star of φ(a) equals φ(star a). -/
theorem star_apply (a : A) : star (φ a) = φ (star a) := by
  rw [Complex.star_def, map_star, starRingEnd_apply, Complex.star_def]

/-! ### Self-adjoint elements map to real values -/

/-- For self-adjoint elements, φ(a) is real.
    This follows from map_star: φ(a) = φ(a*) = conj(φ(a)). -/
theorem apply_real_of_isSelfAdjoint {a : A} (ha : IsSelfAdjoint a) :
    (φ a).im = 0 := by
  have h1 : φ a = starRingEnd ℂ (φ a) := by
    rw [← map_star, ha.star_eq]
  rw [starRingEnd_apply, Complex.star_def] at h1
  have h2 := congrArg Complex.im h1
  simp only [Complex.conj_im] at h2
  -- h2 : (φ a).im = -(φ a).im, so (φ a).im = 0
  linarith

/-- For self-adjoint a, φ(a) equals its real part. -/
theorem apply_eq_re_of_isSelfAdjoint {a : A} (ha : IsSelfAdjoint a) :
    φ a = (φ a).re := by
  apply Complex.ext
  · rfl
  · simp [apply_real_of_isSelfAdjoint φ ha]

/-! ### Consequences -/

/-- The absolute value squared of φ(a) equals φ(a) · conj(φ(a)). -/
theorem normSq_apply (a : A) : Complex.normSq (φ a) = φ a * starRingEnd ℂ (φ a) := by
  rw [Complex.normSq_eq_conj_mul_self]
  ring

end State
