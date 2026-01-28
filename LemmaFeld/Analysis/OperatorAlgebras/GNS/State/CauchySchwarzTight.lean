/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.State.CauchySchwarz

/-!
# Cauchy-Schwarz Inequality for States (Tight Form)

This file proves the tight Cauchy-Schwarz inequality for states on C*-algebras.

## Main results

* `State.inner_mul_le_norm_mul_norm` - |φ(b*a)|² ≤ φ(a*a) · φ(b*b)
* `State.sesqForm_abs_sq_le` - Same with sesqForm notation
* `State.apply_star_mul_eq_zero_of_apply_star_self_eq_zero` - φ(a*a) = 0 ⟹ φ(b*a) = 0

## Proof strategy

The tight bound uses the complex λ-optimization argument:
For μ = -φ(b*a)/φ(b*b), the positivity φ((a + μ·b)*(a + μ·b)) ≥ 0 expands to
φ(a*a).re - |φ(b*a)|²/φ(b*b).re ≥ 0 when φ(b*b).re > 0.
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### Helper lemmas for tight Cauchy-Schwarz -/

/-- Expansion of star(a + μ•b) * (a + μ•b) for complex μ -/
private lemma expand_star_add_smul (a b : A) (μ : ℂ) :
    star (a + μ • b) * (a + μ • b) =
    star a * a + μ • (star a * b) + starRingEnd ℂ μ • (star b * a) +
    (Complex.normSq μ : ℂ) • (star b * b) := by
  have hμ : star (μ • b) = starRingEnd ℂ μ • star b := star_smul μ b
  rw [star_add, hμ]
  simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm, smul_add, smul_smul]
  have : μ * starRingEnd ℂ μ = Complex.normSq μ := Complex.mul_conj μ
  rw [this]; abel

/-- Key algebraic identity: for μ = -c/d where d is real positive,
    the cross-term sum μ*conj(c) + conj(μ)*c + |μ|²*d = -|c|²/d -/
private lemma cross_term_opt_identity (c d : ℂ) (hd_im : d.im = 0) (hd_re_pos : 0 < d.re) :
    (-c / d) * (starRingEnd ℂ c) + (starRingEnd ℂ (-c / d)) * c +
    Complex.normSq (-c / d) * d = -Complex.normSq c / d := by
  have hd_real : d = (d.re : ℂ) := Complex.ext rfl hd_im
  have hd_re_ne : (d.re : ℂ) ≠ 0 := by
    intro h; have : d.re = 0 := Complex.ofReal_eq_zero.mp h; linarith
  rw [hd_real, map_div₀, Complex.conj_ofReal d.re, Complex.normSq_div,
      Complex.normSq_neg, Complex.normSq_ofReal, RingHom.map_neg]
  -- Simplify d.re² * (|c|² / d.re²) = |c|²
  have hsimpl : d.re ^ 2 * (Complex.normSq c / d.re ^ 2) = Complex.normSq c := by
    field_simp [ne_of_gt hd_re_pos]
  have h2 : (d.re : ℂ) ^ 2 * (↑(Complex.normSq c / d.re ^ 2)) = ↑(Complex.normSq c) := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, hsimpl]
  field_simp [hd_re_ne]; rw [h2, Complex.mul_conj c]; ring

/-- The Cauchy-Schwarz inequality for states (tight form):
    |φ(b*a)|² ≤ φ(a*a) · φ(b*b). -/
theorem inner_mul_le_norm_mul_norm (a b : A) :
    Complex.normSq (φ (star b * a)) ≤ (φ (star a * a)).re * (φ (star b * b)).re := by
  rcases eq_or_lt_of_le (φ.apply_star_mul_self_nonneg b) with hbb | hbb
  · -- Case: φ(b*b).re = 0. Weak C-S gives |φ(b*a)|² ≤ 0
    have h := inner_mul_le_norm_mul_norm_weak φ a b
    simp only [← hbb, mul_zero] at h ⊢
    linarith [Complex.normSq_nonneg (φ (star b * a))]
  · -- Case: φ(b*b).re > 0. Complex optimization gives tight bound
    set c := φ (star b * a) with hc_def
    set d := φ (star b * b) with hd_def
    have hd_im : d.im = 0 := φ.apply_star_mul_self_im b
    let μ := -c / d
    -- Positivity gives: φ((a + μ•b)*(a + μ•b)).re ≥ 0
    have hpos := φ.apply_star_mul_self_nonneg (a + μ • b)
    -- Expand and apply φ
    rw [expand_star_add_smul, φ.map_add, φ.map_add, φ.map_add,
        φ.map_smul, φ.map_smul, φ.map_smul] at hpos
    -- Use conjugate symmetry: φ(star a * b) = conj(c)
    have hconj : φ (star a * b) = starRingEnd ℂ c := sesqForm_conj_symm φ b a
    rw [hconj, ← hc_def, ← hd_def] at hpos
    -- Apply cross_term_opt_identity: the cross terms equal -|c|²/d
    have hid := cross_term_opt_identity c d hd_im hbb
    -- Unfold μ = -c/d in hpos, then apply hid
    simp only [show μ = -c / d from rfl] at hpos
    -- Reassociate to match hid pattern
    have hpos' : 0 ≤ (φ (star a * a) + (-c / d * (starRingEnd ℂ) c +
        (starRingEnd ℂ) (-c / d) * c + ↑(Complex.normSq (-c / d)) * d)).re := by
      convert hpos using 2; ring
    rw [hid] at hpos'
    -- Now hpos': 0 ≤ (φ(a*a) + (-|c|²/d)).re
    have hd_real : d = (d.re : ℂ) := Complex.ext rfl hd_im
    rw [hd_real] at hpos'
    -- Simplify: ((-|c|² : ℂ) / d.re).re = -|c|² / d.re
    have hneg_re : ((-↑(Complex.normSq c) : ℂ) / ↑d.re).re = -Complex.normSq c / d.re := by
      rw [Complex.div_ofReal_re, Complex.neg_re, Complex.ofReal_re]
    rw [Complex.add_re, hneg_re] at hpos'
    -- From hpos': (φ(a*a)).re - |c|²/d.re ≥ 0, multiply by d.re > 0
    have hmul := mul_le_mul_of_nonneg_right hpos' (le_of_lt hbb)
    simp only [zero_mul] at hmul
    -- Expand: (a + b) * c = a * c + b * c
    rw [add_mul] at hmul
    have hdiv : (-Complex.normSq c / d.re) * d.re = -Complex.normSq c :=
      div_mul_cancel₀ (-Complex.normSq c) (ne_of_gt hbb)
    rw [hdiv] at hmul
    linarith

/-- Cauchy-Schwarz with sesquilinear form notation. -/
theorem sesqForm_abs_sq_le (a b : A) :
    Complex.normSq (φ.sesqForm a b) ≤ (φ.sesqForm a a).re * (φ.sesqForm b b).re :=
  inner_mul_le_norm_mul_norm φ a b

/-! ### Consequences for the null space -/

/-- If φ(a*a) = 0, then φ(b*a) = 0 for all b.
    This is a direct consequence of Cauchy-Schwarz. -/
theorem apply_star_mul_eq_zero_of_apply_star_self_eq_zero {a : A}
    (ha : φ (star a * a) = 0) (b : A) : φ (star b * a) = 0 := by
  have h := inner_mul_le_norm_mul_norm φ a b
  simp only [ha, Complex.zero_re, zero_mul] at h
  exact Complex.normSq_eq_zero.mp (le_antisymm h (Complex.normSq_nonneg _))

-- Note: `null_space_left_ideal` (ba ∈ N_φ when a ∈ N_φ) belongs in NullSpace/LeftIdeal.lean.
-- Its proof uses boundedness of the state, not Cauchy-Schwarz.
-- See docs/GNS/phases/02_nullspace.md for the planned structure.

end State
