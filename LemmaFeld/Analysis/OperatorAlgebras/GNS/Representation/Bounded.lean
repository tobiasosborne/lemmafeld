/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Representation.PreRep
import LemmaFeld.Analysis.OperatorAlgebras.GNS.HilbertSpace.Completion
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# GNS Representation Boundedness

This file proves the pre-representation is bounded with `‖π(a)‖ ≤ ‖a‖`.

## Main results

* `State.gnsPreRep_norm_le` - `‖π(a)x‖ ≤ ‖a‖ * ‖x‖`

## Mathematical Background

The key inequality: In C*-algebras, `a*a ≤ ‖a‖² · 1` (from spectral theory).
Using positivity of states, this gives the operator norm bound.

## Status

PROVEN. States respect spectral ordering via `AddSubmonoid.closure_induction`.
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

-- Enable spectral order on C*-algebras for this file
attribute [local instance] CStarAlgebra.spectralOrder CStarAlgebra.spectralOrderedRing

/-! ### State monotonicity lemmas -/

/-- States map elements of the positive cone to non-negative reals. -/
private lemma apply_positive_cone_nonneg {a : A}
    (ha : a ∈ AddSubmonoid.closure (Set.range fun s : A ↦ star s * s)) :
    0 ≤ (φ a).re := by
  induction ha using AddSubmonoid.closure_induction with
  | mem x hx => obtain ⟨s, rfl⟩ := hx; exact φ.apply_star_mul_self_nonneg s
  | zero => simp [φ.map_zero]
  | add x y _ _ IHx IHy => simp only [φ.map_add, Complex.add_re]; linarith

/-- States are monotone on self-adjoint elements (spectral ordering). -/
private lemma monotone_re {x y : A} (hxy : x ≤ y) : (φ x).re ≤ (φ y).re := by
  rw [StarOrderedRing.le_iff] at hxy
  obtain ⟨p, hp, rfl⟩ := hxy
  simp only [φ.map_add, Complex.add_re]; linarith [φ.apply_positive_cone_nonneg hp]

/-- Real scalar multiplication commutes with taking real part. -/
private lemma smul_apply_re (r : ℝ) (x : A) : (φ (r • x)).re = r * (φ x).re := by
  have key : φ (r • x) = (r : ℂ) * φ x := φ.map_smul r x
  rw [key]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]; ring

/-- Key inequality: `φ(b* a* a b).re ≤ ‖a‖² · φ(b* b).re`. -/
private lemma key_inequality (a b : A) :
    (φ (star b * (star a * a) * b)).re ≤ ‖a‖ ^ 2 * (φ (star b * b)).re := by
  have h1 : star a * a ≤ algebraMap ℝ A (‖a‖ ^ 2) := CStarAlgebra.star_mul_le_algebraMap_norm_sq
  have h2 : star b * (star a * a) * b ≤ star b * algebraMap ℝ A (‖a‖ ^ 2) * b :=
    star_left_conjugate_le_conjugate h1 b
  have h3 : star b * algebraMap ℝ A (‖a‖ ^ 2) * b = (‖a‖ ^ 2) • (star b * b) := by
    simp only [Algebra.algebraMap_eq_smul_one]; rw [mul_smul_one, smul_mul_assoc]
  rw [h3] at h2
  have h4 := φ.monotone_re h2
  rw [smul_apply_re φ (‖a‖ ^ 2) (star b * b)] at h4
  exact h4

/-! ### Boundedness of the pre-representation -/

/-- The norm squared on the quotient equals the inner product with itself. -/
theorem gnsQuotient_norm_sq (x : φ.gnsQuotient) : ‖x‖ * ‖x‖ = (φ.gnsInner x x).re := by
  have h := @InnerProductSpace.norm_sq_eq_re_inner ℂ _ _ _ φ.gnsQuotientInnerProductSpace x
  simp only [sq] at h; convert h using 1

/-- Key boundedness lemma: `‖π(a)x‖ ≤ ‖a‖ * ‖x‖`. -/
theorem gnsPreRep_norm_le (a : A) (x : φ.gnsQuotient) : ‖φ.gnsPreRep a x‖ ≤ ‖a‖ * ‖x‖ := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal x
  rw [gnsPreRep_mk]
  by_cases ha : a = 0
  · simp [ha]
  · -- Express norms via inner products (squared form)
    have h_lhs : ‖(Submodule.Quotient.mk (a * b) : φ.gnsQuotient)‖ ^ 2 =
        (φ (star (a * b) * (a * b))).re := by
      have := @InnerProductSpace.norm_sq_eq_re_inner ℂ _ _ _ φ.gnsQuotientInnerProductSpace
        (Submodule.Quotient.mk (a * b))
      simp only [sq] at this ⊢
      rw [this, inner_eq_gnsInner_swap, gnsInner_mk]; rfl
    have h_rhs : ‖(Submodule.Quotient.mk b : φ.gnsQuotient)‖ ^ 2 = (φ (star b * b)).re := by
      have := @InnerProductSpace.norm_sq_eq_re_inner ℂ _ _ _ φ.gnsQuotientInnerProductSpace
        (Submodule.Quotient.mk b)
      simp only [sq] at this ⊢
      rw [this, inner_eq_gnsInner_swap, gnsInner_mk]; rfl
    -- Expand (ab)*(ab) = b* a* a b and apply key inequality
    have h_expand : star (a * b) * (a * b) = star b * (star a * a) * b := by
      simp only [star_mul, mul_assoc]
    have h_key := key_inequality φ a b
    rw [← h_expand] at h_key
    -- Convert to norm bound: ‖[ab]‖² ≤ ‖a‖² · ‖[b]‖² → ‖[ab]‖ ≤ ‖a‖ · ‖[b]‖
    have h_sq : ‖(Submodule.Quotient.mk (a * b) : φ.gnsQuotient)‖ ^ 2 ≤
                ‖a‖ ^ 2 * ‖(Submodule.Quotient.mk b : φ.gnsQuotient)‖ ^ 2 := by
      rw [h_lhs, h_rhs]; exact h_key
    have h_sq' : ‖(Submodule.Quotient.mk (a * b) : φ.gnsQuotient)‖ ^ 2 ≤
                 (‖a‖ * ‖(Submodule.Quotient.mk b : φ.gnsQuotient)‖) ^ 2 := by
      rw [mul_pow]; exact h_sq
    have h_nonneg_lhs : 0 ≤ ‖(Submodule.Quotient.mk (a * b) : φ.gnsQuotient)‖ := norm_nonneg _
    have h_nonneg_rhs : 0 ≤ ‖a‖ * ‖(Submodule.Quotient.mk b : φ.gnsQuotient)‖ :=
      mul_nonneg (norm_nonneg _) (norm_nonneg _)
    exact (sq_le_sq₀ h_nonneg_lhs h_nonneg_rhs).mp h_sq'

end State
