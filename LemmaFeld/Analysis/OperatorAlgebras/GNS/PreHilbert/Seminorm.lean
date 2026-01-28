/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.PreHilbert.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Defs

/-!
# GNS Pre-Inner Product Space

This file proves that the GNS quotient forms a pre-inner product space.

## Main definitions

* `State.gnsNorm` - The norm ‖[a]‖ = √(φ(a*a)).re on the quotient

## Main results

* `State.gnsInner_self_nonneg` - ⟨x, x⟩.re ≥ 0
* `State.gnsInner_self_im` - ⟨x, x⟩.im = 0
* `State.gnsNorm_mk` - ‖mk a‖ = √(φ(a*a)).re
* `State.gnsPreInnerProductCore` - The PreInnerProductSpace.Core instance
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### Self inner product properties -/

/-- The inner product ⟨x, x⟩ has non-negative real part. -/
theorem gnsInner_self_nonneg (x : φ.gnsQuotient) : 0 ≤ (φ.gnsInner x x).re := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal x
  simp only [gnsInner_mk]
  exact φ.apply_star_mul_self_nonneg a

/-- The inner product ⟨x, x⟩ has zero imaginary part (is real). -/
theorem gnsInner_self_im (x : φ.gnsQuotient) : (φ.gnsInner x x).im = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal x
  simp only [gnsInner_mk]
  exact φ.apply_star_mul_self_im a

/-- The inner product ⟨x, x⟩ equals its real part (as a complex number). -/
theorem gnsInner_self_eq_re (x : φ.gnsQuotient) : φ.gnsInner x x = (φ.gnsInner x x).re := by
  apply Complex.ext
  · rfl
  · simp [gnsInner_self_im φ x]

/-! ### Norm definition -/

/-- The GNS norm on the quotient: ‖x‖ = √(⟨x, x⟩.re). -/
noncomputable def gnsNorm (x : φ.gnsQuotient) : ℝ :=
  Real.sqrt (φ.gnsInner x x).re

/-- The norm on representatives: ‖mk a‖ = √(φ(a*a)).re. -/
theorem gnsNorm_mk (a : A) : φ.gnsNorm (Submodule.Quotient.mk a) =
    Real.sqrt (φ (star a * a)).re := rfl

/-- The norm is non-negative. -/
theorem gnsNorm_nonneg (x : φ.gnsQuotient) : 0 ≤ φ.gnsNorm x :=
  Real.sqrt_nonneg _

/-! ### Pre-inner product space structure -/

/-- The GNS quotient has an inner product structure.
    Note: We use `gnsInner y x` (swapped) to match mathlib's convention
    where the inner product is conjugate-linear in the first argument. -/
noncomputable instance gnsQuotientInner : Inner ℂ φ.gnsQuotient :=
  ⟨fun x y => φ.gnsInner y x⟩

theorem inner_eq_gnsInner_swap (x y : φ.gnsQuotient) :
    @inner ℂ φ.gnsQuotient φ.gnsQuotientInner x y = φ.gnsInner y x := rfl

/-- Scalar multiplication in second argument (mathlib convention):
    ⟨x, c • y⟩ = conj(c) * ⟨x, y⟩. -/
theorem gnsInner_smul_right (c : ℂ) (x y : φ.gnsQuotient) :
    φ.gnsInner x (c • y) = starRingEnd ℂ c * φ.gnsInner x y := by
  have h1 : φ.gnsInner x (c • y) = starRingEnd ℂ (φ.gnsInner (c • y) x) :=
    gnsInner_conj_symm φ x (c • y)
  have h2 : φ.gnsInner (c • y) x = c * φ.gnsInner y x := gnsInner_smul_left φ c y x
  have h3 : φ.gnsInner x y = starRingEnd ℂ (φ.gnsInner y x) := gnsInner_conj_symm φ x y
  rw [h1, h2, map_mul, h3]

/-- The PreInnerProductSpace.Core instance for the GNS quotient. -/
noncomputable def gnsPreInnerProductCore : PreInnerProductSpace.Core ℂ φ.gnsQuotient where
  conj_inner_symm x y := (gnsInner_conj_symm φ y x).symm
  re_inner_nonneg x := gnsInner_self_nonneg φ x
  add_left x y z := by
    change φ.gnsInner z (x + y) = φ.gnsInner z x + φ.gnsInner z y
    have h := gnsInner_add_left φ x y z
    rw [gnsInner_conj_symm φ z (x + y), gnsInner_conj_symm φ z x, gnsInner_conj_symm φ z y, h]
    exact (starRingEnd ℂ).map_add _ _
  smul_left x y r := gnsInner_smul_right φ r y x

end State
