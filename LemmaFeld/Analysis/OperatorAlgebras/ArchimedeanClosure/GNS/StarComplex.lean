/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.CompleteSpace

/-! # GNS Complexified Star Property

This file proves star preservation and algebraic properties for the complexified GNS representation.

## Main results

* `gnsRepComplex_star` - π_ℂ(star a) = adjoint(π_ℂ(a))
* `gnsRepComplex_mul` - π_ℂ(a*b) = π_ℂ(a) ∘ π_ℂ(b)
* `gnsRepComplex_add` - π_ℂ(a+b) = π_ℂ(a) + π_ℂ(b)
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} [IsArchimedean n] (φ : MPositiveState n)

open ArchimedeanClosure

/-! ### Star Property on Complexified Representation -/

/-- The complexified representation preserves the star: π_ℂ(star a) = adjoint(π_ℂ(a)). -/
theorem gnsRepComplex_star [IsArchimedean n] (a : FreeStarAlgebra n) :
    φ.gnsRepComplex (star a) = ContinuousLinearMap.adjoint (φ.gnsRepComplex a) := by
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro p q
  apply Complex.ext
  · simp only [Complexification.inner_re]
    have hL1 : (φ.gnsRepComplex (star a) p).1 = φ.gnsRep (star a) p.1 := rfl
    have hL2 : (φ.gnsRepComplex (star a) p).2 = φ.gnsRep (star a) p.2 := rfl
    have hR1 : (φ.gnsRepComplex a q).1 = φ.gnsRep a q.1 := rfl
    have hR2 : (φ.gnsRepComplex a q).2 = φ.gnsRep a q.2 := rfl
    rw [hL1, hL2, hR1, hR2]
    simp only [gnsRep_star, ContinuousLinearMap.adjoint_inner_left]
  · simp only [Complexification.inner_im]
    have hL1 : (φ.gnsRepComplex (star a) p).1 = φ.gnsRep (star a) p.1 := rfl
    have hL2 : (φ.gnsRepComplex (star a) p).2 = φ.gnsRep (star a) p.2 := rfl
    have hR1 : (φ.gnsRepComplex a q).1 = φ.gnsRep a q.1 := rfl
    have hR2 : (φ.gnsRepComplex a q).2 = φ.gnsRep a q.2 := rfl
    rw [hL1, hL2, hR1, hR2]
    simp only [gnsRep_star, ContinuousLinearMap.adjoint_inner_left]

/-- The complexified representation sends 1 to the identity. -/
theorem gnsRepComplex_one : φ.gnsRepComplex 1 = ContinuousLinearMap.id ℂ _ := by
  ext p
  · simp only [ContinuousLinearMap.id_apply]
    unfold gnsRepComplex
    simp only [LinearMap.mkContinuous_apply, Complexification.mapComplex_fst]
    rw [gnsRep_one]
    simp only [ContinuousLinearMap.coe_id, LinearMap.id_apply]
  · simp only [ContinuousLinearMap.id_apply]
    unfold gnsRepComplex
    simp only [LinearMap.mkContinuous_apply, Complexification.mapComplex_snd]
    rw [gnsRep_one]
    simp only [ContinuousLinearMap.coe_id, LinearMap.id_apply]

/-- The complexified representation preserves multiplication. -/
theorem gnsRepComplex_mul (a b : FreeStarAlgebra n) :
    φ.gnsRepComplex (a * b) = (φ.gnsRepComplex a).comp (φ.gnsRepComplex b) := by
  ext p
  · simp only [ContinuousLinearMap.comp_apply]
    unfold gnsRepComplex
    simp only [LinearMap.mkContinuous_apply, Complexification.mapComplex_fst]
    rw [gnsRep_mul]
    rfl
  · simp only [ContinuousLinearMap.comp_apply]
    unfold gnsRepComplex
    simp only [LinearMap.mkContinuous_apply, Complexification.mapComplex_snd]
    rw [gnsRep_mul]
    rfl

/-- The complexified representation preserves addition. -/
theorem gnsRepComplex_add (a b : FreeStarAlgebra n) :
    φ.gnsRepComplex (a + b) = φ.gnsRepComplex a + φ.gnsRepComplex b := by
  ext p
  · simp only [ContinuousLinearMap.add_apply]
    unfold gnsRepComplex
    simp only [LinearMap.mkContinuous_apply, Complexification.mapComplex_fst]
    rw [gnsRep_add]
    rfl
  · simp only [ContinuousLinearMap.add_apply]
    unfold gnsRepComplex
    simp only [LinearMap.mkContinuous_apply, Complexification.mapComplex_snd]
    rw [gnsRep_add]
    rfl

/-- The complexified representation preserves ℝ-scalar multiplication. -/
theorem gnsRepComplex_smul (r : ℝ) (a : FreeStarAlgebra n) :
    φ.gnsRepComplex (r • a) = r • φ.gnsRepComplex a := by
  ext p
  · unfold gnsRepComplex
    simp only [LinearMap.mkContinuous_apply, Complexification.mapComplex_fst]
    rw [gnsRep_smul, ContinuousLinearMap.smul_apply]
    change r • φ.gnsRep a p.1 = (r • Complexification.mapComplex (φ.gnsRep a).toLinearMap p).1
    rw [show (r • Complexification.mapComplex (φ.gnsRep a).toLinearMap p).1 =
            ((r : ℂ) • Complexification.mapComplex (φ.gnsRep a).toLinearMap p).1 from rfl,
        Complexification.smul_fst]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complexification.mapComplex_snd,
               zero_smul, sub_zero, Complexification.mapComplex_fst]
    rfl
  · unfold gnsRepComplex
    simp only [LinearMap.mkContinuous_apply, Complexification.mapComplex_snd]
    rw [gnsRep_smul, ContinuousLinearMap.smul_apply]
    change r • φ.gnsRep a p.2 = (r • Complexification.mapComplex (φ.gnsRep a).toLinearMap p).2
    rw [show (r • Complexification.mapComplex (φ.gnsRep a).toLinearMap p).2 =
            ((r : ℂ) • Complexification.mapComplex (φ.gnsRep a).toLinearMap p).2 from rfl,
        Complexification.smul_snd]
    simp only [Complex.ofReal_re, Complex.ofReal_im, Complexification.mapComplex_fst,
               zero_smul, add_zero, Complexification.mapComplex_snd]
    rfl

end MPositiveState

end FreeStarAlgebra
