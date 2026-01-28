/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Extension

/-! # GNS Representation Extension to Complexification

This file extends the GNS representation to the complexified Hilbert space.

## Main definitions

* `MPositiveState.gnsRepComplex` - GNS representation on the complex Hilbert space

## Implementation Notes

The complexified representation acts componentwise:
  gnsRepComplex a (x, y) = (gnsRep a x, gnsRep a y)

This is ℂ-linear because the real action commutes with the complex structure.
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} [IsArchimedean n] (φ : MPositiveState n)

open ArchimedeanClosure

/-- Norm squared on complexification equals sum of component norm squares. -/
private theorem complexification_norm_sq (p : Complexification φ.gnsHilbertSpaceReal) :
    ‖p‖^2 = ‖p.1‖^2 + ‖p.2‖^2 := by
  rw [@norm_sq_eq_re_inner ℂ (Complexification φ.gnsHilbertSpaceReal) _
      Complexification.instNormedAddCommGroup.toSeminormedAddCommGroup
      Complexification.instInnerProductSpace]
  rw [RCLike.re_eq_complex_re]
  rw [Complexification.inner_re, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]

/-- The GNS representation extended to the complexified Hilbert space.

For each algebra element a, gnsRepComplex a acts as gnsRep a on each component:
(gnsRep a)_ℂ (x, y) = ((gnsRep a) x, (gnsRep a) y)

This is ℂ-linear because the real action commutes with complex structure. -/
noncomputable def gnsRepComplex (a : FreeStarAlgebra n) :
    φ.gnsHilbertSpaceComplex →L[ℂ] φ.gnsHilbertSpaceComplex :=
  LinearMap.mkContinuous
    (Complexification.mapComplex (φ.gnsRep a).toLinearMap)
    ‖φ.gnsRep a‖
    (fun p => by
      set q : Complexification φ.gnsHilbertSpaceReal :=
        Complexification.mapComplex (φ.gnsRep a).toLinearMap p
      have hq : q = ((φ.gnsRep a) p.1, (φ.gnsRep a) p.2) := rfl
      have h1 : ‖(φ.gnsRep a) p.1‖ ≤ ‖φ.gnsRep a‖ * ‖p.1‖ := (φ.gnsRep a).le_opNorm p.1
      have h2 : ‖(φ.gnsRep a) p.2‖ ≤ ‖φ.gnsRep a‖ * ‖p.2‖ := (φ.gnsRep a).le_opNorm p.2
      have hsq1 : ‖(φ.gnsRep a) p.1‖^2 ≤ ‖φ.gnsRep a‖^2 * ‖p.1‖^2 := by
        calc ‖(φ.gnsRep a) p.1‖^2 ≤ (‖φ.gnsRep a‖ * ‖p.1‖)^2 :=
              sq_le_sq' (by linarith [norm_nonneg ((φ.gnsRep a) p.1)]) h1
          _ = ‖φ.gnsRep a‖^2 * ‖p.1‖^2 := by ring
      have hsq2 : ‖(φ.gnsRep a) p.2‖^2 ≤ ‖φ.gnsRep a‖^2 * ‖p.2‖^2 := by
        calc ‖(φ.gnsRep a) p.2‖^2 ≤ (‖φ.gnsRep a‖ * ‖p.2‖)^2 :=
              sq_le_sq' (by linarith [norm_nonneg ((φ.gnsRep a) p.2)]) h2
          _ = ‖φ.gnsRep a‖^2 * ‖p.2‖^2 := by ring
      have hnorm_q : ‖q‖^2 = ‖(φ.gnsRep a) p.1‖^2 + ‖(φ.gnsRep a) p.2‖^2 := by
        rw [complexification_norm_sq]; rfl
      have hnorm_p : ‖p‖^2 = ‖p.1‖^2 + ‖p.2‖^2 := complexification_norm_sq φ p
      rw [← Real.sqrt_sq (norm_nonneg q), hnorm_q]
      calc Real.sqrt (‖(φ.gnsRep a) p.1‖^2 + ‖(φ.gnsRep a) p.2‖^2)
          ≤ Real.sqrt (‖φ.gnsRep a‖^2 * ‖p.1‖^2 + ‖φ.gnsRep a‖^2 * ‖p.2‖^2) := by
            apply Real.sqrt_le_sqrt; linarith
        _ = Real.sqrt (‖φ.gnsRep a‖^2 * (‖p.1‖^2 + ‖p.2‖^2)) := by ring_nf
        _ = ‖φ.gnsRep a‖ * Real.sqrt (‖p.1‖^2 + ‖p.2‖^2) := by
            rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _)]
        _ = ‖φ.gnsRep a‖ * ‖p‖ := by rw [← hnorm_p, Real.sqrt_sq (norm_nonneg _)])

end MPositiveState

end FreeStarAlgebra
