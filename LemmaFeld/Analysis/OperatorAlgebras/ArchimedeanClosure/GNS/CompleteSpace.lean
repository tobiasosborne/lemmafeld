/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Star

/-! # Completeness of Complexified GNS Hilbert Space

This file proves that the complexified GNS Hilbert space is complete.

## Main results

* `gnsHilbertSpaceComplex_completeSpace` - The complexified Hilbert space is complete

## Implementation Notes

The norm ‖(x,y)‖² = ‖x‖² + ‖y‖² is equivalent to the product norm.
Completeness follows from completeness of each component.
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} [IsArchimedean n] (φ : MPositiveState n)

open ArchimedeanClosure

/-! ### Norm Bounds -/

/-- Component norm squared inequality: ‖p.1‖² ≤ ‖p‖². -/
theorem Complexification.norm_sq_fst_le (p : Complexification φ.gnsHilbertSpaceReal) :
    ‖p.1‖^2 ≤ ‖p‖^2 := by
  rw [@norm_sq_eq_re_inner ℂ (Complexification φ.gnsHilbertSpaceReal) _
      Complexification.instNormedAddCommGroup.toSeminormedAddCommGroup
      Complexification.instInnerProductSpace]
  simp only [RCLike.re_eq_complex_re, Complexification.inner_re, real_inner_self_eq_norm_sq, sq]
  linarith [sq_nonneg ‖p.2‖]

/-- Component norm squared inequality: ‖p.2‖² ≤ ‖p‖². -/
theorem Complexification.norm_sq_snd_le (p : Complexification φ.gnsHilbertSpaceReal) :
    ‖p.2‖^2 ≤ ‖p‖^2 := by
  rw [@norm_sq_eq_re_inner ℂ (Complexification φ.gnsHilbertSpaceReal) _
      Complexification.instNormedAddCommGroup.toSeminormedAddCommGroup
      Complexification.instInnerProductSpace]
  simp only [RCLike.re_eq_complex_re, Complexification.inner_re, real_inner_self_eq_norm_sq, sq]
  linarith [sq_nonneg ‖p.1‖]

/-- Component norm is bounded by total norm: ‖p.1‖ ≤ ‖p‖. -/
theorem Complexification.norm_fst_le (p : Complexification φ.gnsHilbertSpaceReal) :
    ‖p.1‖ ≤ ‖p‖ := by
  have h := Complexification.norm_sq_fst_le φ p
  nlinarith [sq_nonneg ‖p.1‖, sq_nonneg ‖p‖, norm_nonneg p.1, norm_nonneg p]

/-- Component norm is bounded by total norm: ‖p.2‖ ≤ ‖p‖. -/
theorem Complexification.norm_snd_le (p : Complexification φ.gnsHilbertSpaceReal) :
    ‖p.2‖ ≤ ‖p‖ := by
  have h := Complexification.norm_sq_snd_le φ p
  nlinarith [sq_nonneg ‖p.2‖, sq_nonneg ‖p‖, norm_nonneg p.2, norm_nonneg p]

/-! ### Completeness -/

/-- The complexified Hilbert space is complete. -/
instance gnsHilbertSpaceComplex_completeSpace [IsArchimedean n] :
    CompleteSpace φ.gnsHilbertSpaceComplex := by
  letI := Complexification.instNormedAddCommGroup (H := φ.gnsHilbertSpaceReal)
  refine Metric.complete_of_cauchySeq_tendsto ?_
  intro u hu
  have h1 : CauchySeq (fun n => (u n).1) := by
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    use N
    intro m hm n' hn'
    calc dist (u m).1 (u n').1
        = ‖(u m).1 - (u n').1‖ := dist_eq_norm _ _
      _ = ‖(u m - u n').1‖ := rfl
      _ ≤ ‖u m - u n'‖ := Complexification.norm_fst_le φ (u m - u n')
      _ = dist (u m) (u n') := (dist_eq_norm (u m) (u n')).symm
      _ < ε := hN m hm n' hn'
  have h2 : CauchySeq (fun n => (u n).2) := by
    rw [Metric.cauchySeq_iff] at hu ⊢
    intro ε hε
    obtain ⟨N, hN⟩ := hu ε hε
    use N
    intro m hm n' hn'
    calc dist (u m).2 (u n').2
        = ‖(u m).2 - (u n').2‖ := dist_eq_norm _ _
      _ = ‖(u m - u n').2‖ := rfl
      _ ≤ ‖u m - u n'‖ := Complexification.norm_snd_le φ (u m - u n')
      _ = dist (u m) (u n') := (dist_eq_norm (u m) (u n')).symm
      _ < ε := hN m hm n' hn'
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete h1
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete h2
  let lim : Complexification φ.gnsHilbertSpaceReal := (x, y)
  refine ⟨lim, ?_⟩
  rw [Metric.tendsto_atTop] at hx hy ⊢
  intro ε hε
  obtain ⟨N1, hN1⟩ := hx (ε / 2) (half_pos hε)
  obtain ⟨N2, hN2⟩ := hy (ε / 2) (half_pos hε)
  use max N1 N2
  intro n hn
  have hn1 : N1 ≤ n := le_of_max_le_left hn
  have hn2 : N2 ≤ n := le_of_max_le_right hn
  have hnorm1 : ‖(u n).1 - x‖ < ε / 2 := by rw [← dist_eq_norm]; exact hN1 n hn1
  have hnorm2 : ‖(u n).2 - y‖ < ε / 2 := by rw [← dist_eq_norm]; exact hN2 n hn2
  have hdiff1 : (u n - lim).1 = (u n).1 - x := rfl
  have hdiff2 : (u n - lim).2 = (u n).2 - y := rfl
  rw [dist_eq_norm]
  have hbd : ‖(u n - lim).1‖^2 + ‖(u n - lim).2‖^2 < ε^2 := by
    rw [hdiff1, hdiff2]
    have hsq1 : ‖(u n).1 - x‖^2 < (ε/2)^2 :=
      (sq_lt_sq₀ (norm_nonneg _) (by linarith : 0 ≤ ε/2)).mpr hnorm1
    have hsq2 : ‖(u n).2 - y‖^2 < (ε/2)^2 :=
      (sq_lt_sq₀ (norm_nonneg _) (by linarith : 0 ≤ ε/2)).mpr hnorm2
    calc ‖(u n).1 - x‖^2 + ‖(u n).2 - y‖^2
        < (ε/2)^2 + (ε/2)^2 := add_lt_add hsq1 hsq2
      _ = ε^2/2 := by ring
      _ < ε^2 := by linarith [sq_pos_of_pos hε]
  have hnorm_sq : ‖u n - lim‖^2 = ‖(u n - lim).1‖^2 + ‖(u n - lim).2‖^2 := by
    rw [@norm_sq_eq_re_inner ℂ _ _ Complexification.instNormedAddCommGroup.toSeminormedAddCommGroup
        Complexification.instInnerProductSpace (u n - lim)]
    have hinner : @inner ℂ _ Complexification.instInnerComplex (u n - lim) (u n - lim)
        = { re := @inner ℝ _ _ (u n - lim).1 (u n - lim).1 +
                  @inner ℝ _ _ (u n - lim).2 (u n - lim).2,
            im := @inner ℝ _ _ (u n - lim).1 (u n - lim).2 -
                  @inner ℝ _ _ (u n - lim).2 (u n - lim).1 } :=
      Complexification.inner_def _ _
    simp only [hinner, real_inner_self_eq_norm_sq, sq]
    rfl
  calc ‖u n - lim‖
      = Real.sqrt (‖u n - lim‖^2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖(u n - lim).1‖^2 + ‖(u n - lim).2‖^2) := by rw [hnorm_sq]
    _ < Real.sqrt (ε^2) := Real.sqrt_lt_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _)) hbd
    _ = ε := Real.sqrt_sq (le_of_lt hε)

end MPositiveState

end FreeStarAlgebra
