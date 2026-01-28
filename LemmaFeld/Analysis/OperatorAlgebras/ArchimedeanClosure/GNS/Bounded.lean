/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.PreRep
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Completion
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Algebra.Archimedean
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Boundedness of GNS Pre-Representation

This file proves that the GNS pre-representation is bounded using the Archimedean property.

## Main results

* `gnsLeftAction_bounded` - ‖π_φ(a) x‖ ≤ √N_a * ‖x‖ where N_a is the Archimedean bound
* `gnsBoundedPreRep` - The bounded linear operator version

## Proof Strategy

For [b] in the quotient:
1. ‖[ab]‖² = ⟨[ab], [ab]⟩ = φ(star(ab) * ab) = φ(star b * star a * a * b)
2. Use Archimedean: N·1 - star a * a ∈ M
3. So φ(star b * (N·1 - star a * a) * b) ≥ 0 (conjugation closure)
4. Rearranging: φ(star b * star a * a * b) ≤ N * φ(star b * b)
5. Hence ‖[ab]‖² ≤ N_a * ‖[b]‖², giving ‖[ab]‖ ≤ √N_a * ‖[b]‖

## References

* Schmüdgen (2020) Chapter 10
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} [IsArchimedean n] (φ : MPositiveState n)

/-! ### Auxiliary lemmas -/

/-- The norm squared equals the inner product with itself. -/
theorem gnsNorm_sq_eq_inner (x : φ.gnsQuotient) :
    @Norm.norm _ φ.gnsQuotientNormedAddCommGroup.toNorm x ^ 2 = φ.gnsInner x x := by
  have h := @InnerProductSpace.Core.norm_eq_sqrt_re_inner ℝ φ.gnsQuotient _ _ _
      φ.gnsPreInnerProductCore x
  have h_inner : @inner ℝ _ φ.gnsPreInnerProductCore.toInner x x = φ.gnsInner x x := rfl
  rw [h, h_inner, RCLike.re_to_real]
  exact Real.sq_sqrt (φ.gnsInner_nonneg x)

/-- φ(star b * m * b) ≥ 0 for m ∈ M. This follows from conjugation closure. -/
theorem apply_star_mul_quadMod_mul_nonneg {m : FreeStarAlgebra n}
    (hm : m ∈ QuadraticModule n) (b : FreeStarAlgebra n) :
    0 ≤ φ (star b * m * b) := by
  have h : star b * m * b ∈ QuadraticModule n := QuadraticModule.star_mul_mem_star_mul hm b
  exact φ.apply_m_nonneg h

/-! ### Main boundedness theorem -/

/-- The GNS left action is bounded: ‖π_φ(a) x‖ ≤ √N_a * ‖x‖.

This is the key theorem using the Archimedean property. -/
theorem gnsLeftAction_bounded (a : FreeStarAlgebra n) (x : φ.gnsQuotient) :
    @Norm.norm _ φ.gnsQuotientNormedAddCommGroup.toNorm (φ.gnsLeftAction a x) ≤
    Real.sqrt (archimedeanBound a) * @Norm.norm _ φ.gnsQuotientNormedAddCommGroup.toNorm x := by
  -- Work with representatives
  obtain ⟨b, rfl⟩ := φ.gnsQuotient_mk_surjective x
  -- Goal: ‖[ab]‖ ≤ √N_a * ‖[b]‖
  -- Strategy: show ‖[ab]‖² ≤ N_a * ‖[b]‖², then take sqrt
  have h_action : φ.gnsLeftAction a (Submodule.Quotient.mk b) = Submodule.Quotient.mk (a * b) :=
    φ.gnsPreRep_mk a b
  rw [h_action]
  -- Abbreviation for the norm instance
  let nrm := φ.gnsQuotientNormedAddCommGroup.toNorm
  -- Use norm² = inner product
  have h_lhs : @Norm.norm _ nrm (Submodule.Quotient.mk (a * b)) ^ 2
      = φ (star (a * b) * (a * b)) := by
    rw [gnsNorm_sq_eq_inner, gnsInner_mk]
  have h_rhs : @Norm.norm _ nrm (Submodule.Quotient.mk b) ^ 2 = φ (star b * b) := by
    rw [gnsNorm_sq_eq_inner, gnsInner_mk]
  -- Key step: φ(star(ab) * ab) = φ(star b * star a * a * b)
  have h_expand : φ (star (a * b) * (a * b)) = φ (star b * (star a * a) * b) := by
    simp only [star_mul, mul_assoc]
  -- Archimedean gives: N·1 - star a * a ∈ M
  have h_arch := archimedeanBound_spec a
  -- So φ(star b * (N·1 - star a * a) * b) ≥ 0
  have h_nonneg := apply_star_mul_quadMod_mul_nonneg φ h_arch b
  -- Expand: φ(N * star b * b - star b * star a * a * b) ≥ 0
  have h_expand2 : star b * ((archimedeanBound a : ℝ) • (1 : FreeStarAlgebra n) - star a * a) * b
      = (archimedeanBound a : ℝ) • (star b * b) - star b * (star a * a) * b := by
    simp only [Algebra.smul_def, mul_sub, sub_mul, mul_one, mul_assoc]
    congr 1
    -- Goal: star b * (r * b) = r * (star b * b) where r = algebraMap ...
    calc star b * (algebraMap ℝ (FreeStarAlgebra n) ↑(archimedeanBound a) * b)
        = (star b * algebraMap ℝ (FreeStarAlgebra n) ↑(archimedeanBound a)) * b := by rw [mul_assoc]
      _ = (algebraMap ℝ (FreeStarAlgebra n) ↑(archimedeanBound a) * star b) * b := by
          rw [Algebra.commutes]
      _ = algebraMap ℝ (FreeStarAlgebra n) ↑(archimedeanBound a) * (star b * b) := by rw [mul_assoc]
  rw [h_expand2] at h_nonneg
  -- φ is linear: φ(N • (star b * b) - ...) = N * φ(star b * b) - φ(...)
  have h_linear : φ ((archimedeanBound a : ℝ) • (star b * b) - star b * (star a * a) * b)
      = (archimedeanBound a : ℝ) * φ (star b * b) - φ (star b * (star a * a) * b) := by
    have hsub : φ ((archimedeanBound a : ℝ) • (star b * b) - star b * (star a * a) * b)
        = φ ((archimedeanBound a : ℝ) • (star b * b) + (-1 : ℝ) • (star b * (star a * a) * b)) := by
      simp only [neg_one_smul, sub_eq_add_neg]
    rw [hsub, φ.map_add, φ.map_smul, φ.map_smul, neg_one_mul, sub_eq_add_neg]
  rw [h_linear] at h_nonneg
  -- So: φ(star b * star a * a * b) ≤ N * φ(star b * b)
  have h_bound : φ (star b * (star a * a) * b) ≤ (archimedeanBound a : ℝ) * φ (star b * b) := by
    linarith
  -- Combine with h_expand
  rw [h_expand] at h_lhs
  -- Abbreviations for readability (nrm defined above)
  let norm_ab := @Norm.norm _ nrm (Submodule.Quotient.mk (a * b))
  let norm_b := @Norm.norm _ nrm (Submodule.Quotient.mk b)
  let N := (archimedeanBound a : ℝ)
  -- Now: ‖[ab]‖² ≤ N_a * ‖[b]‖²
  have h_sq_bound : norm_ab ^ 2 ≤ N * norm_b ^ 2 := by
    simp only [norm_ab, norm_b, N]
    rw [h_lhs, h_rhs]
    exact h_bound
  -- Take sqrt: ‖[ab]‖ ≤ √N_a * ‖[b]‖
  -- Norms are nonneg since ‖x‖ = sqrt(inner x x)
  have h_norm_nonneg : 0 ≤ norm_ab := by
    simp only [norm_ab]
    have heq := @InnerProductSpace.Core.norm_eq_sqrt_re_inner ℝ φ.gnsQuotient _ _ _
        φ.gnsPreInnerProductCore (Submodule.Quotient.mk (a * b))
    simp only [RCLike.re_to_real] at heq
    rw [heq]
    exact Real.sqrt_nonneg _
  have h_norm_nonneg' : 0 ≤ norm_b := by
    simp only [norm_b]
    have heq := @InnerProductSpace.Core.norm_eq_sqrt_re_inner ℝ φ.gnsQuotient _ _ _
        φ.gnsPreInnerProductCore (Submodule.Quotient.mk b)
    simp only [RCLike.re_to_real] at heq
    rw [heq]
    exact Real.sqrt_nonneg _
  have h_N_nonneg : 0 ≤ N := Nat.cast_nonneg _
  calc norm_ab
      = Real.sqrt (norm_ab ^ 2) := (Real.sqrt_sq h_norm_nonneg).symm
    _ ≤ Real.sqrt (N * norm_b ^ 2) := Real.sqrt_le_sqrt h_sq_bound
    _ = Real.sqrt N * Real.sqrt (norm_b ^ 2) := Real.sqrt_mul h_N_nonneg _
    _ = Real.sqrt N * norm_b := by rw [Real.sqrt_sq h_norm_nonneg']
    _ = Real.sqrt (archimedeanBound a) * norm_b := rfl

end MPositiveState

end FreeStarAlgebra
