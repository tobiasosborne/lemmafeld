/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Star
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.StarComplex
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.CompleteSpace
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Representation.Constrained

/-! # GNS Representation is Constrained

This file proves that the GNS representation of an M-positive state satisfies the
generator positivity constraint: π_φ(gⱼ) is a positive operator.

## Main results

* `gnsPreRep_generator_inner_nonneg` - Key identity: ⟨[b], π(gⱼ)[b]⟩ = φ(star b * gⱼ * b) ≥ 0
* `gnsRep_generator_inner_nonneg` - Extended to Hilbert space by density

## Mathematical Background

The key insight: For quotient element [b],
  ⟨[b], π(gⱼ)[b]⟩ = ⟨[b], [gⱼ * b]⟩ = φ(star b * gⱼ * b)

But star b * gⱼ * b ∈ M by the definition of the quadratic module (star_generator_mul_mem).
Since φ is M-positive, φ(star b * gⱼ * b) ≥ 0.

This extends to the full Hilbert space by continuity and density.
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} [IsArchimedean n] (φ : MPositiveState n)

/-! ### Generator positivity on the quotient -/

omit [IsArchimedean n] in
/-- Key identity: ⟨[b], π(gⱼ)[b]⟩ = φ(star b * gⱼ * b) on quotient elements.

This combines gnsPreRep_mk and gnsInner_mk. -/
theorem gnsPreRep_generator_inner (j : Fin n) (b : FreeStarAlgebra n) :
    φ.gnsInner (Submodule.Quotient.mk b) (φ.gnsPreRep (generator j) (Submodule.Quotient.mk b)) =
    φ (star b * generator j * b) := by
  rw [gnsPreRep_mk, gnsInner_mk]
  -- star (gⱼ * b) * b = star b * star gⱼ * b = star b * gⱼ * b (gⱼ self-adjoint)
  simp only [star_mul, (isSelfAdjoint_generator j).star_eq, mul_assoc]

omit [IsArchimedean n] in
/-- The inner product ⟨[b], π(gⱼ)[b]⟩ is nonnegative for generators.

This is the key step: star b * gⱼ * b ∈ M by star_generator_mul_mem,
and φ is M-positive. -/
theorem gnsPreRep_generator_inner_nonneg (j : Fin n) (b : FreeStarAlgebra n) :
    0 ≤ φ.gnsInner (Submodule.Quotient.mk b)
      (φ.gnsPreRep (generator j) (Submodule.Quotient.mk b)) := by
  rw [gnsPreRep_generator_inner]
  exact φ.apply_m_nonneg (star_generator_mul_mem j b)

/-! ### Generator positivity on the Hilbert space -/

/-- The inner product ⟨x, π(gⱼ)x⟩ is nonnegative on the Hilbert space.

Extended from the quotient by density and continuity.
The set {x | 0 ≤ ⟪x, π(gⱼ)x⟫} is closed (continuous preimage of [0,∞)),
and contains the dense subset of quotient elements by gnsPreRep_generator_inner_nonneg. -/
theorem gnsRep_generator_inner_nonneg (j : Fin n) (x : φ.gnsHilbertSpaceReal) :
    0 ≤ @inner ℝ _ _ x (φ.gnsRep (generator j) x) := by
  letI seminorm : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  letI ips : InnerProductSpace ℝ φ.gnsQuotient :=
    @InnerProductSpace.ofCore ℝ _ _ _ _ φ.gnsInnerProductCore.toCore
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    -- The set {x | 0 ≤ ⟪x, π(gⱼ)x⟫} is closed
    apply isClosed_le continuous_const
    exact Continuous.inner continuous_id (φ.gnsRep (generator j)).continuous
  | ih y =>
    -- y is in the quotient, extract representative
    obtain ⟨b, rfl⟩ := φ.gnsQuotient_mk_surjective y
    rw [gnsRep_coe, @UniformSpace.Completion.inner_coe ℝ φ.gnsQuotient _ seminorm ips,
      inner_eq_gnsInner, gnsBoundedPreRep_eq_gnsPreRep]
    exact gnsPreRep_generator_inner_nonneg φ j b

/-! ### Generator positivity on the complexified Hilbert space -/

open ArchimedeanClosure

/-- The complexified inner product Re⟨p, π(gⱼ)p⟩_ℂ is nonnegative for generators.

For p = (x, y) ∈ H_ℂ:
  Re⟨p, π_ℂ(gⱼ)p⟩ = ⟨x, π(gⱼ)x⟩_ℝ + ⟨y, π(gⱼ)y⟩_ℝ ≥ 0

by gnsRep_generator_inner_nonneg applied to x and y. -/
theorem gnsRepComplex_generator_inner_nonneg (j : Fin n)
    (p : φ.gnsHilbertSpaceComplex) :
    0 ≤ (@inner ℂ _ Complexification.instInnerComplex p
      (φ.gnsRepComplex (generator j) p)).re := by
  -- Expand inner product using Complexification.inner_re
  simp only [Complexification.inner_re]
  -- gnsRepComplex acts componentwise
  have h1 : (φ.gnsRepComplex (generator j) p).1 = φ.gnsRep (generator j) p.1 := rfl
  have h2 : (φ.gnsRepComplex (generator j) p).2 = φ.gnsRep (generator j) p.2 := rfl
  rw [h1, h2]
  exact add_nonneg (gnsRep_generator_inner_nonneg φ j p.1)
    (gnsRep_generator_inner_nonneg φ j p.2)

/-- The complexified GNS representation maps generators to positive operators.

Uses isPositive_def': need self-adjoint and nonneg reApplyInnerSelf. -/
theorem gnsRepComplex_generator_isPositive (j : Fin n) :
    (φ.gnsRepComplex (generator j)).IsPositive := by
  rw [ContinuousLinearMap.isPositive_def']
  constructor
  · -- Self-adjoint: adjoint (π_ℂ(gⱼ)) = π_ℂ(gⱼ)
    rw [ContinuousLinearMap.isSelfAdjoint_iff']
    rw [← gnsRepComplex_star]
    congr 1
    exact (isSelfAdjoint_generator j).star_eq
  · -- Nonneg reApplyInnerSelf
    intro p
    rw [ContinuousLinearMap.reApplyInnerSelf_apply]
    simp only [RCLike.re_eq_complex_re]
    -- Re⟨π_ℂ(gⱼ)p, p⟩ = Re⟨p, π_ℂ(gⱼ)p⟩ by conjugate symmetry
    have hsym : (@inner ℂ _ Complexification.instInnerComplex
        (φ.gnsRepComplex (generator j) p) p).re =
        (@inner ℂ _ Complexification.instInnerComplex p
        (φ.gnsRepComplex (generator j) p)).re := by
      have h := @inner_conj_symm ℂ φ.gnsHilbertSpaceComplex _ _ _
        p (φ.gnsRepComplex (generator j) p)
      -- h : conj ⟨π(gⱼ)p, p⟩ = ⟨p, π(gⱼ)p⟩, so RHS.re = (conj LHS).re = LHS.re
      rw [← h, starRingEnd_apply, Complex.star_def, Complex.conj_re]
    rw [hsym]
    exact gnsRepComplex_generator_inner_nonneg φ j p

end MPositiveState

end FreeStarAlgebra
