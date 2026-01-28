/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.ExtensionComplex
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # GNS Star Property

This file proves the GNS representation preserves the star operation: π(star a) = adjoint(π(a)).

## Main results

* `gnsPreRep_inner_star` - Key identity on quotient elements
* `gnsRep_star` - π(star a) = adjoint(π(a)) on the real Hilbert space

## Mathematical Background

The key calculation: For quotient elements [b], [c],
  ⟨[c], π(star a)[b]⟩ = ⟨[c], [star(a)*b]⟩ = φ(star(star(a)*b) * c) = φ(star(b)*a*c)
  ⟨π(a)[c], [b]⟩ = ⟨[a*c], [b]⟩ = φ(star(b) * (a*c)) = φ(star(b)*a*c)

These are equal, so π(star a) = adjoint(π(a)) by density and continuity.
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} [IsArchimedean n] (φ : MPositiveState n)

/-! ### Star property on the pre-representation -/

/-- The pre-representation satisfies the adjoint identity on quotient elements. -/
theorem gnsPreRep_inner_star (a b c : FreeStarAlgebra n) :
    φ.gnsInner (φ.gnsPreRep (star a) (Submodule.Quotient.mk b)) (Submodule.Quotient.mk c) =
    φ.gnsInner (Submodule.Quotient.mk b) (φ.gnsPreRep a (Submodule.Quotient.mk c)) := by
  -- LHS: gnsInner [star(a)*b] [c] = φ(star(c) * (star(a)*b)) = φ(star(c)*star(a)*b)
  -- RHS: gnsInner [b] [a*c] = φ(star(a*c) * b) = φ(star(c)*star(a)*b)  (using star anti-hom)
  simp only [gnsPreRep_mk, gnsInner_mk, star_mul, mul_assoc]

/-! ### Star property on the extended representation -/

/-- gnsBoundedPreRep is just gnsPreRep with continuity data. -/
theorem gnsBoundedPreRep_eq_gnsPreRep (a : FreeStarAlgebra n) (x : φ.gnsQuotient) :
    φ.gnsBoundedPreRep a x = φ.gnsPreRep a x := by
  rfl

/-- The GNS representation preserves the star: π(star a) = adjoint(π(a)).

Uses that both sides are continuous and agree on the dense subset. -/
theorem gnsRep_star (a : FreeStarAlgebra n) :
    φ.gnsRep (star a) = ContinuousLinearMap.adjoint (φ.gnsRep a) := by
  letI : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  -- Use density: it suffices to check on embedded quotient elements
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp =>
    apply isClosed_eq
    · exact continuous_inner.comp ((φ.gnsRep (star a)).continuous.prodMap continuous_id)
    · exact continuous_inner.comp (continuous_id.prodMap (φ.gnsRep a).continuous)
  | ih qb qc =>
    -- Extract algebra elements from quotient elements
    obtain ⟨b, rfl⟩ := φ.gnsQuotient_mk_surjective qb
    obtain ⟨c, rfl⟩ := φ.gnsQuotient_mk_surjective qc
    -- Compute both sides using the pre-representation
    simp only [gnsRep_coe, UniformSpace.Completion.inner_coe, inner_eq_gnsInner,
      gnsBoundedPreRep_eq_gnsPreRep]
    exact gnsPreRep_inner_star φ a b c

/-- Alternative formulation: star of gnsRep is adjoint. -/
theorem gnsRep_star' (a : FreeStarAlgebra n) :
    star (φ.gnsRep a) = φ.gnsRep (star a) := by
  rw [ContinuousLinearMap.star_eq_adjoint, gnsRep_star]

/-! ### Additional properties for StarAlgHom -/

/-- The representation of 0 is 0. -/
@[simp]
theorem gnsRep_zero : φ.gnsRep 0 = 0 := by
  letI : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (φ.gnsRep 0).continuous continuous_const
  | ih y =>
    simp only [gnsRep_coe, ContinuousLinearMap.zero_apply]
    obtain ⟨z, rfl⟩ := φ.gnsQuotient_mk_surjective y
    simp only [gnsBoundedPreRep_eq_gnsPreRep, gnsPreRep_mk, zero_mul,
      Submodule.Quotient.mk_zero, UniformSpace.Completion.coe_zero]

/-- The representation respects scalar multiplication by ℝ. -/
theorem gnsRep_smul (r : ℝ) (a : FreeStarAlgebra n) : φ.gnsRep (r • a) = r • φ.gnsRep a := by
  letI : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  letI : NormedSpace ℝ φ.gnsQuotient := φ.gnsQuotientNormedSpace
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (φ.gnsRep _).continuous ((r • φ.gnsRep a).continuous)
  | ih y =>
    simp only [gnsRep_coe, ContinuousLinearMap.smul_apply]
    obtain ⟨z, rfl⟩ := φ.gnsQuotient_mk_surjective y
    simp only [gnsBoundedPreRep_eq_gnsPreRep, gnsPreRep_mk, Algebra.smul_mul_assoc,
      Submodule.Quotient.mk_smul]
    change (↑(r • Submodule.Quotient.mk (a * z) : φ.gnsQuotient) : φ.gnsHilbertSpaceReal) =
      r • (↑(Submodule.Quotient.mk (a * z) : φ.gnsQuotient) : φ.gnsHilbertSpaceReal)
    exact UniformSpace.Completion.coe_smul (M := ℝ) r (Submodule.Quotient.mk (a * z))

end MPositiveState

end FreeStarAlgebra
