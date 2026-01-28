/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Representation.Extension
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# GNS Representation Star Property

This file proves the GNS representation preserves the star operation: π(a*) = π(a)†.

## Main results

* `State.gnsRep_star` - π(a*) = π(a).adjoint
* `State.gnsStarAlgHom` - The GNS representation as a *-algebra homomorphism

## Mathematical Background

The key calculation: For x = [b], y = [c],
  ⟪π(a*)x, y⟫ = ⟪[a*b], [c]⟫ = φ(c* · a* · b)
  ⟪x, π(a)y⟫ = ⟪[b], [ac]⟫ = φ((ac)* · b) = φ(c* · a* · b)

These are equal, so by density and continuity, π(a*) = π(a)† on the completion.
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### Star property on the pre-representation -/

/-- The pre-representation satisfies the adjoint identity on quotient elements.
    Note: Uses the swapped convention where inner x y = gnsInner y x. -/
theorem gnsPreRep_inner_star (a b c : A) :
    φ.gnsInner (Submodule.Quotient.mk c) (φ.gnsPreRep (star a) (Submodule.Quotient.mk b)) =
    φ.gnsInner (φ.gnsPreRep a (Submodule.Quotient.mk c)) (Submodule.Quotient.mk b) := by
  -- LHS: gnsInner [c] [a*b] = φ(star(a*b) * c) = φ(b* a c)
  -- RHS: gnsInner [ac] [b] = φ(star b * (ac)) = φ(b* a c)
  simp only [gnsPreRep_mk, gnsInner_mk, star_mul, star_star, mul_assoc]

/-! ### Star property on the full representation -/

/-- Helper: inner product of gnsRep with quotient elements. -/
theorem gnsRep_inner_quotient (a : A) (x y : φ.gnsQuotient) :
    @inner ℂ _ _ (φ.gnsRep a (x : φ.gnsHilbertSpace)) (y : φ.gnsHilbertSpace) =
    @inner ℂ _ φ.gnsQuotientInner (φ.gnsPreRep a x) y := by
  simp only [gnsRep_coe, UniformSpace.Completion.inner_coe, inner_eq_gnsInner_swap]

/-- The GNS representation preserves the star: π(a*) = π(a)†. -/
theorem gnsRep_star (a : A) :
    φ.gnsRep (star a) = ContinuousLinearMap.adjoint (φ.gnsRep a) := by
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
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal qb
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal qc
    -- Compute both sides using the pre-representation
    simp only [gnsRep_coe, UniformSpace.Completion.inner_coe, inner_eq_gnsInner_swap]
    exact gnsPreRep_inner_star φ a b c

/-- Alternative formulation: star of gnsRep is adjoint. -/
theorem gnsRep_star' (a : A) :
    star (φ.gnsRep a) = φ.gnsRep (star a) := by
  rw [ContinuousLinearMap.star_eq_adjoint, gnsRep_star]

/-! ### The *-algebra homomorphism -/

/-- The representation of 0 is 0. -/
@[simp]
theorem gnsRep_zero : φ.gnsRep 0 = 0 := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (φ.gnsRep 0).continuous continuous_const
  | ih y =>
    simp only [gnsRep_coe, gnsPreRep_zero, LinearMap.zero_apply,
      ContinuousLinearMap.zero_apply, UniformSpace.Completion.coe_zero]

/-- The representation respects scalar multiplication. -/
theorem gnsRep_smul (c : ℂ) (a : A) : φ.gnsRep (c • a) = c • φ.gnsRep a := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (φ.gnsRep _).continuous ((c • φ.gnsRep a).continuous)
  | ih y =>
    simp only [gnsRep_coe, gnsPreRep_smul, LinearMap.smul_apply,
      ContinuousLinearMap.smul_apply, UniformSpace.Completion.coe_smul]

/-- The GNS representation is a *-algebra homomorphism A →⋆ₐ[ℂ] B(H_φ). -/
noncomputable def gnsStarAlgHom : A →⋆ₐ[ℂ] (φ.gnsHilbertSpace →L[ℂ] φ.gnsHilbertSpace) where
  toFun := φ.gnsRep
  map_one' := gnsRep_one φ
  map_mul' := fun a b => by rw [gnsRep_mul, ContinuousLinearMap.mul_def]
  map_zero' := gnsRep_zero φ
  map_add' := gnsRep_add φ
  commutes' := fun r => by
    simp only [Algebra.algebraMap_eq_smul_one, gnsRep_smul, gnsRep_one]
    rfl
  map_star' := fun a => (gnsRep_star' φ a).symm

@[simp]
theorem gnsStarAlgHom_apply (a : A) : φ.gnsStarAlgHom a = φ.gnsRep a := rfl

end State
