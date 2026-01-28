/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Representation.Bounded
import LemmaFeld.Analysis.OperatorAlgebras.GNS.HilbertSpace.CyclicVector

/-!
# GNS Representation Extension

This file extends the pre-representation from A/N_φ to the GNS Hilbert space H_φ.

## Main definitions

* `State.gnsPreRepContinuous` - The pre-representation as a continuous linear map
* `State.gnsRep` - The GNS representation π_φ(a) : H_φ →L[ℂ] H_φ

## Main results

* `State.gnsRep_coe` - gnsRep agrees with gnsPreRep on the embedded quotient
* `State.gnsRep_cyclicVector` - gnsRep φ a Ω_φ = [a]
* `State.gnsRep_mul` - gnsRep φ (a * b) = gnsRep φ a ∘L gnsRep φ b
* `State.gnsRep_one` - gnsRep φ 1 = id

## Mathematical Background

The pre-representation π_φ(a) on A/N_φ is bounded with ‖π_φ(a)‖ ≤ ‖a‖.
This allows unique extension to the completion H_φ by uniform continuity.
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### Continuous linear map version of the pre-representation -/

/-- The pre-representation as a continuous linear map on the quotient.
    Uses the boundedness: ‖π_φ(a)x‖ ≤ ‖a‖ * ‖x‖.
    Note: We use explicit @ syntax to avoid the typeclass diamond between
    the quotient topology and the seminormed topology. -/
noncomputable def gnsPreRepContinuous (a : A) :
    @ContinuousLinearMap ℂ ℂ _ _ (RingHom.id ℂ) φ.gnsQuotient
      (@UniformSpace.toTopologicalSpace _ φ.gnsQuotientSeminormedAddCommGroup.toUniformSpace)
      φ.gnsQuotientSeminormedAddCommGroup.toAddCommMonoid φ.gnsQuotient
      (@UniformSpace.toTopologicalSpace _ φ.gnsQuotientSeminormedAddCommGroup.toUniformSpace)
      φ.gnsQuotientSeminormedAddCommGroup.toAddCommMonoid
      (φ.gnsQuotientNormedSpace).toModule (φ.gnsQuotientNormedSpace).toModule :=
  @LinearMap.mkContinuous ℂ ℂ φ.gnsQuotient φ.gnsQuotient _ _
    φ.gnsQuotientSeminormedAddCommGroup φ.gnsQuotientSeminormedAddCommGroup
    (φ.gnsQuotientNormedSpace).toModule (φ.gnsQuotientNormedSpace).toModule
    (RingHom.id ℂ) (φ.gnsPreRep a) ‖a‖ (fun x => φ.gnsPreRep_norm_le a x)

/-- The continuous version agrees with the linear map version. -/
@[simp]
theorem gnsPreRepContinuous_apply (a : A) (x : φ.gnsQuotient) :
    φ.gnsPreRepContinuous a x = φ.gnsPreRep a x := by
  unfold gnsPreRepContinuous
  simp only [LinearMap.mkContinuous_apply]

/-- The pre-representation is uniformly continuous. -/
theorem gnsPreRepContinuous_uniformContinuous (a : A) :
    @UniformContinuous _ _ φ.gnsQuotientSeminormedAddCommGroup.toUniformSpace
      φ.gnsQuotientSeminormedAddCommGroup.toUniformSpace (φ.gnsPreRepContinuous a) :=
  (φ.gnsPreRepContinuous a).uniformContinuous

/-! ### Extension to the Hilbert space -/

/-- The GNS representation on the Hilbert space.
    Defined using UniformSpace.Completion.map with the uniformly continuous pre-rep.
    The representation is a bounded linear operator on H_φ. -/
noncomputable def gnsRep (a : A) : φ.gnsHilbertSpace →L[ℂ] φ.gnsHilbertSpace where
  toLinearMap := {
    toFun := UniformSpace.Completion.map (φ.gnsPreRepContinuous a)
    map_add' := fun x y => by
      let huc := gnsPreRepContinuous_uniformContinuous φ a
      induction x, y using UniformSpace.Completion.induction_on₂ with
      | hp =>
        refine isClosed_eq ?_ ?_
        · exact (UniformSpace.Completion.continuous_map (f := φ.gnsPreRepContinuous a)).comp
            continuous_add
        · exact (UniformSpace.Completion.continuous_map (f := φ.gnsPreRepContinuous a)).comp
            continuous_fst |>.add <| (UniformSpace.Completion.continuous_map
            (f := φ.gnsPreRepContinuous a)).comp continuous_snd
      | ih x y =>
        simp only [← UniformSpace.Completion.coe_add,
          UniformSpace.Completion.map_coe huc, gnsPreRepContinuous_apply,
          (φ.gnsPreRep a).map_add]
    map_smul' := fun c x => by
      let huc := gnsPreRepContinuous_uniformContinuous φ a
      induction x using UniformSpace.Completion.induction_on with
      | hp =>
        refine isClosed_eq ?_ ?_
        · exact (UniformSpace.Completion.continuous_map (f := φ.gnsPreRepContinuous a)).comp
            (continuous_const_smul c)
        · exact (continuous_const_smul c).comp
            (UniformSpace.Completion.continuous_map (f := φ.gnsPreRepContinuous a))
      | ih x =>
        simp only [RingHom.id_apply, ← UniformSpace.Completion.coe_smul,
          UniformSpace.Completion.map_coe huc, gnsPreRepContinuous_apply,
          (φ.gnsPreRep a).map_smul]
  }
  cont := UniformSpace.Completion.continuous_map

/-- The representation agrees with the pre-representation on the embedded quotient. -/
@[simp]
theorem gnsRep_coe (a : A) (x : φ.gnsQuotient) :
    φ.gnsRep a (x : φ.gnsHilbertSpace) = (φ.gnsPreRep a x : φ.gnsHilbertSpace) := by
  change UniformSpace.Completion.map (φ.gnsPreRepContinuous a) x = _
  rw [UniformSpace.Completion.map_coe (gnsPreRepContinuous_uniformContinuous φ a),
      gnsPreRepContinuous_apply]

/-- The representation on the cyclic vector: π_φ(a)Ω_φ = [a]. -/
theorem gnsRep_cyclicVector (a : A) :
    φ.gnsRep a φ.gnsCyclicVector =
      (Submodule.Quotient.mk (p := φ.gnsNullIdeal) a : φ.gnsHilbertSpace) := by
  rw [gnsCyclicVector_eq_coe, gnsCyclicVectorQuotient]
  simp only [gnsRep_coe, gnsPreRep_mk, mul_one]

/-! ### Algebraic properties -/

/-- The representation is multiplicative: π_φ(ab) = π_φ(a) ∘L π_φ(b). -/
theorem gnsRep_mul (a b : A) :
    φ.gnsRep (a * b) = φ.gnsRep a ∘L φ.gnsRep b := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    apply isClosed_eq
    · exact (φ.gnsRep (a * b)).continuous
    · exact (φ.gnsRep a ∘L φ.gnsRep b).continuous
  | ih y =>
    simp only [gnsRep_coe, ContinuousLinearMap.coe_comp', Function.comp_apply]
    rw [gnsPreRep_mul]
    rfl

/-- The representation of 1 is the identity: π_φ(1) = id. -/
@[simp]
theorem gnsRep_one : φ.gnsRep 1 = ContinuousLinearMap.id ℂ φ.gnsHilbertSpace := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq (φ.gnsRep 1).continuous continuous_id
  | ih y =>
    simp only [gnsRep_coe, gnsPreRep_one, LinearMap.id_coe, id_eq,
      ContinuousLinearMap.id_apply]

/-- The representation is additive: π_φ(a+b) = π_φ(a) + π_φ(b). -/
theorem gnsRep_add (a b : A) :
    φ.gnsRep (a + b) = φ.gnsRep a + φ.gnsRep b := by
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    apply isClosed_eq
    · exact (φ.gnsRep (a + b)).continuous
    · exact (φ.gnsRep a + φ.gnsRep b).continuous
  | ih y =>
    simp only [gnsRep_coe, gnsPreRep_add, LinearMap.add_apply,
      ContinuousLinearMap.add_apply, UniformSpace.Completion.coe_add]

end State
