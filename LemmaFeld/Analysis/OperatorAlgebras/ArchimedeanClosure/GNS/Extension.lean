/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Bounded
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.ComplexifyGNS
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.ComplexifyMap

/-! # GNS Representation Extension

This file extends the pre-representation from the GNS quotient to the Hilbert space.

## Main definitions

* `MPositiveState.gnsBoundedPreRep` - Pre-representation as ContinuousLinearMap
* `MPositiveState.gnsRep` - GNS representation extended to the Hilbert space

## Implementation Notes

The quotient A₀/N_φ has two incompatible TopologicalSpace instances:
1. Quotient module topology (from Submodule.Quotient)
2. Seminormed topology (from gnsQuotientNormedAddCommGroup)

We must use explicit @ syntax to select the seminormed topology consistently.
See docs/GNS/learnings/completion-topology.md for details.
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} [IsArchimedean n] (φ : MPositiveState n)

/-! ### Pre-representation as ContinuousLinearMap -/

/-- The pre-representation as a continuous linear map on the quotient.

Uses explicit @ syntax to resolve the topology diamond. All instances
are derived from gnsQuotientNormedAddCommGroup for consistency. -/
noncomputable def gnsBoundedPreRep (a : FreeStarAlgebra n) :
    @ContinuousLinearMap ℝ ℝ _ _ (RingHom.id ℝ) φ.gnsQuotient
      (@UniformSpace.toTopologicalSpace _ φ.gnsQuotientNormedAddCommGroup.toUniformSpace)
      φ.gnsQuotientNormedAddCommGroup.toAddCommMonoid φ.gnsQuotient
      (@UniformSpace.toTopologicalSpace _ φ.gnsQuotientNormedAddCommGroup.toUniformSpace)
      φ.gnsQuotientNormedAddCommGroup.toAddCommMonoid
      φ.gnsQuotientNormedSpace.toModule φ.gnsQuotientNormedSpace.toModule :=
  @LinearMap.mkContinuous ℝ ℝ φ.gnsQuotient φ.gnsQuotient _ _
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
    φ.gnsQuotientNormedSpace.toModule φ.gnsQuotientNormedSpace.toModule
    (RingHom.id ℝ) (φ.gnsPreRep a) (Real.sqrt (archimedeanBound a))
    (fun x => φ.gnsLeftAction_bounded a x)

/-- The pre-representation is uniformly continuous with respect to the seminormed topology.

The letI establishes the SeminormedAddCommGroup instance, which brings:
- UniformSpace (from PseudoMetricSpace)
- IsUniformAddGroup (from SeminormedAddCommGroup.to_isUniformAddGroup)
Both are required by ContinuousLinearMap.uniformContinuous. -/
theorem gnsBoundedPreRep_uniformContinuous (a : FreeStarAlgebra n) :
    @UniformContinuous _ _ φ.gnsQuotientNormedAddCommGroup.toUniformSpace
      φ.gnsQuotientNormedAddCommGroup.toUniformSpace (φ.gnsBoundedPreRep a) := by
  letI : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  exact (φ.gnsBoundedPreRep a).uniformContinuous

/-! ### Extension to Hilbert space completion -/

/-- The GNS representation extended to the real Hilbert space completion.

Uses UniformSpace.Completion.map with the uniformly continuous pre-rep.
The letI establishes SeminormedAddCommGroup, which brings:
- UniformSpace (from PseudoMetricSpace)
- IsUniformAddGroup (for Completion.induction and .uniformContinuous) -/
noncomputable def gnsRep (a : FreeStarAlgebra n) :
    φ.gnsHilbertSpaceReal →L[ℝ] φ.gnsHilbertSpaceReal := by
  letI : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  exact {
    toLinearMap := {
      toFun := UniformSpace.Completion.map (φ.gnsBoundedPreRep a)
      map_add' := fun x y => by
        have huc : UniformContinuous (φ.gnsBoundedPreRep a) :=
          (φ.gnsBoundedPreRep a).uniformContinuous
        induction x, y using UniformSpace.Completion.induction_on₂ with
        | hp =>
          refine isClosed_eq ?_ ?_
          · exact (UniformSpace.Completion.continuous_map).comp continuous_add
          · exact (UniformSpace.Completion.continuous_map).comp continuous_fst |>.add <|
              (UniformSpace.Completion.continuous_map).comp continuous_snd
        | ih x y =>
          simp only [← UniformSpace.Completion.coe_add,
            UniformSpace.Completion.map_coe huc, (φ.gnsBoundedPreRep a).map_add]
      map_smul' := fun c x => by
        have huc : UniformContinuous (φ.gnsBoundedPreRep a) :=
          (φ.gnsBoundedPreRep a).uniformContinuous
        induction x using UniformSpace.Completion.induction_on with
        | hp =>
          refine isClosed_eq ?_ ?_
          · exact (UniformSpace.Completion.continuous_map).comp (continuous_const_smul c)
          · exact (continuous_const_smul c).comp (UniformSpace.Completion.continuous_map)
        | ih x =>
          simp only [RingHom.id_apply, ← UniformSpace.Completion.coe_smul,
            UniformSpace.Completion.map_coe huc, (φ.gnsBoundedPreRep a).map_smul]
    }
    cont := UniformSpace.Completion.continuous_map
  }

/-! ### Properties of gnsRep -/

/-- gnsRep agrees with gnsBoundedPreRep on quotient elements (embedded in completion). -/
theorem gnsRep_coe (a : FreeStarAlgebra n) (x : φ.gnsQuotient) :
    φ.gnsRep a x = φ.gnsBoundedPreRep a x := by
  letI : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  have huc : UniformContinuous (φ.gnsBoundedPreRep a) :=
    (φ.gnsBoundedPreRep a).uniformContinuous
  exact UniformSpace.Completion.map_coe huc x

/-- The representation is additive in the algebra element. -/
theorem gnsRep_add (a b : FreeStarAlgebra n) :
    φ.gnsRep (a + b) = φ.gnsRep a + φ.gnsRep b := by
  letI : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    refine isClosed_eq ?_ ?_
    · exact (φ.gnsRep (a + b)).continuous
    · exact (φ.gnsRep a + φ.gnsRep b).continuous
  | ih y =>
    simp only [gnsRep_coe, ContinuousLinearMap.add_apply]
    -- Goal: ↑(gnsBoundedPreRep (a+b) y) = ↑(gnsBoundedPreRep a y) + ↑(gnsBoundedPreRep b y)
    -- The underlying linear maps agree by gnsPreRep_add
    have heq : φ.gnsBoundedPreRep (a + b) y = φ.gnsBoundedPreRep a y + φ.gnsBoundedPreRep b y := by
      -- gnsBoundedPreRep is mkContinuous applied to gnsPreRep
      -- So the function value is just the gnsPreRep value
      change (φ.gnsPreRep (a + b)) y = (φ.gnsPreRep a) y + (φ.gnsPreRep b) y
      rw [φ.gnsPreRep_add]
      rfl
    simp only [heq, UniformSpace.Completion.coe_add]

/-- The representation sends 1 to the identity. -/
theorem gnsRep_one : φ.gnsRep 1 = ContinuousLinearMap.id ℝ _ := by
  letI : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    refine isClosed_eq ?_ ?_
    · exact (φ.gnsRep 1).continuous
    · exact continuous_id
  | ih y =>
    simp only [gnsRep_coe, ContinuousLinearMap.id_apply]
    -- Goal: ↑(gnsBoundedPreRep 1 y) = ↑y
    have heq : φ.gnsBoundedPreRep 1 y = y := by
      change (φ.gnsPreRep 1) y = y
      rw [φ.gnsPreRep_one]
      rfl
    simp only [heq]

/-- The representation preserves multiplication: π(a*b) = π(a) ∘ π(b). -/
theorem gnsRep_mul (a b : FreeStarAlgebra n) :
    φ.gnsRep (a * b) = (φ.gnsRep a).comp (φ.gnsRep b) := by
  letI : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  ext x
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    refine isClosed_eq ?_ ?_
    · exact (φ.gnsRep (a * b)).continuous
    · exact ((φ.gnsRep a).comp (φ.gnsRep b)).continuous
  | ih y =>
    simp only [gnsRep_coe, ContinuousLinearMap.comp_apply]
    -- Goal: ↑(gnsBoundedPreRep (a*b) y) = ↑(gnsBoundedPreRep a (gnsBoundedPreRep b y))
    congr 1
    -- Goal: gnsBoundedPreRep (a*b) y = gnsBoundedPreRep a (gnsBoundedPreRep b y)
    change (φ.gnsPreRep (a * b)) y = (φ.gnsPreRep a) ((φ.gnsPreRep b) y)
    rw [φ.gnsPreRep_mul]
    rfl

end MPositiveState

end FreeStarAlgebra
