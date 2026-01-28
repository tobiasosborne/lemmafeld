/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Quotient
import Mathlib.Analysis.InnerProductSpace.Completion

/-! # GNS Hilbert Space Completion

This file completes the GNS quotient to a real Hilbert space.

## Main definitions

* `MPositiveState.gnsInnerProductCore` - The InnerProductSpace.Core instance
* `MPositiveState.gnsHilbertSpaceReal` - The completion (a real Hilbert space)
* `MPositiveState.gnsCyclicVector` - The cyclic vector [1]

## Implementation Notes

The GNS quotient has a REAL inner product structure because:
- MPositiveState maps FreeStarAlgebra n →ₗ[ℝ] ℝ
- The inner product ⟨[a], [b]⟩ = φ(star b * a) is ℝ-valued

The completed space is therefore a real Hilbert space. To obtain a complex Hilbert
space (as required by ConstrainedStarRep), complexification is needed - see
LEARNINGS.md for discussion of this architectural gap.
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} (φ : MPositiveState n)

/-! ### InnerProductSpace.Core (with positive definiteness) -/

/-- The InnerProductSpace.Core instance, adding positive definiteness to the
PreInnerProductSpace.Core structure. -/
noncomputable def gnsInnerProductCore : InnerProductSpace.Core ℝ φ.gnsQuotient where
  __ := φ.gnsPreInnerProductCore
  definite x h := (φ.gnsInner_self_eq_zero_iff x).mp h

/-! ### Normed structures from Core -/

/-- The NormedAddCommGroup structure on the quotient. -/
noncomputable def gnsQuotientNormedAddCommGroup : NormedAddCommGroup φ.gnsQuotient :=
  @InnerProductSpace.Core.toNormedAddCommGroup ℝ φ.gnsQuotient _ _ _ φ.gnsInnerProductCore

/-- The NormedSpace structure on the quotient.

Uses explicit @ to match the SeminormedAddCommGroup from gnsQuotientNormedAddCommGroup. -/
noncomputable def gnsQuotientNormedSpace :
    @NormedSpace ℝ φ.gnsQuotient _ φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup :=
  @InnerProductSpace.Core.toNormedSpace ℝ φ.gnsQuotient _ _ _ φ.gnsPreInnerProductCore

/-! ### The completion (real Hilbert space) -/

/-- The GNS Hilbert space is the completion of the quotient.

**Note**: This is a REAL Hilbert space. For a complex Hilbert space,
complexification is required. -/
noncomputable abbrev gnsHilbertSpaceReal :=
  @UniformSpace.Completion φ.gnsQuotient φ.gnsQuotientNormedAddCommGroup.toUniformSpace

/-! ### The cyclic vector -/

/-- The cyclic vector Ω = [1] embedded in the completion.

This is the image of the identity element 1 ∈ A₀ under the composition
A₀ → A₀/N_φ → Completion(A₀/N_φ). -/
noncomputable def gnsCyclicVector : φ.gnsHilbertSpaceReal :=
  @UniformSpace.Completion.coe' φ.gnsQuotient φ.gnsQuotientNormedAddCommGroup.toUniformSpace
    (Submodule.Quotient.mk 1)

/-! ### Norm of [1] in the quotient -/

/-- The inner product ⟨[1], [1]⟩ = 1 in the quotient. -/
theorem gnsInner_one_one : φ.gnsInner (Submodule.Quotient.mk 1) (Submodule.Quotient.mk 1) = 1 := by
  simp only [gnsInner_mk, star_one, one_mul, φ.apply_one]

/-- The quotient element [1] has norm 1.

**Proof:**
Using the Core norm: ‖x‖ = sqrt(re⟨x,x⟩). For x = [1]:
- ⟨[1], [1]⟩ = φ(star 1 * 1) = φ(1) = 1
- So ‖[1]‖ = sqrt(1) = 1 -/
theorem gnsQuotient_one_norm :
    @Norm.norm _ φ.gnsQuotientNormedAddCommGroup.toNorm (Submodule.Quotient.mk 1) = 1 := by
  -- The norm from InnerProductSpace.Core is sqrt(⟨x,x⟩)
  have h := @InnerProductSpace.Core.norm_eq_sqrt_re_inner ℝ φ.gnsQuotient _ _ _
      φ.gnsPreInnerProductCore (Submodule.Quotient.mk 1)
  -- Need to show the inner product in h equals gnsInner
  have h_inner : @inner ℝ _ φ.gnsPreInnerProductCore.toInner (Submodule.Quotient.mk 1)
      (Submodule.Quotient.mk 1) = φ.gnsInner _ _ := rfl
  rw [h, h_inner, RCLike.re_to_real, gnsInner_one_one, Real.sqrt_one]

/-! ### Norm of cyclic vector in completion -/

/-- The cyclic vector Ω has norm 1 in the completion.

**Proof:**
The embedding coe' : A₀/N_φ → Completion preserves norms.
By gnsQuotient_one_norm, ‖[1]‖ = 1 in the quotient.
Hence ‖Ω‖ = ‖coe'([1])‖ = ‖[1]‖ = 1. -/
theorem gnsCyclicVector_norm :
    @Norm.norm _ (@SeminormedAddCommGroup.toNorm _
      (@NormedAddCommGroup.toSeminormedAddCommGroup _
        (@UniformSpace.Completion.instNormedAddCommGroup φ.gnsQuotient
          φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup))) φ.gnsCyclicVector = 1 := by
  -- Unfold gnsCyclicVector to expose coe' structure
  unfold gnsCyclicVector
  -- Use norm_coe: ‖coe' x‖ = ‖x‖
  rw [@UniformSpace.Completion.norm_coe φ.gnsQuotient
      φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup]
  exact gnsQuotient_one_norm φ

end MPositiveState

end FreeStarAlgebra
