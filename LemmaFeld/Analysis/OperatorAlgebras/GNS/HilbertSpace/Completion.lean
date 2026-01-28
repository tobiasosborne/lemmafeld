/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.PreHilbert.Positive
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# GNS Hilbert Space Completion

This file completes the pre-Hilbert space A/N_φ to get the GNS Hilbert space H_φ.

## Main definitions

* `State.gnsHilbertSpace` - The GNS Hilbert space H_φ = completion of A/N_φ

## Main results

* `InnerProductSpace` and `CompleteSpace` instances on the completion

## Note

Most of the heavy lifting is done by mathlib's completion machinery.
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### Normed structure on quotient -/

/-- The SeminormedAddCommGroup structure on the GNS quotient.
    Derived from the PreInnerProductSpace.Core. -/
noncomputable instance gnsQuotientSeminormedAddCommGroup :
    SeminormedAddCommGroup φ.gnsQuotient :=
  @InnerProductSpace.Core.toSeminormedAddCommGroup ℂ _ _ _ _ φ.gnsPreInnerProductCore

/-- The NormedSpace structure on the GNS quotient. -/
noncomputable instance gnsQuotientNormedSpace : NormedSpace ℂ φ.gnsQuotient :=
  @InnerProductSpace.Core.toNormedSpace ℂ _ _ _ _ φ.gnsPreInnerProductCore

/-! ### InnerProductSpace instance on quotient -/

/-- The GNS quotient is an inner product space. -/
noncomputable instance gnsQuotientInnerProductSpace : InnerProductSpace ℂ φ.gnsQuotient := {
  gnsQuotientNormedSpace φ with
  inner := φ.gnsPreInnerProductCore.inner
  norm_sq_eq_re_inner := fun x => by
    rw [@InnerProductSpace.Core.norm_eq_sqrt_re_inner ℂ _ _ _ _ φ.gnsPreInnerProductCore x]
    rw [Real.sq_sqrt (φ.gnsPreInnerProductCore.re_inner_nonneg x)]
  conj_inner_symm := φ.gnsPreInnerProductCore.conj_inner_symm
  add_left := φ.gnsPreInnerProductCore.add_left
  smul_left := φ.gnsPreInnerProductCore.smul_left
}

/-! ### The GNS Hilbert space -/

/-- The GNS Hilbert space H_φ = completion of A/N_φ. -/
abbrev gnsHilbertSpace := UniformSpace.Completion φ.gnsQuotient

/-- The GNS Hilbert space is complete. -/
instance gnsHilbertSpaceCompleteSpace : CompleteSpace φ.gnsHilbertSpace :=
  UniformSpace.Completion.completeSpace φ.gnsQuotient

/-- The GNS Hilbert space is an inner product space. -/
noncomputable instance gnsHilbertSpaceInnerProductSpace :
    InnerProductSpace ℂ φ.gnsHilbertSpace :=
  inferInstance

end State
