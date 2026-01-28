/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Completion
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.ComplexifyInner

/-! # Complexified GNS Hilbert Space

This file complexifies the real GNS Hilbert space to obtain a complex Hilbert space
suitable for use in ConstrainedStarRep.

## Main definitions

* `MPositiveState.gnsHilbertSpaceComplex` - The complexification of gnsHilbertSpaceReal
* `MPositiveState.gnsCyclicVectorComplex` - The cyclic vector in the complex space

## Mathematical Background

The GNS construction produces a real Hilbert space H_ℝ. To obtain a complex Hilbert
space (as required by ConstrainedStarRep), we complexify:

H_ℂ = H_ℝ ⊕ iH_ℝ = {(x, y) : x, y ∈ H_ℝ}

with complex scalar multiplication (a + bi)·(x, y) = (ax - by, ay + bx).

The cyclic vector Ω ∈ H_ℝ embeds as (Ω, 0) ∈ H_ℂ.
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} (φ : MPositiveState n)

open ArchimedeanClosure

/-! ### Instances for Real GNS Hilbert Space -/

/-- The NormedAddCommGroup instance on the completed real GNS space. -/
noncomputable instance gnsHilbertSpaceRealNormedAddCommGroup :
    NormedAddCommGroup φ.gnsHilbertSpaceReal :=
  @UniformSpace.Completion.instNormedAddCommGroup φ.gnsQuotient
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup

/-- The InnerProductSpace instance on the completed real GNS space. -/
noncomputable instance gnsHilbertSpaceRealInnerProductSpace :
    InnerProductSpace ℝ φ.gnsHilbertSpaceReal :=
  @UniformSpace.Completion.innerProductSpace ℝ φ.gnsQuotient _
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
    (@InnerProductSpace.ofCore ℝ _ _ _ _ φ.gnsInnerProductCore.toCore)

/-! ### The Complexified GNS Hilbert Space -/

/-- The complexified GNS Hilbert space.

This is a complex Hilbert space obtained by complexifying the real GNS completion. -/
noncomputable abbrev gnsHilbertSpaceComplex : Type :=
  Complexification φ.gnsHilbertSpaceReal

/-! ### The Cyclic Vector in Complex Space -/

/-- The cyclic vector embedded in the complexified space.

Ω_ℂ = (Ω_ℝ, 0) where Ω_ℝ is the real cyclic vector. -/
noncomputable def gnsCyclicVectorComplex : φ.gnsHilbertSpaceComplex :=
  Complexification.embed φ.gnsCyclicVector

/-- The complex cyclic vector has norm 1. -/
theorem gnsCyclicVectorComplex_norm : ‖φ.gnsCyclicVectorComplex‖ = 1 := by
  rw [gnsCyclicVectorComplex, Complexification.embed_norm, gnsCyclicVector_norm]

end MPositiveState

end FreeStarAlgebra
