/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Representation.Extension

/-!
# GNS Vector State Theorem

This file proves the fundamental GNS identity: φ(a) = ⟨Ω_φ, π_φ(a)Ω_φ⟩.

## Main results

* `State.gns_vector_state` - φ(a) = ⟪Ω_φ, gnsRep φ a Ω_φ⟫

## Mathematical Background

The GNS construction produces a Hilbert space H_φ, a representation π_φ : A → B(H_φ),
and a cyclic vector Ω_φ. The key identity is that the original state φ can be
recovered as a vector state:

  φ(a) = ⟨Ω_φ, π_φ(a)Ω_φ⟩

This shows that every state arises from a vector state in some representation.

### Proof sketch
- π_φ(a)Ω_φ = [a·1] = [a] by definition of the representation
- ⟨Ω_φ, [a]⟩ = ⟨[1], [a]⟩ = φ(1*·a) = φ(a)
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### The vector state theorem -/

/-- The inner product of the cyclic vector with an element [a] in the quotient.
    Note: Uses inner_eq_gnsInner_swap since mathlib's inner has swapped arguments. -/
theorem gnsCyclicVectorQuotient_inner_mk (a : A) :
    @inner ℂ _ φ.gnsQuotientInner φ.gnsCyclicVectorQuotient (Submodule.Quotient.mk a) = φ a := by
  unfold gnsCyclicVectorQuotient
  rw [inner_eq_gnsInner_swap, gnsInner_mk]
  simp only [star_one, one_mul]

/-- The inner product ⟨Ω_φ, [a]⟩ in the Hilbert space equals φ(a). -/
theorem gnsCyclicVector_inner_mk (a : A) :
    @inner ℂ φ.gnsHilbertSpace _ φ.gnsCyclicVector
      (Submodule.Quotient.mk (p := φ.gnsNullIdeal) a : φ.gnsHilbertSpace) = φ a := by
  rw [gnsCyclicVector_eq_coe]
  rw [UniformSpace.Completion.inner_coe]
  exact gnsCyclicVectorQuotient_inner_mk φ a

/-- **The GNS Vector State Theorem**: φ(a) = ⟪Ω_φ, π_φ(a)Ω_φ⟫.

This is the fundamental identity of the GNS construction, showing that every
state on a C*-algebra can be represented as a vector state. -/
theorem gns_vector_state (a : A) :
    φ a = @inner ℂ φ.gnsHilbertSpace _ φ.gnsCyclicVector (φ.gnsRep a φ.gnsCyclicVector) := by
  rw [gnsRep_cyclicVector]
  exact (gnsCyclicVector_inner_mk φ a).symm

/-- Alternative formulation: the representation recovers the state. -/
theorem gnsRep_recovers_state (a : A) :
    @inner ℂ φ.gnsHilbertSpace _ φ.gnsCyclicVector (φ.gnsRep a φ.gnsCyclicVector) = φ a :=
  (gns_vector_state φ a).symm

end State
