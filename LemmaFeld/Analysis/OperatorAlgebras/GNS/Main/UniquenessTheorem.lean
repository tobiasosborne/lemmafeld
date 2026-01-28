/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Main.UniquenessIntertwine

/-!
# GNS Uniqueness Theorem

The GNS representation is unique up to unitary equivalence.

## Main results

* `State.gns_uniqueness` - The GNS uniqueness theorem

## Mathematical Statement

Given any cyclic *-representation (H, π, ξ) with:
- π : A →⋆ₐ[ℂ] B(H) is a *-representation
- ‖ξ‖ = 1
- φ(a) = ⟨ξ, π(a)ξ⟩ for all a ∈ A
- {π(a)ξ : a ∈ A} is dense in H

There exists a unitary U : H_φ ≃ₗᵢ[ℂ] H such that:
- U(Ω_φ) = ξ
- U ∘ π_φ(a) = π(a) ∘ U for all a ∈ A
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

/-- **GNS Uniqueness Theorem**: The GNS representation is unique up to unitary equivalence.

Given any cyclic *-representation (H, π, ξ) satisfying the state condition φ(a) = ⟨ξ, π(a)ξ⟩
and cyclicity (the orbit {π(a)ξ : a ∈ A} is dense in H), there exists a unitary
U : H_φ ≃ₗᵢ[ℂ] H that:
1. Maps the canonical cyclic vector to ξ: U(Ω_φ) = ξ
2. Intertwines the representations: U ∘ π_φ(a) = π(a) ∘ U for all a ∈ A

This establishes that all cyclic *-representations implementing the same state are
unitarily equivalent to the GNS representation. -/
theorem gns_uniqueness
    (_hξ_norm : ‖ξ‖ = 1)
    (hξ_cyclic : DenseRange (fun a => π a ξ))
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    ∃ U : φ.gnsHilbertSpace ≃ₗᵢ[ℂ] H,
      U φ.gnsCyclicVector = ξ ∧
      ∀ a : A, ∀ x : φ.gnsHilbertSpace, U (φ.gnsRep a x) = π a (U x) :=
  ⟨gnsIntertwinerEquiv φ π ξ hξ_state hξ_cyclic,
   gnsIntertwinerEquiv_cyclic φ π ξ hξ_state hξ_cyclic,
   gnsIntertwiner_intertwines φ π ξ hξ_state hξ_cyclic⟩

end State
