/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Main.VectorState
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Representation.Star

/-!
# The GNS Construction Theorem

This file states the main Gelfand-Naimark-Segal construction theorem.

## Main results

* `State.gnsCyclicVector_denseRange` - The orbit {π_φ(a)Ω_φ : a ∈ A} is dense in H_φ
* `State.gns_theorem` - The complete GNS theorem

## Mathematical Background

The GNS construction shows that every state φ on a C*-algebra A can be
realized as a vector state. Given φ, we construct:
1. A Hilbert space H_φ (the completion of A/N_φ)
2. A *-representation π_φ : A → B(H_φ)
3. A cyclic unit vector Ω_φ ∈ H_φ

Such that:
- φ(a) = ⟨Ω_φ, π_φ(a)Ω_φ⟩ for all a ∈ A (vector state property)
- {π_φ(a)Ω_φ : a ∈ A} is dense in H_φ (cyclicity)
- ‖Ω_φ‖ = 1 (unit vector)
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### Cyclicity: Dense range of the orbit -/

/-- The quotient map A → A/N_φ is surjective, hence has dense range. -/
theorem gnsQuotientMk_denseRange :
    DenseRange (Submodule.Quotient.mk (p := φ.gnsNullIdeal)) :=
  Function.Surjective.denseRange (Submodule.Quotient.mk_surjective φ.gnsNullIdeal)

/-- The cyclic orbit {π_φ(a)Ω_φ : a ∈ A} is dense in the GNS Hilbert space.

This is the cyclicity condition: the vector Ω_φ is cyclic for the representation π_φ. -/
theorem gnsCyclicVector_denseRange :
    DenseRange (fun a : A => φ.gnsRep a φ.gnsCyclicVector) := by
  -- The range of (fun a => gnsRep a gnsCyclicVector) equals the range of coe'
  -- since Submodule.Quotient.mk is surjective.
  have h_range_eq : Set.range (fun a : A => φ.gnsRep a φ.gnsCyclicVector) =
      Set.range (UniformSpace.Completion.coe' (α := φ.gnsQuotient)) := by
    ext x
    constructor
    · rintro ⟨a, ha⟩
      refine ⟨Submodule.Quotient.mk a, ?_⟩
      simp only at ha ⊢
      rw [gnsRep_cyclicVector] at ha
      exact ha
    · rintro ⟨q, hq⟩
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal q
      refine ⟨a, ?_⟩
      simp only
      rw [gnsRep_cyclicVector]
      exact hq
  rw [DenseRange, h_range_eq]
  exact UniformSpace.Completion.denseRange_coe

/-! ### The main GNS theorem -/

/-- **The GNS Construction Theorem**: Every state on a C*-algebra arises as a vector state.

Given a state φ on a C*-algebra A, the GNS construction provides:
1. `gnsHilbertSpace φ` - A Hilbert space H_φ
2. `gnsStarAlgHom φ` - A *-representation π_φ : A →⋆ₐ[ℂ] B(H_φ)
3. `gnsCyclicVector φ` - A cyclic unit vector Ω_φ ∈ H_φ

With the fundamental properties:
- `gnsCyclicVector_norm` : ‖Ω_φ‖ = 1
- `gns_vector_state` : φ(a) = ⟨Ω_φ, π_φ(a)Ω_φ⟩
- `gnsCyclicVector_denseRange` : {π_φ(a)Ω_φ : a ∈ A} is dense in H_φ
-/
theorem gns_theorem :
    ‖φ.gnsCyclicVector‖ = 1 ∧
    (∀ a : A, φ a = @inner ℂ φ.gnsHilbertSpace _ φ.gnsCyclicVector
                      (φ.gnsRep a φ.gnsCyclicVector)) ∧
    DenseRange (fun a : A => φ.gnsRep a φ.gnsCyclicVector) :=
  ⟨gnsCyclicVector_norm φ, gns_vector_state φ, gnsCyclicVector_denseRange φ⟩

end State
