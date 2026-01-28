/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Main.UniquenessExtension

/-!
# GNS Intertwiner as Linear Isometry Equivalence

Constructs the intertwiner U as a `LinearIsometryEquiv H_φ ≃ₗᵢ[ℂ] H`.

## Main definitions

* `gnsIntertwinerEquiv` - The intertwiner as a linear isometry equivalence

## Main results

* `gnsIntertwiner_injective` - The intertwiner is injective (isometries are injective)
* `gnsIntertwiner_bijective` - The intertwiner is bijective
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

/-! ### Injectivity and Bijectivity (GNS-U8) -/

/-- The intertwiner U is injective. Isometries between metric spaces are injective. -/
theorem gnsIntertwiner_injective
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    Function.Injective (gnsIntertwiner φ π ξ hξ_state) :=
  (gnsIntertwinerFun_isometry φ π ξ hξ_state).injective

/-- The intertwiner U is bijective: injective (isometry) + surjective (GNS-U7). -/
theorem gnsIntertwiner_bijective
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (hξ_cyclic : DenseRange (fun a => π a ξ)) :
    Function.Bijective (gnsIntertwiner φ π ξ hξ_state) :=
  ⟨gnsIntertwiner_injective φ π ξ hξ_state,
   gnsIntertwiner_surjective φ π ξ hξ_state hξ_cyclic⟩

/-- The intertwiner as a LinearEquiv, constructed from bijectivity. -/
noncomputable def gnsIntertwinerLinearEquiv
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (hξ_cyclic : DenseRange (fun a => π a ξ)) :
    φ.gnsHilbertSpace ≃ₗ[ℂ] H :=
  LinearEquiv.ofBijective (gnsIntertwiner φ π ξ hξ_state).toLinearMap
    (gnsIntertwiner_bijective φ π ξ hξ_state hξ_cyclic)

/-- The LinearEquiv agrees with gnsIntertwiner on all elements. -/
@[simp]
theorem gnsIntertwinerLinearEquiv_apply
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (hξ_cyclic : DenseRange (fun a => π a ξ))
    (x : φ.gnsHilbertSpace) :
    gnsIntertwinerLinearEquiv φ π ξ hξ_state hξ_cyclic x = gnsIntertwiner φ π ξ hξ_state x :=
  rfl

/-- The intertwiner as a LinearIsometryEquiv H_φ ≃ₗᵢ[ℂ] H.
    This is the unitary operator witnessing uniqueness of GNS representation. -/
noncomputable def gnsIntertwinerEquiv
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (hξ_cyclic : DenseRange (fun a => π a ξ)) :
    φ.gnsHilbertSpace ≃ₗᵢ[ℂ] H where
  toLinearEquiv := gnsIntertwinerLinearEquiv φ π ξ hξ_state hξ_cyclic
  norm_map' := gnsIntertwiner_norm φ π ξ hξ_state

/-- The LinearIsometryEquiv agrees with gnsIntertwiner on all elements. -/
@[simp]
theorem gnsIntertwinerEquiv_apply
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (hξ_cyclic : DenseRange (fun a => π a ξ))
    (x : φ.gnsHilbertSpace) :
    gnsIntertwinerEquiv φ π ξ hξ_state hξ_cyclic x = gnsIntertwiner φ π ξ hξ_state x :=
  rfl

/-! ### Cyclic vector mapping (GNS-U9) -/

/-- The intertwiner sends the GNS cyclic vector Ω_φ to ξ.
    This is a key property for uniqueness: the unitary equivalence maps
    the canonical cyclic vector to the given cyclic vector.

    Proof: Ω_φ = [1] embedded, and U([1]) = π(1)ξ = ξ by gnsIntertwinerQuotient_cyclic. -/
theorem gnsIntertwinerEquiv_cyclic
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (hξ_cyclic : DenseRange (fun a => π a ξ)) :
    gnsIntertwinerEquiv φ π ξ hξ_state hξ_cyclic φ.gnsCyclicVector = ξ := by
  -- gnsIntertwinerEquiv agrees with gnsIntertwiner
  rw [gnsIntertwinerEquiv_apply]
  -- gnsCyclicVector is the embedded quotient element [1]
  rw [gnsCyclicVector_eq_coe]
  -- gnsIntertwiner on embedded element equals gnsIntertwinerQuotientFun
  rw [gnsIntertwiner_coe]
  -- gnsIntertwinerQuotientFun on [1] equals ξ
  exact gnsIntertwinerQuotient_cyclic φ π ξ hξ_state

end State
