/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Main.Uniqueness
import Mathlib.Topology.MetricSpace.Completion

/-!
# GNS Intertwiner Extension

Extends the quotient-level intertwiner U₀ : A/N_φ →ₗᵢ[ℂ] H to the full Hilbert space H_φ.

## Main definitions

* `gnsIntertwinerFun` - The extended function H_φ → H via completion extension

## Main results

* `gnsIntertwinerFun_coe` - Extension agrees with U₀ on embedded quotient elements
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

/-! ### Extension to Hilbert space -/

/-- The underlying function of U₀ is uniformly continuous (isometries are).
    This allows extension to the completion. -/
theorem gnsIntertwinerQuotientFun_uniformContinuous
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    UniformContinuous (gnsIntertwinerQuotientFun φ π ξ hξ_state) :=
  (gnsIntertwinerQuotientLinearIsometry φ π ξ hξ_state).isometry.uniformContinuous

/-- Extend U₀ to the full Hilbert space H_φ = completion of A/N_φ.
    Uses the universal property of completions: uniformly continuous maps extend uniquely. -/
noncomputable def gnsIntertwinerFun
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) : φ.gnsHilbertSpace → H :=
  UniformSpace.Completion.extension (gnsIntertwinerQuotientFun φ π ξ hξ_state)

/-- The extension agrees with U₀ on embedded quotient elements. -/
theorem gnsIntertwinerFun_coe
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (x : φ.gnsQuotient) :
    gnsIntertwinerFun φ π ξ hξ_state x = gnsIntertwinerQuotientFun φ π ξ hξ_state x := by
  unfold gnsIntertwinerFun
  exact UniformSpace.Completion.extension_coe
    (gnsIntertwinerQuotientFun_uniformContinuous φ π ξ hξ_state) x

/-- The extension is continuous. -/
theorem gnsIntertwinerFun_continuous
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    Continuous (gnsIntertwinerFun φ π ξ hξ_state) :=
  UniformSpace.Completion.continuous_extension

/-- The extension preserves addition.
    Proof by density: both sides are continuous and agree on dense quotient. -/
theorem gnsIntertwinerFun_add
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (x y : φ.gnsHilbertSpace) :
    gnsIntertwinerFun φ π ξ hξ_state (x + y) =
    gnsIntertwinerFun φ π ξ hξ_state x + gnsIntertwinerFun φ π ξ hξ_state y := by
  refine UniformSpace.Completion.induction_on₂ x y ?_ ?_
  · exact isClosed_eq (gnsIntertwinerFun_continuous φ π ξ hξ_state |>.comp continuous_add)
        ((gnsIntertwinerFun_continuous φ π ξ hξ_state |>.comp continuous_fst).add
         (gnsIntertwinerFun_continuous φ π ξ hξ_state |>.comp continuous_snd))
  · intro a b
    simp only [← UniformSpace.Completion.coe_add]
    rw [gnsIntertwinerFun_coe, gnsIntertwinerFun_coe, gnsIntertwinerFun_coe]
    exact gnsIntertwinerQuotient_add φ π ξ hξ_state a b

/-- The extension preserves scalar multiplication.
    Proof by density: both sides are continuous and agree on dense quotient. -/
theorem gnsIntertwinerFun_smul
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (c : ℂ) (x : φ.gnsHilbertSpace) :
    gnsIntertwinerFun φ π ξ hξ_state (c • x) =
    c • gnsIntertwinerFun φ π ξ hξ_state x := by
  refine UniformSpace.Completion.induction_on x ?_ ?_
  · have hc1 := gnsIntertwinerFun_continuous φ π ξ hξ_state |>.comp (continuous_const_smul c)
    have hc2 := (continuous_const_smul c).comp (gnsIntertwinerFun_continuous φ π ξ hξ_state)
    exact isClosed_eq hc1 hc2
  · intro a
    simp only [← UniformSpace.Completion.coe_smul]
    rw [gnsIntertwinerFun_coe, gnsIntertwinerFun_coe]
    exact gnsIntertwinerQuotient_smul φ π ξ hξ_state c a

/-- The extended intertwiner as a ContinuousLinearMap H_φ →L[ℂ] H. -/
noncomputable def gnsIntertwiner
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) : φ.gnsHilbertSpace →L[ℂ] H where
  toFun := gnsIntertwinerFun φ π ξ hξ_state
  map_add' := gnsIntertwinerFun_add φ π ξ hξ_state
  map_smul' := gnsIntertwinerFun_smul φ π ξ hξ_state
  cont := gnsIntertwinerFun_continuous φ π ξ hξ_state

/-- The ContinuousLinearMap agrees with U₀ on embedded quotient elements. -/
@[simp]
theorem gnsIntertwiner_coe
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (x : φ.gnsQuotient) :
    gnsIntertwiner φ π ξ hξ_state x = gnsIntertwinerQuotientFun φ π ξ hξ_state x :=
  gnsIntertwinerFun_coe φ π ξ hξ_state x

/-! ### Extension is isometry (GNS-U5) -/

/-- The quotient-level intertwiner is an isometry as a function. -/
theorem gnsIntertwinerQuotientFun_isometry
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    Isometry (gnsIntertwinerQuotientFun φ π ξ hξ_state) :=
  (gnsIntertwinerQuotientLinearIsometry φ π ξ hξ_state).isometry

/-- The extended intertwiner is an isometry.
    Uses Isometry.completion_extension: if f is an isometry into a complete space,
    then its extension to the completion is also an isometry. -/
theorem gnsIntertwinerFun_isometry
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    Isometry (gnsIntertwinerFun φ π ξ hξ_state) :=
  (gnsIntertwinerQuotientFun_isometry φ π ξ hξ_state).completion_extension

/-- The extended intertwiner maps zero to zero. -/
theorem gnsIntertwinerFun_map_zero
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    gnsIntertwinerFun φ π ξ hξ_state 0 = 0 :=
  (gnsIntertwiner φ π ξ hξ_state).map_zero

/-- The extended intertwiner preserves norms: ‖U(x)‖ = ‖x‖. -/
theorem gnsIntertwiner_norm
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (x : φ.gnsHilbertSpace) :
    ‖gnsIntertwiner φ π ξ hξ_state x‖ = ‖x‖ :=
  (gnsIntertwinerFun_isometry φ π ξ hξ_state).norm_map_of_map_zero
    (gnsIntertwinerFun_map_zero φ π ξ hξ_state) x

/-- The extended intertwiner as a LinearIsometry H_φ →ₗᵢ[ℂ] H. -/
noncomputable def gnsIntertwinerLinearIsometry
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    φ.gnsHilbertSpace →ₗᵢ[ℂ] H where
  toLinearMap := (gnsIntertwiner φ π ξ hξ_state).toLinearMap
  norm_map' := gnsIntertwiner_norm φ π ξ hξ_state

/-! ### Dense range (GNS-U6) -/

/-- The range of U contains the orbit {π(a)ξ : a ∈ A}.
    Proof: U([a]) = π(a)ξ by definition, so π(a)ξ is in the range. -/
theorem gnsIntertwiner_range_contains_orbit
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) (a : A) :
    π a ξ ∈ Set.range (gnsIntertwiner φ π ξ hξ_state) := by
  -- U([a]) = π(a)ξ, so π(a)ξ is in the range
  use (Submodule.Quotient.mk (p := φ.gnsNullIdeal) a : φ.gnsHilbertSpace)
  -- gnsIntertwiner applied to embedded quotient element
  rw [gnsIntertwiner_coe]
  -- By definition of gnsIntertwinerQuotientFun
  rfl

/-- The orbit {π(a)ξ : a ∈ A} is contained in the range of U. -/
theorem gnsIntertwiner_orbit_subset_range
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    Set.range (fun a => π a ξ) ⊆ Set.range (gnsIntertwiner φ π ξ hξ_state) := by
  intro y hy
  obtain ⟨a, rfl⟩ := hy
  exact gnsIntertwiner_range_contains_orbit φ π ξ hξ_state a

/-- The range of U is dense in H.
    Proof: The orbit {π(a)ξ : a ∈ A} is dense (by cyclicity) and contained in range(U).
    By Dense.mono, range(U) is also dense. -/
theorem gnsIntertwiner_denseRange
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (hξ_cyclic : DenseRange (fun a => π a ξ)) :
    DenseRange (gnsIntertwiner φ π ξ hξ_state) :=
  hξ_cyclic.mono (gnsIntertwiner_orbit_subset_range φ π ξ hξ_state)

/-! ### Surjectivity (GNS-U7) -/

/-- An isometry with dense range from a complete space into a complete T0 space is surjective.
    The range is complete (image of complete under uniform inducing), hence closed.
    Dense + closed = whole space. -/
theorem Isometry.surjective_of_completeSpace_denseRange
    {X Y : Type*} [MetricSpace X] [MetricSpace Y] [CompleteSpace X] [CompleteSpace Y]
    {f : X → Y} (hf : Isometry f) (hd : DenseRange f) : Function.Surjective f :=
  Set.range_eq_univ.mp <| hf.isUniformInducing.isComplete_range.isClosed.closure_eq ▸
    dense_iff_closure_eq.mp hd

/-- The intertwiner U is surjective.
    Uses: H_φ is complete (Hilbert completion), H is complete (hypothesis),
    U is isometry (GNS-U5), U has dense range (GNS-U6). -/
theorem gnsIntertwiner_surjective
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (hξ_cyclic : DenseRange (fun a => π a ξ)) :
    Function.Surjective (gnsIntertwiner φ π ξ hξ_state) :=
  Isometry.surjective_of_completeSpace_denseRange
    (gnsIntertwinerFun_isometry φ π ξ hξ_state)
    (gnsIntertwiner_denseRange φ π ξ hξ_state hξ_cyclic)

end State
