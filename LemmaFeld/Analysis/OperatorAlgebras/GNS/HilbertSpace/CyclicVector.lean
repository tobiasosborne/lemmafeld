/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.HilbertSpace.Completion

/-!
# GNS Cyclic Vector

This file defines the cyclic vector Ω_φ = [1] in the GNS Hilbert space.

## Main definitions

* `State.gnsCyclicVector` - The cyclic vector Ω_φ in the GNS Hilbert space

## Main results

* `State.gnsCyclicVector_inner_self` - ⟪Ω_φ, Ω_φ⟫ = 1
* `State.gnsCyclicVector_norm` - ‖Ω_φ‖ = 1

## Mathematical Background

The cyclic vector Ω_φ is the image of the identity element 1 ∈ A in the GNS
Hilbert space H_φ. Its key properties are:
1. ‖Ω_φ‖ = 1 (follows from φ(1) = 1)
2. The orbit {π_φ(a)Ω_φ : a ∈ A} is dense in H_φ (cyclicity)
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### The cyclic vector -/

/-- The cyclic vector Ω_φ = [1] in the GNS Hilbert space.
    This is the embedding of the quotient class of 1 ∈ A. -/
noncomputable def gnsCyclicVector : φ.gnsHilbertSpace :=
  (Submodule.Quotient.mk (p := φ.gnsNullIdeal) 1 : φ.gnsQuotient)

/-- The cyclic vector as a quotient element (before completion). -/
noncomputable def gnsCyclicVectorQuotient : φ.gnsQuotient :=
  Submodule.Quotient.mk (p := φ.gnsNullIdeal) 1

/-- The cyclic vector is the embedding of the quotient cyclic vector. -/
theorem gnsCyclicVector_eq_coe :
    φ.gnsCyclicVector = (φ.gnsCyclicVectorQuotient : φ.gnsHilbertSpace) := rfl

/-! ### Inner product of the cyclic vector -/

/-- The inner product ⟪Ω_φ, Ω_φ⟫ in the quotient is φ(1). -/
theorem gnsCyclicVectorQuotient_inner_self :
    @inner ℂ _ φ.gnsQuotientInner φ.gnsCyclicVectorQuotient φ.gnsCyclicVectorQuotient = 1 := by
  unfold gnsCyclicVectorQuotient
  rw [inner_eq_gnsInner_swap, gnsInner_mk]
  simp only [star_one, one_mul]
  exact φ.apply_one

/-- The inner product ⟪Ω_φ, Ω_φ⟫ in the Hilbert space is 1.
    Proof: inner product is preserved under the embedding. -/
theorem gnsCyclicVector_inner_self :
    @inner ℂ _ _ φ.gnsCyclicVector φ.gnsCyclicVector = 1 := by
  rw [gnsCyclicVector_eq_coe]
  rw [UniformSpace.Completion.inner_coe]
  exact gnsCyclicVectorQuotient_inner_self φ

/-! ### Norm of the cyclic vector -/

/-- The norm ‖Ω_φ‖ in the quotient is 1. -/
theorem gnsCyclicVectorQuotient_norm : ‖φ.gnsCyclicVectorQuotient‖ = 1 := by
  rw [@InnerProductSpace.Core.norm_eq_sqrt_re_inner ℂ _ _ _ _ φ.gnsPreInnerProductCore]
  unfold gnsCyclicVectorQuotient
  simp only [inner_eq_gnsInner_swap, gnsInner_mk, star_one, one_mul, apply_one]
  simp only [RCLike.one_re, Real.sqrt_one]

/-- The norm ‖Ω_φ‖ = 1.
    Proof: ‖Ω_φ‖ = ‖embed (mk 1)‖ = ‖mk 1‖ (isometry) = √(φ(1*1)).re = √1 = 1 -/
theorem gnsCyclicVector_norm : ‖φ.gnsCyclicVector‖ = 1 := by
  rw [gnsCyclicVector_eq_coe]
  rw [UniformSpace.Completion.norm_coe]
  exact gnsCyclicVectorQuotient_norm φ

/-- The cyclic vector is nonzero. -/
theorem gnsCyclicVector_ne_zero : φ.gnsCyclicVector ≠ 0 := by
  intro h
  have : ‖φ.gnsCyclicVector‖ = 0 := by rw [h, norm_zero]
  rw [gnsCyclicVector_norm] at this
  exact one_ne_zero this

end State
