/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Main.UniquenessEquiv

/-!
# GNS Intertwining Property

Proves the intertwining property: U ∘ π_φ(a) = π(a) ∘ U.

## Main results

* `gnsIntertwiner_intertwines_quotient` - Intertwining on quotient elements
* `gnsIntertwiner_intertwines` - Full intertwining property on H_φ
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

/-! ### Intertwining on quotient (GNS-U10) -/

/-- The intertwiner intertwines on quotient elements: U(π_φ(a)[b]) = π(a)(U[b]).

    Proof: Both sides equal π(ab)ξ.
    - LHS: U(π_φ(a)[b]) = U([ab]) = π(ab)ξ
    - RHS: π(a)(U[b]) = π(a)(π(b)ξ) = π(ab)ξ -/
theorem gnsIntertwiner_intertwines_quotient
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (a : A) (x : φ.gnsQuotient) :
    gnsIntertwiner φ π ξ hξ_state (φ.gnsPreRep a x : φ.gnsHilbertSpace) =
    π a (gnsIntertwiner φ π ξ hξ_state (x : φ.gnsHilbertSpace)) := by
  -- Use quotient induction: x = [b] for some b : A
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal x
  -- Simplify gnsPreRep a [b] = [ab]
  simp only [gnsPreRep_mk]
  -- Now: gnsIntertwiner ([ab] : H_φ) = π(a)(gnsIntertwiner ([b] : H_φ))
  -- Use gnsIntertwiner_coe to reduce to quotient function
  rw [gnsIntertwiner_coe, gnsIntertwiner_coe]
  -- gnsIntertwinerQuotientFun [c] = π(c)ξ by definition (Quotient.liftOn)
  -- LHS: π(ab)ξ, RHS: π(a)(π(b)ξ)
  -- Show π(ab)ξ = π(a)(π(b)ξ) using multiplicativity of π
  change π (a * b) ξ = π a (π b ξ)
  rw [_root_.map_mul, ContinuousLinearMap.mul_apply]

/-! ### Full intertwining property (GNS-U11) -/

/-- The intertwining property: U ∘ π_φ(a) = π(a) ∘ U on all of H_φ.
    Extended from quotient by density and continuity.

    Proof: Both sides are continuous, and they agree on the dense quotient. -/
theorem gnsIntertwiner_intertwines
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (hξ_cyclic : DenseRange (fun a => π a ξ))
    (a : A) (x : φ.gnsHilbertSpace) :
    gnsIntertwinerEquiv φ π ξ hξ_state hξ_cyclic (φ.gnsRep a x) =
    π a (gnsIntertwinerEquiv φ π ξ hξ_state hξ_cyclic x) := by
  -- Use completion induction
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    -- Both sides are continuous, hence equal if they agree on dense subset
    apply isClosed_eq
    · -- LHS: gnsIntertwinerEquiv ∘ gnsRep a is continuous
      exact (gnsIntertwinerEquiv φ π ξ hξ_state hξ_cyclic).continuous.comp (φ.gnsRep a).continuous
    · -- RHS: π a ∘ gnsIntertwinerEquiv is continuous
      exact (π a).continuous.comp (gnsIntertwinerEquiv φ π ξ hξ_state hξ_cyclic).continuous
  | ih y =>
    -- On quotient elements, use gnsIntertwiner_intertwines_quotient
    simp only [gnsIntertwinerEquiv_apply]
    -- gnsRep a on embedded quotient equals embedded gnsPreRep a
    rw [gnsRep_coe]
    -- Now apply the quotient intertwining property
    exact gnsIntertwiner_intertwines_quotient φ π ξ hξ_state a y

end State
