/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Representation.Star
import Mathlib.Analysis.Normed.Operator.LinearIsometry

/-!
# GNS Uniqueness Theorem

The GNS representation is unique up to unitary equivalence.

## Main results

* `gnsIntertwinerQuotientFun` - The candidate intertwiner U₀([a]) = π(a)ξ
* `gnsIntertwinerQuotient_isometry` - ‖U₀(x)‖ = ‖x‖
* `gnsIntertwinerQuotientLinearIsometry` - U₀ as a LinearIsometry
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)

/-! ### The intertwiner construction -/

/-- Given a *-representation π and vector ξ satisfying the state condition,
    the map a ↦ π(a)ξ descends to a well-defined function on the quotient.

    Well-definedness: if a - b ∈ N_φ, then φ((a-b)*(a-b)) = 0.
    Since ⟨ξ, π(c)ξ⟩ = φ(c) for all c, we have
    ‖π(a-b)ξ‖² = ⟨ξ, π((a-b)*(a-b))ξ⟩ = φ((a-b)*(a-b)) = 0. -/
noncomputable def gnsIntertwinerQuotientFun
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) : φ.gnsQuotient → H := fun x =>
  Quotient.liftOn x (fun a => π a ξ) (by
    intro a b hab
    -- hab says a ≈ b, meaning a - b ∈ gnsNullIdeal, so φ((a-b)*(a-b)) = 0
    have hab' : a - b ∈ φ.gnsNullIdeal := (Submodule.quotientRel_def φ.gnsNullIdeal).mp hab
    have h_null : φ (star (a - b) * (a - b)) = 0 := hab'
    -- Goal: π(a)ξ = π(b)ξ, equivalently π(a-b)ξ = 0
    suffices h : π (a - b) ξ = 0 by
      have hsub : π a ξ - π b ξ = π (a - b) ξ := by
        rw [← ContinuousLinearMap.sub_apply, ← _root_.map_sub]
      rw [← sub_eq_zero, hsub, h]
    -- Show π(a-b)ξ = 0 via inner_self_eq_zero
    rw [← @inner_self_eq_zero ℂ]
    -- ⟨π(a-b)ξ, π(a-b)ξ⟩ = ⟨ξ, π(a-b)† (π(a-b) ξ)⟩ by adjoint property
    -- Using adjoint_inner_right: ⟨x, A† y⟩ = ⟨A x, y⟩
    have h_adj : @inner ℂ H _ (π (a - b) ξ) (π (a - b) ξ) =
        @inner ℂ H _ ξ ((π (a - b)).adjoint (π (a - b) ξ)) := by
      rw [ContinuousLinearMap.adjoint_inner_right]
    -- π(a-b)† = π((a-b)*)
    have h_star : (π (a - b)).adjoint = π (star (a - b)) := by
      have := π.map_star' (a - b)
      simp only [ContinuousLinearMap.star_eq_adjoint] at this
      exact this.symm
    -- π((a-b)*) (π(a-b) ξ) = π((a-b)* * (a-b)) ξ
    have h_mul : π (star (a - b)) (π (a - b) ξ) = π (star (a - b) * (a - b)) ξ := by
      conv_lhs => rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
                      ← _root_.map_mul]
    rw [h_adj, h_star, h_mul, hξ_state, h_null])

/-- The intertwiner is isometric: ‖U₀([a])‖ = ‖[a]‖.

    Proof: ‖π(a)ξ‖² = ⟨π(a)ξ, π(a)ξ⟩ = ⟨ξ, π(a*a)ξ⟩ = φ(a*a) = ‖[a]‖² -/
theorem gnsIntertwinerQuotient_isometry
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) (x : φ.gnsQuotient) :
    ‖gnsIntertwinerQuotientFun φ π ξ hξ_state x‖ = ‖x‖ := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal x
  -- By definition, gnsIntertwinerQuotientFun φ π ξ hξ_state [a] = π(a)ξ
  change ‖π a ξ‖ = ‖Submodule.Quotient.mk (p := φ.gnsNullIdeal) a‖
  -- ‖π(a)ξ‖² = φ(a*a) = ‖[a]‖²
  rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
  -- LHS: ‖π(a)ξ‖²
  have h_lhs : ‖π a ξ‖^2 = RCLike.re (@inner ℂ H _ ξ (π (star a * a) ξ)) := by
    have h1 : ‖π a ξ‖^2 = RCLike.re (@inner ℂ H _ (π a ξ) (π a ξ)) := by
      rw [← @inner_self_eq_norm_sq ℂ H]
    rw [h1]
    have h_adj : @inner ℂ H _ (π a ξ) (π a ξ) = @inner ℂ H _ ξ ((π a).adjoint (π a ξ)) := by
      rw [ContinuousLinearMap.adjoint_inner_right]
    have h_star : (π a).adjoint = π (star a) := by
      have := π.map_star' a
      simp only [ContinuousLinearMap.star_eq_adjoint] at this
      exact this.symm
    rw [h_adj, h_star]
    have h_mul : π (star a) (π a ξ) = π (star a * a) ξ := by
      conv_lhs => rw [← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.mul_def,
                      ← _root_.map_mul]
    rw [h_mul]
  rw [h_lhs, hξ_state]
  -- RHS: ‖[a]‖² in the GNS quotient
  rw [@InnerProductSpace.Core.norm_eq_sqrt_re_inner ℂ _ _ _ _ φ.gnsPreInnerProductCore]
  rw [Real.sq_sqrt (φ.gnsPreInnerProductCore.re_inner_nonneg _)]
  simp only [inner_eq_gnsInner_swap, gnsInner_mk]

/-- The intertwiner sends the cyclic vector to ξ: U₀([1]) = π(1)ξ = ξ. -/
theorem gnsIntertwinerQuotient_cyclic
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    gnsIntertwinerQuotientFun φ π ξ hξ_state φ.gnsCyclicVectorQuotient = ξ := by
  -- By definition, gnsCyclicVectorQuotient = [1], and U₀([1]) = π(1)ξ = ξ
  change π 1 ξ = ξ
  rw [_root_.map_one]
  rfl

/-! ### Linearity of the intertwiner -/

/-- U₀ preserves addition: U₀(x + y) = U₀(x) + U₀(y).
    Proof: [a] + [b] = [a + b], so U₀([a] + [b]) = π(a + b)ξ = π(a)ξ + π(b)ξ. -/
theorem gnsIntertwinerQuotient_add
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (x y : φ.gnsQuotient) :
    gnsIntertwinerQuotientFun φ π ξ hξ_state (x + y) =
    gnsIntertwinerQuotientFun φ π ξ hξ_state x +
    gnsIntertwinerQuotientFun φ π ξ hξ_state y := by
  -- Use quotient induction on x and y
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal y
  -- [a] + [b] = [a + b] by Submodule.Quotient.mk_add
  rw [← Submodule.Quotient.mk_add]
  -- U₀([a + b]) = π(a + b)ξ, U₀([a]) = π(a)ξ, U₀([b]) = π(b)ξ (by definition)
  -- π(a + b)ξ = π(a)ξ + π(b)ξ by additivity of π
  change π (a + b) ξ = π a ξ + π b ξ
  rw [_root_.map_add, ContinuousLinearMap.add_apply]

/-- U₀ preserves scalar multiplication: U₀(c • x) = c • U₀(x).
    Proof: c • [a] = [c • a], so U₀(c • [a]) = π(c • a)ξ = c • π(a)ξ.
    Uses that π : A →⋆ₐ[ℂ] (H →L[ℂ] H) is a ℂ-algebra hom. -/
theorem gnsIntertwinerQuotient_smul
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (c : ℂ) (x : φ.gnsQuotient) :
    gnsIntertwinerQuotientFun φ π ξ hξ_state (c • x) =
    c • gnsIntertwinerQuotientFun φ π ξ hξ_state x := by
  -- Use quotient induction on x
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal x
  -- c • [a] = [c • a] by Submodule.Quotient.mk_smul
  rw [← Submodule.Quotient.mk_smul]
  -- U₀([c • a]) = π(c • a)ξ, and π(c • a) = c • π(a) since π is a ℂ-algebra hom
  change π (c • a) ξ = c • π a ξ
  -- c • a = (algebraMap ℂ A c) * a in any ℂ-algebra
  rw [Algebra.smul_def, _root_.map_mul, ContinuousLinearMap.mul_apply]
  -- π(algebraMap ℂ A c) = algebraMap ℂ (H →L[ℂ] H) c = c • 1
  rw [AlgHomClass.commutes]
  -- (c • 1) applied to π(a)ξ gives c • π(a)ξ
  simp only [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply]

/-- U₀ maps zero to zero: U₀(0) = 0.
    Proof: 0 = [0] in the quotient, so U₀(0) = π(0)ξ = 0. -/
theorem gnsIntertwinerQuotient_zero
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    gnsIntertwinerQuotientFun φ π ξ hξ_state 0 = 0 := by
  -- 0 in the quotient is mk 0
  change gnsIntertwinerQuotientFun φ π ξ hξ_state (Submodule.Quotient.mk 0) = 0
  -- U₀([0]) = π(0)ξ = 0
  change π 0 ξ = 0
  rw [_root_.map_zero, ContinuousLinearMap.zero_apply]

/-! ### LinearMap structure -/

/-- U₀ as a linear map gnsQuotient →ₗ[ℂ] H.
    Combines the function with its linearity properties into a LinearMap structure. -/
noncomputable def gnsIntertwinerQuotientLinearMap
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    φ.gnsQuotient →ₗ[ℂ] H where
  toFun := gnsIntertwinerQuotientFun φ π ξ hξ_state
  map_add' := gnsIntertwinerQuotient_add φ π ξ hξ_state
  map_smul' := gnsIntertwinerQuotient_smul φ π ξ hξ_state

/-- The LinearMap agrees with the underlying function. -/
@[simp]
theorem gnsIntertwinerQuotientLinearMap_apply
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a)
    (x : φ.gnsQuotient) :
    gnsIntertwinerQuotientLinearMap φ π ξ hξ_state x =
    gnsIntertwinerQuotientFun φ π ξ hξ_state x := rfl

/-! ### LinearIsometry structure -/

/-- U₀ as a linear isometry gnsQuotient →ₗᵢ[ℂ] H.
    Combines the LinearMap with the isometry property. -/
noncomputable def gnsIntertwinerQuotientLinearIsometry
    (hξ_state : ∀ a : A, @inner ℂ H _ ξ (π a ξ) = φ a) :
    φ.gnsQuotient →ₗᵢ[ℂ] H where
  toLinearMap := gnsIntertwinerQuotientLinearMap φ π ξ hξ_state
  norm_map' := gnsIntertwinerQuotient_isometry φ π ξ hξ_state

end State
