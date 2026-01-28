/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Representation.Constrained
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.State.MPositiveState
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! # Vector States from Constrained Representations

Given a constrained *-representation π and a unit vector ξ, the vector state
φ_ξ(a) = Re⟨ξ, π(a)ξ⟩ is an M-positive state.

## Main definitions

* `vectorStateFun` - The underlying functional a ↦ Re⟨ξ, π(a)ξ⟩

## Main results

* `vectorState` - Vector states from constrained reps are M-positive
-/

open scoped ComplexOrder InnerProductSpace

namespace ArchimedeanClosure

variable {n : ℕ} (π : ConstrainedStarRep n) (ξ : π.H)

/-- The vector state functional: a ↦ Re⟨ξ, π(a)ξ⟩. -/
noncomputable def vectorStateFun : FreeStarAlgebra n → ℝ :=
  fun a => (⟪ξ, π a ξ⟫_ℂ).re

/-- Vector state is additive. -/
theorem vectorStateFun_add (a b : FreeStarAlgebra n) :
    vectorStateFun π ξ (a + b) = vectorStateFun π ξ a + vectorStateFun π ξ b := by
  unfold vectorStateFun ConstrainedStarRep.apply
  simp only [map_add, ContinuousLinearMap.add_apply, inner_add_right, Complex.add_re]

/-- Vector state respects ℝ-scaling. -/
theorem vectorStateFun_smul (c : ℝ) (a : FreeStarAlgebra n) :
    vectorStateFun π ξ (c • a) = c * vectorStateFun π ξ a := by
  unfold vectorStateFun ConstrainedStarRep.apply
  rw [map_smul, ← Complex.coe_smul]
  -- (↑c • π.toStarAlgHom a) ξ = ↑c • (π.toStarAlgHom a ξ) by definition of CLM smul
  change (⟪ξ, (c : ℂ) • (π.toStarAlgHom a ξ)⟫_ℂ).re = c * (⟪ξ, (π.toStarAlgHom a) ξ⟫_ℂ).re
  have h : (⟪ξ, (c : ℂ) • (π.toStarAlgHom a ξ)⟫_ℂ : ℂ) = c • ⟪ξ, (π.toStarAlgHom a ξ)⟫_ℂ :=
    inner_smul_real_right ξ _ c
  rw [h, Complex.real_smul]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- Vector state is ℝ-linear. -/
noncomputable def vectorStateLinear : FreeStarAlgebra n →ₗ[ℝ] ℝ where
  toFun := vectorStateFun π ξ
  map_add' := vectorStateFun_add π ξ
  map_smul' := vectorStateFun_smul π ξ

/-- Vector state is symmetric: φ(star a) = φ(a). -/
theorem vectorStateFun_star (a : FreeStarAlgebra n) :
    vectorStateFun π ξ (star a) = vectorStateFun π ξ a := by
  unfold vectorStateFun ConstrainedStarRep.apply
  have h1 : π.toStarAlgHom (star a) = star (π.toStarAlgHom a) := π.toStarAlgHom.map_star' a
  rw [h1, ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  -- Goal: (⟪(π.toStarAlgHom a) ξ, ξ⟫_ℂ).re = (⟪ξ, (π.toStarAlgHom a) ξ⟫_ℂ).re
  have h2 : (⟪(π.toStarAlgHom a) ξ, ξ⟫_ℂ : ℂ) =
            starRingEnd ℂ ⟪ξ, (π.toStarAlgHom a) ξ⟫_ℂ := (inner_conj_symm _ _).symm
  rw [h2]
  simp only [Complex.conj_re]

section UnitVector

variable (hξ : ‖ξ‖ = 1)

/-- Vector state maps 1 to 1 for unit vectors. -/
theorem vectorStateFun_one (hξ : ‖ξ‖ = 1) : vectorStateFun π ξ 1 = 1 := by
  unfold vectorStateFun ConstrainedStarRep.apply
  simp only [map_one, ContinuousLinearMap.one_apply]
  rw [inner_self_eq_norm_sq_to_K, hξ]
  simp

/-- Vector state is nonnegative on star a * a. -/
theorem vectorStateFun_star_mul_self_nonneg (a : FreeStarAlgebra n) :
    0 ≤ vectorStateFun π ξ (star a * a) := by
  unfold vectorStateFun ConstrainedStarRep.apply
  have h1 : π.toStarAlgHom (star a) = star (π.toStarAlgHom a) := π.toStarAlgHom.map_star' a
  simp only [map_mul, h1]
  rw [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.adjoint_inner_right]
  -- Goal: 0 ≤ (⟪v, v⟫_ℂ).re
  have h : 0 ≤ RCLike.re ⟪(π.toStarAlgHom a) ξ, (π.toStarAlgHom a) ξ⟫_ℂ := inner_self_nonneg
  simp only [RCLike.re_eq_complex_re] at h
  exact h

/-- Vector state is nonnegative on star b * gⱼ * b. -/
theorem vectorStateFun_star_generator_mul_nonneg (j : Fin n) (b : FreeStarAlgebra n) :
    0 ≤ vectorStateFun π ξ (star b * FreeStarAlgebra.generator j * b) := by
  unfold vectorStateFun ConstrainedStarRep.apply
  have h1 : π.toStarAlgHom (star b) = star (π.toStarAlgHom b) := π.toStarAlgHom.map_star' b
  simp only [map_mul, h1, mul_assoc]
  rw [ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply]
  rw [ContinuousLinearMap.adjoint_inner_right]
  -- π(gⱼ) is positive, so ⟨v, π(gⱼ)v⟩ has nonnegative real part
  have hp := (π.apply_generator_isPositive j).inner_nonneg_right ((π.toStarAlgHom b) ξ)
  exact (Complex.nonneg_iff.mp hp).1

/-- Vector state is nonnegative on QuadraticModule generators. -/
theorem vectorStateFun_generators_nonneg {m : FreeStarAlgebra n}
    (hm : m ∈ FreeStarAlgebra.QuadraticModuleGenerators n) :
    0 ≤ vectorStateFun π ξ m := by
  rcases hm with ⟨a, rfl⟩ | ⟨j, b, rfl⟩
  · exact vectorStateFun_star_mul_self_nonneg π ξ a
  · exact vectorStateFun_star_generator_mul_nonneg π ξ j b

/-- Vector state is nonnegative on all of QuadraticModule. -/
theorem vectorStateFun_m_nonneg {m : FreeStarAlgebra n}
    (hm : m ∈ FreeStarAlgebra.QuadraticModule n) :
    0 ≤ vectorStateFun π ξ m := by
  induction hm with
  | generator_mem m hm => exact vectorStateFun_generators_nonneg π ξ hm
  | add_mem m₁ m₂ _ _ ih₁ ih₂ =>
    rw [vectorStateFun_add]
    exact add_nonneg ih₁ ih₂
  | smul_mem c m hc _ ih =>
    rw [vectorStateFun_smul]
    exact mul_nonneg hc ih

/-- The vector state as an MPositiveState. -/
noncomputable def vectorState : FreeStarAlgebra.MPositiveState n where
  toFun := vectorStateLinear π ξ
  map_star := vectorStateFun_star π ξ
  map_one := vectorStateFun_one π ξ hξ
  map_m_nonneg := fun _ hm => vectorStateFun_m_nonneg π ξ hm

/-- Main theorem: vector states from constrained representations are M-positive. -/
theorem vectorState_mpositive :
    ∃ φ : FreeStarAlgebra.MPositiveState n, φ = vectorState π ξ hξ :=
  ⟨vectorState π ξ hξ, rfl⟩

end UnitVector

end ArchimedeanClosure
