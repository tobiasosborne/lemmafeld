/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Complexify

/-! # Complexification: Linear Maps and Inner Product

This file provides the extension of real linear maps to complexification
and the complex inner product on the complexified space.

## Main definitions

* `Complexification.mapComplex` - Extend a real linear map to the complexification
* `Complexification.instInnerComplex` - Complex inner product on H_ℂ

## Mathematical Background

For T : H →ₗ[ℝ] H, define T_ℂ : H_ℂ → H_ℂ by T_ℂ(x, y) = (T x, T y).
This is ℂ-linear because T is ℝ-linear.

The inner product on H_ℂ = H × H is:
⟪(x₁,y₁), (x₂,y₂)⟫_ℂ = ⟪x₁,x₂⟫ + ⟪y₁,y₂⟫ + i(⟪x₁,y₂⟫ - ⟪y₁,x₂⟫)
-/

namespace ArchimedeanClosure

open scoped InnerProductSpace

namespace Complexification

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

/-! ### Extending Real Linear Maps to Complexification -/

/-- Extend a real linear map T : H → H to the complexification.

For T : H →ₗ[ℝ] H, define T_ℂ : H_ℂ → H_ℂ by T_ℂ(x, y) = (T x, T y).
This is ℂ-linear because T is ℝ-linear. -/
def mapComplex (T : H →ₗ[ℝ] H) : Complexification H →ₗ[ℂ] Complexification H where
  toFun p := (T p.1, T p.2)
  map_add' p q := by
    change (T (p.1 + q.1), T (p.2 + q.2)) = (T p.1 + T q.1, T p.2 + T q.2)
    simp only [map_add]
  map_smul' c p := by
    ext
    · simp only [smul_fst, T.map_sub, T.map_smul, RingHom.id_apply]
    · simp only [smul_snd, T.map_add, T.map_smul, RingHom.id_apply]

@[simp]
theorem mapComplex_fst (T : H →ₗ[ℝ] H) (p : Complexification H) :
    (mapComplex T p).1 = T p.1 := rfl

@[simp]
theorem mapComplex_snd (T : H →ₗ[ℝ] H) (p : Complexification H) :
    (mapComplex T p).2 = T p.2 := rfl

/-- Extending preserves the embedding: T_ℂ(embed x) = embed(T x). -/
theorem mapComplex_embed (T : H →ₗ[ℝ] H) (x : H) :
    mapComplex T (embed x) = embed (T x) := by
  ext <;> simp

/-- The identity map complexifies to the identity. -/
@[simp]
theorem mapComplex_id : mapComplex (LinearMap.id (R := ℝ) (M := H)) = LinearMap.id := by
  ext p
  · simp only [mapComplex_fst, LinearMap.id_apply]
  · simp only [mapComplex_snd, LinearMap.id_apply]

/-- Composition of maps complexifies to composition: (T₁ ∘ T₂)_ℂ = T₁_ℂ ∘ T₂_ℂ. -/
theorem mapComplex_comp (T₁ T₂ : H →ₗ[ℝ] H) :
    mapComplex (T₁.comp T₂) = (mapComplex T₁).comp (mapComplex T₂) := by
  ext p
  · simp only [mapComplex_fst, LinearMap.comp_apply]
  · simp only [mapComplex_snd, LinearMap.comp_apply]

/-- Addition of maps complexifies to addition: (T₁ + T₂)_ℂ = T₁_ℂ + T₂_ℂ. -/
theorem mapComplex_add (T₁ T₂ : H →ₗ[ℝ] H) :
    mapComplex (T₁ + T₂) = mapComplex T₁ + mapComplex T₂ := by
  ext p <;> rfl

/-- Scalar multiplication complexifies: (r • T)_ℂ = (r : ℂ) • T_ℂ. -/
theorem mapComplex_smul (r : ℝ) (T : H →ₗ[ℝ] H) :
    mapComplex (r • T) = (r : ℂ) • mapComplex T := by
  ext p
  · simp only [mapComplex_fst, LinearMap.smul_apply, smul_fst,
               Complex.ofReal_re, Complex.ofReal_im, zero_smul, sub_zero]
  · simp only [mapComplex_snd, LinearMap.smul_apply, smul_snd,
               Complex.ofReal_re, Complex.ofReal_im, zero_smul, add_zero]

/-! ### Complex Inner Product -/

variable [Inner ℝ H]

/-- Complex inner product on the complexification.

For p = (x₁, y₁) and q = (x₂, y₂):
⟪p, q⟫_ℂ = ⟪x₁,x₂⟫ + ⟪y₁,y₂⟫ + i(⟪x₁,y₂⟫ - ⟪y₁,x₂⟫) -/
instance instInnerComplex : Inner ℂ (Complexification H) where
  inner p q := {
    re := @inner ℝ H _ p.1 q.1 + @inner ℝ H _ p.2 q.2
    im := @inner ℝ H _ p.1 q.2 - @inner ℝ H _ p.2 q.1
  }

omit [AddCommGroup H] [Module ℝ H] in
theorem inner_def (p q : Complexification H) :
    ⟪p, q⟫_ℂ = { re := @inner ℝ H _ p.1 q.1 + @inner ℝ H _ p.2 q.2,
                 im := @inner ℝ H _ p.1 q.2 - @inner ℝ H _ p.2 q.1 } := rfl

omit [AddCommGroup H] [Module ℝ H] in
@[simp]
theorem inner_re (p q : Complexification H) :
    (⟪p, q⟫_ℂ).re = @inner ℝ H _ p.1 q.1 + @inner ℝ H _ p.2 q.2 := rfl

omit [AddCommGroup H] [Module ℝ H] in
@[simp]
theorem inner_im (p q : Complexification H) :
    (⟪p, q⟫_ℂ).im = @inner ℝ H _ p.1 q.2 - @inner ℝ H _ p.2 q.1 := rfl

end Complexification

end ArchimedeanClosure
