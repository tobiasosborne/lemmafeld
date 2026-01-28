/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Completion
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # Complexification of Real Hilbert Spaces

This file provides the complexification of a real inner product space.

## Mathematical Background

Given a real inner product space H_ℝ, the complexification H_ℂ is:
- As a set: H_ℝ × H_ℝ (pairs (x, y) representing x + iy)
- Complex scalar: (a + bi)·(x, y) = (ax - by, ay + bx)
- Inner product: ⟪(x₁,y₁), (x₂,y₂)⟫_ℂ = ⟪x₁,x₂⟫ + ⟪y₁,y₂⟫ + i(⟪x₁,y₂⟫ - ⟪y₁,x₂⟫)

The embedding H_ℝ → H_ℂ is x ↦ (x, 0), and ‖(x,0)‖_ℂ = ‖x‖_ℝ.

## Main definitions

* `Complexification` - The complexified type H × H
* `Complexification.instSMulComplex` - Complex scalar multiplication
* `Complexification.embed` - The embedding H_ℝ → H_ℂ

## References

Standard textbook construction. See e.g., Reed & Simon Vol I.
-/

namespace ArchimedeanClosure

open scoped InnerProductSpace

/-! ### The Complexification Type -/

/-- Complexification of a real inner product space.

Represented as pairs (x, y) ∈ H × H, interpreted as x + iy. -/
def Complexification (H : Type*) := H × H

namespace Complexification

variable {H : Type*} [AddCommGroup H] [Module ℝ H]

/-! ### Basic Instances -/

instance : AddCommGroup (Complexification H) :=
  inferInstanceAs (AddCommGroup (H × H))

omit [AddCommGroup H] [Module ℝ H] in
/-- Extensionality for Complexification. -/
@[ext]
theorem ext {p q : Complexification H} (h1 : p.1 = q.1) (h2 : p.2 = q.2) : p = q :=
  Prod.ext h1 h2

/-- Complex scalar multiplication on the complexification.

For c = a + bi ∈ ℂ and (x, y) ∈ H_ℂ:
c · (x, y) = (ax - by, ay + bx) -/
instance instSMulComplex : SMul ℂ (Complexification H) where
  smul c p := (c.re • p.1 - c.im • p.2, c.re • p.2 + c.im • p.1)

theorem smul_def (c : ℂ) (p : Complexification H) :
    c • p = (c.re • p.1 - c.im • p.2, c.re • p.2 + c.im • p.1) := rfl

@[simp]
theorem smul_fst (c : ℂ) (p : Complexification H) :
    (c • p).1 = c.re • p.1 - c.im • p.2 := rfl

@[simp]
theorem smul_snd (c : ℂ) (p : Complexification H) :
    (c • p).2 = c.re • p.2 + c.im • p.1 := rfl

/-- One acts as identity. -/
theorem one_smul' (p : Complexification H) : (1 : ℂ) • p = p := by
  ext <;> simp [smul_def]

/-- Zero annihilates. -/
theorem zero_smul' (p : Complexification H) : (0 : ℂ) • p = 0 := by
  ext <;> simp [smul_def]

/-- Scalar multiplication is associative: (c₁ * c₂) • p = c₁ • (c₂ • p). -/
theorem mul_smul' (c₁ c₂ : ℂ) (p : Complexification H) :
    (c₁ * c₂) • p = c₁ • (c₂ • p) := by
  ext
  · -- First component: (c₁*c₂).re•p.1 - (c₁*c₂).im•p.2 = c₁.re•(c₂•p).1 - c₁.im•(c₂•p).2
    simp only [smul_fst, smul_snd, Complex.mul_re, Complex.mul_im]
    module
  · -- Second component
    simp only [smul_fst, smul_snd, Complex.mul_re, Complex.mul_im]
    module

/-- Scalar addition distributes: (c₁ + c₂) • p = c₁ • p + c₂ • p. -/
theorem add_smul' (c₁ c₂ : ℂ) (p : Complexification H) :
    (c₁ + c₂) • p = c₁ • p + c₂ • p := by
  ext
  · simp only [smul_fst, Complex.add_re, Complex.add_im]
    change (c₁.re + c₂.re) • p.1 - (c₁.im + c₂.im) • p.2 =
           (c₁.re • p.1 - c₁.im • p.2) + (c₂.re • p.1 - c₂.im • p.2)
    module
  · simp only [smul_snd, Complex.add_re, Complex.add_im]
    change (c₁.re + c₂.re) • p.2 + (c₁.im + c₂.im) • p.1 =
           (c₁.re • p.2 + c₁.im • p.1) + (c₂.re • p.2 + c₂.im • p.1)
    module

/-- Scalar distributes over vector addition: c • (p + q) = c • p + c • q. -/
theorem smul_add' (c : ℂ) (p q : Complexification H) :
    c • (p + q) = c • p + c • q := by
  ext
  · simp only [smul_fst]
    change c.re • (p.1 + q.1) - c.im • (p.2 + q.2) =
           (c.re • p.1 - c.im • p.2) + (c.re • q.1 - c.im • q.2)
    module
  · simp only [smul_snd]
    change c.re • (p.2 + q.2) + c.im • (p.1 + q.1) =
           (c.re • p.2 + c.im • p.1) + (c.re • q.2 + c.im • q.1)
    module

/-- Scalar times zero is zero: c • 0 = 0. -/
theorem smul_zero' (c : ℂ) : c • (0 : Complexification H) = 0 := by
  ext <;> simp [smul_def]

/-! ### Module Instance -/

/-- The complexification is a complex module. -/
instance instModuleComplex : Module ℂ (Complexification H) where
  one_smul := one_smul'
  mul_smul := mul_smul'
  smul_zero := smul_zero'
  smul_add := smul_add'
  add_smul := add_smul'
  zero_smul := zero_smul'

/-! ### The Embedding -/

/-- Embed the real space into the complexification: x ↦ (x, 0). -/
def embed (x : H) : Complexification H := (x, 0)

omit [Module ℝ H] in
@[simp]
theorem embed_fst (x : H) : (embed x).1 = x := rfl

omit [Module ℝ H] in
@[simp]
theorem embed_snd (x : H) : (embed x).2 = 0 := rfl

omit [Module ℝ H] in
theorem embed_add (x y : H) : embed (x + y) = embed x + embed y := by
  change (x + y, (0 : H)) = (x, 0) + (y, 0)
  simp only [Prod.mk_add_mk, add_zero]

theorem embed_smul_real (r : ℝ) (x : H) : embed (r • x) = (r : ℂ) • embed x := by
  ext
  · simp only [embed_fst, smul_fst, embed_snd, Complex.ofReal_re, Complex.ofReal_im,
               smul_zero, sub_zero]
  · simp only [embed_snd, smul_snd, embed_fst, Complex.ofReal_re, Complex.ofReal_im,
               smul_zero, zero_add, zero_smul]

end Complexification

end ArchimedeanClosure
