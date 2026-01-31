/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.FiniteDual
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# Chapter 1, Section 1.12: Coalgebra Structure on the Finite Dual

This file establishes the coalgebra structure on the finite dual A°_fin,
following Etingof et al. "Tensor Categories" §1.12 Proposition 1.12.2.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.12

## Main Definitions

* `dualComulAux`: The "pre-comultiplication" Δ : A* → (A ⊗ A)* defined by Δ(f)(a ⊗ b) = f(ab)

## Proposition 1.12.2

Book: "The maps Δ := m* and ε := u*, where m : A ⊗ A → A and u : k → A are
the multiplication and unit of A, define a coalgebra structure on A*_fin."

The counit ε(f) = f(1) is defined in FiniteDual.lean as `dualCounit`.

The comultiplication Δ(f)(a ⊗ b) = f(ab) is the dual of multiplication.
For f ∈ A*_fin vanishing on ideal I, Δ(f) vanishes on I ⊗ A + A ⊗ I.
-/

namespace LemmaFeld.TensorCategories.Chapter1

open scoped TensorProduct

variable {k : Type*} {A : Type*} [Field k] [Ring A] [Algebra k A]

/-! ## Pre-Comultiplication on the Full Dual

We first define Δ : A* → (A ⊗ A)* by Δ(f)(a ⊗ b) = f(ab).
This is the dual of the multiplication map m : A ⊗ A → A.
-/

/-- Multiplication as a bilinear map A × A → A. -/
def mulBilin : A →ₗ[k] A →ₗ[k] A where
  toFun a := {
    toFun := fun b => a * b
    map_add' := fun _ _ => mul_add a _ _
    map_smul' := fun r b => by
      simp only [Algebra.smul_def, RingHom.id_apply]
      exact Algebra.left_comm a r b
  }
  map_add' := fun _ _ => by ext; simp [add_mul]
  map_smul' := fun r a => by
    ext b
    -- Goal: (r • a) * b = r • (a * b)
    simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, smul_mul_assoc,
      RingHom.id_apply]

/-- Multiplication as a linear map A ⊗ A → A. -/
noncomputable def mulLinear : A ⊗[k] A →ₗ[k] A :=
  TensorProduct.lift mulBilin

@[simp]
lemma mulLinear_tmul (a b : A) : mulLinear (a ⊗ₜ[k] b) = a * b := rfl

/-- The pre-comultiplication Δ : A* → (A ⊗ A)*.

For f ∈ A*, we define Δ(f) ∈ (A ⊗ A)* by Δ(f)(a ⊗ b) = f(ab).
This is the dual (transpose) of the multiplication map.

Book Proposition 1.12.2: Δ = m* where m : A ⊗ A → A is multiplication. -/
noncomputable def dualComulAux : Module.Dual k A →ₗ[k] Module.Dual k (A ⊗[k] A) :=
  mulLinear.dualMap

@[simp]
lemma dualComulAux_apply_tmul (f : Module.Dual k A) (a b : A) :
    dualComulAux f (a ⊗ₜ[k] b) = f (a * b) := rfl

/-! ## Vanishing on Ideal Tensor Products

If f vanishes on an ideal I, then Δ(f) vanishes on I ⊗ A + A ⊗ I.
This is key to showing Δ preserves the finite dual.
-/

/-- If f vanishes on a two-sided ideal I, then Δ(f) vanishes on any pure tensor
where the left factor is in I. -/
lemma dualComulAux_vanishes_left {f : Module.Dual k A} {I : TwoSidedIdeal A}
    (hf : ∀ x ∈ I, f x = 0) (a : A) (ha : a ∈ I) (b : A) :
    dualComulAux f (a ⊗ₜ[k] b) = 0 := by
  simp only [dualComulAux_apply_tmul]
  exact hf (a * b) (I.mul_mem_right a b ha)

/-- If f vanishes on a two-sided ideal I, then Δ(f) vanishes on any pure tensor
where the right factor is in I. -/
lemma dualComulAux_vanishes_right {f : Module.Dual k A} {I : TwoSidedIdeal A}
    (hf : ∀ x ∈ I, f x = 0) (a : A) (b : A) (hb : b ∈ I) :
    dualComulAux f (a ⊗ₜ[k] b) = 0 := by
  simp only [dualComulAux_apply_tmul]
  exact hf (a * b) (I.mul_mem_left a b hb)

end LemmaFeld.TensorCategories.Chapter1
