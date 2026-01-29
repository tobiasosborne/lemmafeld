/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.InnerDerivations

/-!
# Bimodule Derivations

This file defines bimodule derivations, which satisfy the bimodule Leibniz rule
D(ab) = a • D(b) + D(a) • b, and proves that inner derivations are bimodule derivations.

## Main Definitions

* `IsBimoduleDerivation R A M D` — predicate for D satisfying bimodule Leibniz
* `BimoduleDerivations R A M` — submodule of bimodule derivations

## Main Results

* `BimoduleDerivation.map_one` — bimodule derivations send 1 to 0
* `InnerDerivations_le_BimoduleDerivations` — inner derivations are bimodule derivations

## Mathematical Background

For a bimodule M (with left A-action and right Aᵐᵒᵖ-action), a **bimodule derivation**
is a linear map D : A →ₗ[R] M satisfying the bimodule Leibniz rule:

  D(ab) = a • D(b) + D(a) • b

This differs from mathlib's `Derivation` which uses `D(ab) = a • D(b) + b • D(a)`
(symmetric form appropriate for commutative A with M = A).

## References

- Etingof et al. "Tensor Categories" (AMS 2015), §1.4, Exercise 1.4.3(ii)

-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

section BimoduleDerivations

variable (R A M : Type*) [CommRing R] [CommRing A] [AddCommGroup M]
variable [Algebra R A] [Module A M] [Module Aᵐᵒᵖ M] [Module R M]
variable [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]

/-- The bimodule Leibniz rule: D(ab) = a • D(b) + D(a) • b.
The right action `D(a) • b` is expressed as `MulOpposite.op b • D(a)`. -/
def IsBimoduleDerivation (D : A →ₗ[R] M) : Prop :=
  ∀ a b : A, D (a * b) = a • D b + MulOpposite.op b • D a

/-- The submodule of bimodule derivations in A →ₗ[R] M.
These are R-linear maps satisfying D(ab) = a • D(b) + D(a) • b. -/
def BimoduleDerivations : Submodule R (A →ₗ[R] M) where
  carrier := {D | IsBimoduleDerivation R A M D}
  zero_mem' := by
    intro a b
    simp only [LinearMap.zero_apply, smul_zero, add_zero]
  add_mem' := by
    intro D₁ D₂ hD₁ hD₂ a b
    simp only [LinearMap.add_apply, smul_add]
    rw [hD₁ a b, hD₂ a b]
    abel
  smul_mem' := by
    intro r D hD a b
    simp only [LinearMap.smul_apply]
    rw [hD a b]
    rw [smul_add, smul_comm r a, smul_comm r (MulOpposite.op b)]

/-- Membership characterization for BimoduleDerivations. -/
lemma mem_bimoduleDerivations_iff (D : A →ₗ[R] M) :
    D ∈ BimoduleDerivations R A M ↔ IsBimoduleDerivation R A M D := Iff.rfl

/-- A bimodule derivation satisfies D(1) = 0. -/
lemma BimoduleDerivation.map_one (D : A →ₗ[R] M) (hD : IsBimoduleDerivation R A M D) :
    D 1 = 0 := by
  have h := hD 1 1
  simp only [mul_one, MulOpposite.op_one, one_smul] at h
  -- h : D 1 = D 1 + D 1
  have : (0 : M) = D 1 := by
    calc (0 : M) = D 1 - D 1 := (sub_self (D 1)).symm
         _ = (D 1 + D 1) - D 1 := by rw [← h]
         _ = D 1 := add_sub_cancel_right (D 1) (D 1)
  exact this.symm

/-- Inner derivations are bimodule derivations, provided the left and right actions commute. -/
theorem InnerDerivations_le_BimoduleDerivations [SMulCommClass A Aᵐᵒᵖ M] :
    InnerDerivations R A M ≤ BimoduleDerivations R A M := by
  intro D hD
  rw [mem_innerDerivations_iff] at hD
  obtain ⟨f, rfl⟩ := hD
  rw [mem_bimoduleDerivations_iff]
  intro a b
  -- Goal: D_f(ab) = a • D_f(b) + (op b) • D_f(a)
  -- where D_f(x) = x • f - (op x) • f
  simp only [InnerDerivation.toLinearMap, InnerDerivation.toFun,
    LinearMap.coe_mk, AddHom.coe_mk]
  -- LHS: (ab) • f - op(ab) • f
  -- RHS: a • (b • f - op b • f) + op b • (a • f - op a • f)
  rw [MulOpposite.op_mul]
  -- LHS: (ab) • f - (op b * op a) • f
  -- RHS: a • b • f - a • op b • f + op b • a • f - op b • op a • f
  rw [mul_smul, mul_smul]
  -- LHS: a • (b • f) - op b • (op a • f)
  rw [smul_sub, smul_sub]
  -- RHS expanded, need to use commutativity of A and Aᵐᵒᵖ actions
  rw [smul_comm a (MulOpposite.op b) f]
  abel

end BimoduleDerivations

end LemmaFeld.TensorCategories.Chapter1
