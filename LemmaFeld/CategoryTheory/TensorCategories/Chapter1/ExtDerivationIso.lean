/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Tactic.Abel

/-!
# Extension to Derivation Map

This file constructs the map from module extensions to derivations,
which is one direction of the Ext¹ ≅ H¹ isomorphism from Exercise 1.4.3(ii).

## Main Definitions

* `extensionDerivationAux` - The function A → (Y → E) given by a • s(y) - s(a • y)
* `extensionDerivation` - The derivation A → Hom_k(Y, X) from an extension

## Book Reference

Etingof et al. "Tensor Categories" §1.4, Exercise 1.4.3(ii):
Given an extension 0 → X → E → Y → 0 of A-modules, choose a k-linear splitting s : Y → E.
Define D(a)(y) = a · s(y) - s(a · y). This is a derivation.

-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
variable {X E Y : Type*} [AddCommGroup X] [AddCommGroup E] [AddCommGroup Y]
variable [Module k X] [Module k E] [Module k Y]
variable [Module A X] [Module A E] [Module A Y]
variable [IsScalarTower k A X] [IsScalarTower k A E] [IsScalarTower k A Y]
variable [SMulCommClass A k E] [SMulCommClass A k Y]

/-! ## The Extension-to-Derivation Construction

Given:
- A short exact sequence 0 → X →[i] E →[π] Y → 0 of A-modules
- A k-linear section s : Y → E (with π ∘ s = id)

We construct D : A → Hom_k(Y, X) by D(a)(y) = a • s(y) - s(a • y).
-/

section ExtensionToDerivation

variable (i : X →ₗ[A] E) (π : E →ₗ[A] Y) (s : Y →ₗ[k] E)

/-- The auxiliary function: for a ∈ A and y ∈ Y, compute a • s(y) - s(a • y) ∈ E. -/
def extensionDerivationAux (a : A) (y : Y) : E :=
  a • s y - s (a • y)

/-- The auxiliary function lands in ker π when s is a section of π. -/
lemma extensionDerivationAux_mem_ker (hs : ∀ y, π (s y) = y) (a : A) (y : Y) :
    extensionDerivationAux s a y ∈ LinearMap.ker π := by
  simp only [LinearMap.mem_ker, extensionDerivationAux]
  rw [map_sub, map_smul, hs, hs, sub_self]

/-- The auxiliary function as a k-linear map Y → ker π (for fixed a). -/
def extensionDerivationToKer (hs : ∀ y, π (s y) = y) (a : A) : Y →ₗ[k] LinearMap.ker π where
  toFun y := ⟨extensionDerivationAux s a y, extensionDerivationAux_mem_ker π s hs a y⟩
  map_add' y₁ y₂ := by
    apply Subtype.ext
    -- Goal: a • s(y₁ + y₂) - s(a • (y₁ + y₂)) = (a • s y₁ - s (a • y₁)) + (a • s y₂ - s (a • y₂))
    simp only [extensionDerivationAux, Submodule.coe_add, map_add, smul_add]
    abel
  map_smul' r y := by
    apply Subtype.ext
    -- Goal: a • s(r • y) - s(a • (r • y)) = r • (a • s y - s (a • y))
    simp only [extensionDerivationAux, RingHom.id_apply, Submodule.coe_smul_of_tower,
      LinearMap.map_smul, smul_sub, smul_comm a r (s y), smul_comm a r y]

/-- Given an equivalence X ≃ ker π, lift the derivation to land in X. -/
def extensionDerivation (hs : ∀ y, π (s y) = y)
    (equiv : X ≃ₗ[k] LinearMap.ker π) : A → (Y →ₗ[k] X) :=
  fun a => equiv.symm.toLinearMap.comp (extensionDerivationToKer π s hs a)

/-- The extension derivation at 1 is zero. -/
lemma extensionDerivation_one (hs : ∀ y, π (s y) = y)
    (equiv : X ≃ₗ[k] LinearMap.ker π) : extensionDerivation π s hs equiv 1 = 0 := by
  ext y
  simp only [extensionDerivation, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.zero_apply]
  have h : (extensionDerivationToKer π s hs 1 y : E) = 0 := by
    simp only [extensionDerivationToKer, LinearMap.coe_mk, AddHom.coe_mk,
      extensionDerivationAux, one_smul, sub_self]
  rw [show extensionDerivationToKer π s hs 1 y = 0 from Subtype.ext h, map_zero]

/-- The extension derivation is additive in A. -/
lemma extensionDerivation_add (hs : ∀ y, π (s y) = y)
    (equiv : X ≃ₗ[k] LinearMap.ker π) (a b : A) :
    extensionDerivation π s hs equiv (a + b) =
    extensionDerivation π s hs equiv a + extensionDerivation π s hs equiv b := by
  ext y
  simp only [extensionDerivation, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
    LinearMap.add_apply]
  have h : extensionDerivationToKer π s hs (a + b) y =
      extensionDerivationToKer π s hs a y + extensionDerivationToKer π s hs b y := by
    apply Subtype.ext
    simp only [extensionDerivationToKer, LinearMap.coe_mk, AddHom.coe_mk,
      Submodule.coe_add, Submodule.coe_mk, extensionDerivationAux, add_smul, map_add]
    abel
  simp only [h, map_add]

end ExtensionToDerivation

end LemmaFeld.TensorCategories.Chapter1
