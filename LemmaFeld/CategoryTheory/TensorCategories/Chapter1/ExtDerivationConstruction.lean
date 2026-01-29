/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel

/-!
# Extension to Derivation Construction

This file constructs the derivation from a module extension, and proves the
k-linear round-trip E → D → E gives an equivalent extension.

## Main Definitions

* `extensionDerivationAux` - The function a • s(y) - s(a • y)
* `extensionDerivation` - The derivation A → Hom_k(Y, X) from an extension
* `extensionSemidirectEquiv` - The k-linear equivalence E ≃ X × Y

## Book Reference

Etingof et al. "Tensor Categories" §1.4, Exercise 1.4.3(ii):
Given extension 0 → X → E → Y → 0 with section s, define D(a)(y) = a · s(y) - s(a · y).
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
variable {X E Y : Type*} [AddCommGroup X] [AddCommGroup E] [AddCommGroup Y]
variable [Module k X] [Module k E] [Module k Y]
variable [Module A X] [Module A E] [Module A Y]
variable [IsScalarTower k A X] [IsScalarTower k A E] [IsScalarTower k A Y]
variable [SMulCommClass A k E] [SMulCommClass A k Y]

/-! ## The Extension-to-Derivation Construction -/

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
    simp only [extensionDerivationAux, Submodule.coe_add, map_add, smul_add]
    abel
  map_smul' r y := by
    apply Subtype.ext
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

/-! ## Round-Trip: Extension → Derivation → Extension ~ Original

The k-linear equivalence E ≃ X × Y showing E→D→E gives an equivalent extension.
-/

section ExtensionRoundTrip

/-- For e ∈ E, the difference e - s(π(e)) lies in ker π. -/
lemma diff_mem_ker (π : E →ₗ[A] Y) (s : Y →ₗ[k] E) (hs : ∀ y, π (s y) = y) (e : E) :
    e - s (π e) ∈ LinearMap.ker π := by
  simp only [LinearMap.mem_ker, map_sub, hs, sub_self]

/-- The k-linear map E → X × Y: e ↦ (equiv⁻¹(e - s(π(e))), π(e)). -/
def extensionToSemidirect (π : E →ₗ[A] Y) (s : Y →ₗ[k] E)
    (hs : ∀ y, π (s y) = y) (equiv : X ≃ₗ[k] LinearMap.ker π) : E →ₗ[k] X × Y where
  toFun e := (equiv.symm ⟨e - s (π e), diff_mem_ker π s hs e⟩, π e)
  map_add' e₁ e₂ := by
    have heq_s : s (π (e₁ + e₂)) = s (π e₁) + s (π e₂) := by simp only [map_add]
    ext
    · simp only [Prod.fst_add, map_add]
      rw [← map_add equiv.symm]
      congr 1; ext
      simp only [Submodule.coe_add, Submodule.coe_mk, heq_s]; abel
    · simp only [Prod.snd_add, map_add]
  map_smul' r e := by
    have heq_s : s (π (r • e)) = r • s (π e) := by
      simp only [LinearMap.map_smul_of_tower, LinearMap.map_smul]
    ext
    · simp only [Prod.smul_fst, RingHom.id_apply]
      rw [← LinearEquiv.map_smul]
      congr 1; ext
      simp only [Submodule.coe_smul_of_tower, Submodule.coe_mk, heq_s, smul_sub]
    · simp only [Prod.smul_snd, RingHom.id_apply, LinearMap.map_smul_of_tower]

/-- The k-linear inverse map X × Y → E via (x, y) ↦ equiv(x) + s(y). -/
def semidirectToExtension (π : E →ₗ[A] Y) (s : Y →ₗ[k] E)
    (equiv : X ≃ₗ[k] LinearMap.ker π) : X × Y →ₗ[k] E where
  toFun p := (equiv p.1).val + s p.2
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add, LinearMap.map_add]; abel
  map_smul' r p := by
    simp only [Prod.smul_mk, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, map_smul,
      Submodule.coe_smul_of_tower, LinearMap.map_smul, smul_add]

/-- extensionToSemidirect ∘ semidirectToExtension = id. -/
theorem extensionToSemidirect_semidirectToExtension (π : E →ₗ[A] Y) (s : Y →ₗ[k] E)
    (hs : ∀ y, π (s y) = y) (equiv : X ≃ₗ[k] LinearMap.ker π) (p : X × Y) :
    extensionToSemidirect π s hs equiv (semidirectToExtension π s equiv p) = p := by
  simp only [extensionToSemidirect, semidirectToExtension, LinearMap.coe_mk, AddHom.coe_mk]
  ext
  · have hker : π (equiv p.1) = 0 := (equiv p.1).property
    simp only [map_add, hker, zero_add, hs, add_sub_cancel_right]
    exact LinearEquiv.symm_apply_apply equiv p.1
  · have hker : π (equiv p.1) = 0 := (equiv p.1).property
    simp only [map_add, hker, zero_add, hs]

/-- semidirectToExtension ∘ extensionToSemidirect = id. -/
theorem semidirectToExtension_extensionToSemidirect (π : E →ₗ[A] Y) (s : Y →ₗ[k] E)
    (hs : ∀ y, π (s y) = y) (equiv : X ≃ₗ[k] LinearMap.ker π) (e : E) :
    semidirectToExtension π s equiv (extensionToSemidirect π s hs equiv e) = e := by
  simp only [extensionToSemidirect, semidirectToExtension, LinearMap.coe_mk, AddHom.coe_mk,
    LinearEquiv.apply_symm_apply, Submodule.coe_mk, sub_add_cancel]

/-- The k-linear equivalence E ≃ X × Y for an extension with section. -/
def extensionSemidirectEquiv (π : E →ₗ[A] Y) (s : Y →ₗ[k] E)
    (hs : ∀ y, π (s y) = y) (equiv : X ≃ₗ[k] LinearMap.ker π) : E ≃ₗ[k] X × Y where
  toLinearMap := extensionToSemidirect π s hs equiv
  invFun := semidirectToExtension π s equiv
  left_inv := semidirectToExtension_extensionToSemidirect π s hs equiv
  right_inv := extensionToSemidirect_semidirectToExtension π s hs equiv

/-- The extension round-trip gives an equivalent extension (k-linear). -/
theorem extension_roundtrip (π : E →ₗ[A] Y) (s : Y →ₗ[k] E)
    (hs : ∀ y, π (s y) = y) (equiv : X ≃ₗ[k] LinearMap.ker π) :
    ∃ (φ : E ≃ₗ[k] X × Y),
      (∀ e, (φ e).2 = π e) ∧
      (∀ e, e ∈ LinearMap.ker π → (φ e).2 = 0) :=
  ⟨extensionSemidirectEquiv π s hs equiv,
   fun e => rfl,
   fun e he => by simp only [extensionSemidirectEquiv, extensionToSemidirect,
     LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mem_ker.mp he]⟩

end ExtensionRoundTrip

end LemmaFeld.TensorCategories.Chapter1
