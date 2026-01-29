/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.SemidirectProduct
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.ExtDerivationConstruction

/-!
# A-Linear Round-Trip Compatibility

The key insight: when the equivalence `X ≃ ker π` is A-linear (not just k-linear),
the map `extensionToSemidirect` respects the semi-direct A-action.

This is the key piece for showing the extension round-trip gives an ExtensionEquiv.

## Main Theorems

* `extensionToSemidirect_A_linear_aux` - A-linearity of first component
* `extensionToSemidirect_respects_action` - Full A-action compatibility

## Book Reference

Etingof et al. "Tensor Categories" §1.4, Exercise 1.4.3(ii)
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

section ALinearRoundTrip

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
variable {X E Y : Type*} [AddCommGroup X] [AddCommGroup E] [AddCommGroup Y]
variable [Module k X] [Module k E] [Module k Y]
variable [Module A X] [Module A E] [Module A Y]
variable [IsScalarTower k A X] [IsScalarTower k A E] [IsScalarTower k A Y]
variable [SMulCommClass A k E] [SMulCommClass A k Y]

/-- When equiv is A-linear, the first component of extensionToSemidirect respects A-action.

The key equation:
  equiv⁻¹(a • e - s(π(a • e))) = a • equiv⁻¹(e - s(π(e))) + equiv⁻¹(a • s(π(e)) - s(a • π(e)))
-/
theorem extensionToSemidirect_A_linear_aux (π : E →ₗ[A] Y) (s : Y →ₗ[k] E)
    (hs : ∀ y, π (s y) = y) (equiv : X ≃ₗ[A] LinearMap.ker π) (a : A) (e : E) :
    equiv.symm ⟨a • e - s (π (a • e)), diff_mem_ker π s hs (a • e)⟩ =
    a • equiv.symm ⟨e - s (π e), diff_mem_ker π s hs e⟩ +
    equiv.symm ⟨a • s (π e) - s (a • π e), extensionDerivationAux_mem_ker π s hs a (π e)⟩ := by
  apply_fun equiv using equiv.injective
  rw [map_add, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
      LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]
  ext
  simp only [Submodule.coe_add, Submodule.coe_smul_of_tower, Submodule.coe_mk, smul_sub, map_smul]
  abel

/-- The extracted derivation as a k-linear map (using A-linear equiv). -/
def extractedDerivationLinear (π : E →ₗ[A] Y) (s : Y →ₗ[k] E)
    (hs : ∀ y, π (s y) = y) (equiv : X ≃ₗ[A] LinearMap.ker π) (a : A) : Y →ₗ[k] X where
  toFun y := equiv.symm ⟨a • s y - s (a • y), extensionDerivationAux_mem_ker π s hs a y⟩
  map_add' y₁ y₂ := by
    apply_fun equiv using equiv.injective
    simp only [map_add, LinearEquiv.apply_symm_apply]
    ext
    simp only [Submodule.coe_add, Submodule.coe_mk, smul_add, map_add]
    abel
  map_smul' r y := by
    simp only [RingHom.id_apply, map_smul, smul_comm a r (s y), smul_comm a r y]
    apply_fun equiv using equiv.injective
    simp only [LinearEquiv.apply_symm_apply]
    have h : equiv (r • equiv.symm ⟨a • s y - s (a • y),
        extensionDerivationAux_mem_ker π s hs a y⟩) =
        r • ⟨a • s y - s (a • y), extensionDerivationAux_mem_ker π s hs a y⟩ := by
      rw [← smul_one_smul A r (equiv.symm _), LinearEquiv.map_smul,
          LinearEquiv.apply_symm_apply, smul_one_smul]
    rw [h]
    ext
    simp only [Submodule.coe_smul_of_tower, Submodule.coe_mk, smul_sub]

/-- The full A-linear compatibility: extensionToSemidirect respects semi-direct action. -/
theorem extensionToSemidirect_respects_action (π : E →ₗ[A] Y) (s : Y →ₗ[k] E)
    (hs : ∀ y, π (s y) = y) (equiv : X ≃ₗ[A] LinearMap.ker π) (a : A) (e : E) :
    let φ := fun e' => (equiv.symm ⟨e' - s (π e'), diff_mem_ker π s hs e'⟩, π e')
    let D := extractedDerivationLinear π s hs equiv
    φ (a • e) = SemidirectSMul D a (φ e) := by
  simp only [SemidirectSMul, extractedDerivationLinear, LinearMap.coe_mk, AddHom.coe_mk]
  ext
  · exact extensionToSemidirect_A_linear_aux π s hs equiv a e
  · exact map_smul π a e

/-- Properties showing round-trip compatibility with A-linear equiv. -/
theorem extension_roundtrip_equiv (i : X →ₗ[A] E) (π : E →ₗ[A] Y) (s : Y →ₗ[k] E)
    (hs : ∀ y, π (s y) = y)
    (equiv : X ≃ₗ[A] LinearMap.ker π)
    (hi : i.comp equiv.symm.toLinearMap = Submodule.subtype _) :
    (∀ a e, (equiv.symm ⟨a • e - s (π (a • e)), diff_mem_ker π s hs (a • e)⟩ : X) =
            a • equiv.symm ⟨e - s (π e), diff_mem_ker π s hs e⟩ +
            equiv.symm ⟨a • s (π e) - s (a • π e), extensionDerivationAux_mem_ker π s hs a (π e)⟩) ∧
    (∀ e, π e = (equiv.symm ⟨e - s (π e), diff_mem_ker π s hs e⟩, π e).2) := by
  constructor
  · intro a e; exact extensionToSemidirect_A_linear_aux π s hs equiv a e
  · intro e; rfl

end ALinearRoundTrip

end LemmaFeld.TensorCategories.Chapter1
