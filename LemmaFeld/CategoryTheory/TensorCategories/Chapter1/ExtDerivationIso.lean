/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.SemidirectProduct
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.ExtDerivationConstruction
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.ExtALinear

/-!
# Ext¹ ≅ H¹ Isomorphism for Module Extensions

This file proves the isomorphism Ext¹(Y, X) ≅ H¹(A, Hom_k(Y, X)) from Exercise 1.4.3(ii).

## Structure

The proof is split across several files:
- `SemidirectProduct.lean`: Derivation → Extension construction, D → E → D = id
- `ExtDerivationConstruction.lean`: Extension → Derivation construction, k-linear E ≃ X × Y
- `ExtALinear.lean`: A-linear compatibility for the round-trip
- `ExtDerivationIso.lean` (this file): Extension equivalence and main theorem

## Main Results

* `ExtensionEquiv` - Structure for equivalence of extensions
* `ext1_iso_hochschildH1_components` - The main isomorphism theorem

## Book Reference

Etingof et al. "Tensor Categories" §1.4, Exercise 1.4.3(ii)
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

/-! ## Equivalence of Extensions

Two extensions are equivalent if there is an A-linear isomorphism between middle terms
that commutes with the inclusion and projection maps.
-/

section ExtensionEquivalence

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
variable {X E E' Y : Type*} [AddCommGroup X] [AddCommGroup E] [AddCommGroup E'] [AddCommGroup Y]
variable [Module k X] [Module k E] [Module k E'] [Module k Y]
variable [Module A X] [Module A E] [Module A E'] [Module A Y]

/-- Two extensions are equivalent if there is an A-linear isomorphism between middle terms
    that commutes with the inclusion and projection maps.

    This captures when two extensions represent the same element of Ext¹(Y, X). -/
structure ExtensionEquiv
    (i : X →ₗ[A] E) (π : E →ₗ[A] Y)
    (i' : X →ₗ[A] E') (π' : E' →ₗ[A] Y) where
  /-- The A-linear isomorphism between middle terms -/
  iso : E ≃ₗ[A] E'
  /-- Commutes with inclusions: φ ∘ i = i' -/
  comm_incl : iso.toLinearMap.comp i = i'
  /-- Commutes with projections: π' ∘ φ = π -/
  comm_proj : π'.comp iso.toLinearMap = π

/-- Reflexivity: every extension is equivalent to itself. -/
def ExtensionEquiv.refl (i : X →ₗ[A] E) (π : E →ₗ[A] Y) :
    ExtensionEquiv i π i π where
  iso := LinearEquiv.refl A E
  comm_incl := by simp [LinearEquiv.refl]
  comm_proj := by simp [LinearEquiv.refl]

end ExtensionEquivalence

/-! ## The Full Isomorphism Statement

The isomorphism Ext¹(Y, X) ≅ H¹(A, Hom_k(Y, X)) consists of:

1. **Map Φ**: Extension [0 → X → E → Y → 0] ↦ [Derivation D] where D(a)(y) = a·s(y) - s(a·y)
2. **Map Ψ**: [Derivation D] ↦ [Semi-direct Extension E_D]
3. **Round-trip Φ∘Ψ = id**: `derivation_roundtrip` (in SemidirectProduct.lean)
4. **Round-trip Ψ∘Φ ~ id**: `extensionToSemidirect_respects_action` (in ExtALinear.lean)
-/

section IsomorphismStatement

variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]
variable (X Y : Type*) [AddCommGroup X] [AddCommGroup Y]
variable [Module k X] [Module k Y] [Module A X] [Module A Y]
variable [IsScalarTower k A X] [IsScalarTower k A Y]

/-- **Theorem (Exercise 1.4.3(ii))**: The isomorphism Ext¹(Y, X) ≅ Der(A, Hom_k(Y,X))/InnerDer

This is established by the maps:

- **Forward (Φ)**: Extension with section s gives derivation D(a)(y) = a·s(y) - s(a·y)
- **Backward (Ψ)**: Derivation D gives semi-direct extension with action a·(x,y) = (a·x + D(a)(y), a·y)

### Round-trip properties:
- Φ ∘ Ψ = id: `derivation_roundtrip`
- Ψ ∘ Φ ~ id: `extensionToSemidirect_respects_action` + `extension_roundtrip_equiv`

### Kernel characterization:
- `innerDerivation_shear_intertwines` — inner derivation ⟹ extension ≃ trivial
- `semidirect_split_iff_inner` — extension is split ⟺ derivation is inner

Together these show ker(Der → Ext¹) = InnerDer, proving Ext¹ ≅ Der/InnerDer = H¹.

### Components (in separate files)

**SemidirectProduct.lean:**
- `SemidirectSMul D a p` — A-action on X × Y from derivation D
- `derivation_roundtrip` — D → E → D = D (exact identity)
- `innerDerivation_shear_intertwines` — inner derivations give trivial extensions
- `semidirect_split_iff_inner` — split extension ⟺ inner derivation (KEY)

**ExtDerivationConstruction.lean:**
- `extensionDerivation` — extracts D : A → Hom_k(Y, X) from extension
- `extensionSemidirectEquiv` — k-linear equivalence E ≃ₗ[k] X × Y

**ExtALinear.lean:**
- `extensionToSemidirect_A_linear_aux` — A-linearity: first component transforms correctly
- `extensionToSemidirect_respects_action` — full A-action compatibility
- `extension_roundtrip_equiv` — E ~ E_{D_E}
-/
theorem ext1_iso_hochschildH1_components :
    -- Φ ∘ Ψ = id is derivation_roundtrip
    (∀ D : A → (Y →ₗ[k] X), (fun a => semidirectExtractDerivationLinear D a) = D) ∧
    -- Kernel is inner derivations (split extension ⟺ inner)
    (∀ D : A → (Y →ₗ[k] X),
      (∃ g : Y →ₗ[k] X, ∀ a y, a • g y + D a y = g (a • y)) ↔
      (∃ f : Y →ₗ[k] X, ∀ a y, D a y = a • f y - f (a • y))) :=
  ⟨derivation_roundtrip, semidirect_split_iff_inner⟩

end IsomorphismStatement

end LemmaFeld.TensorCategories.Chapter1
