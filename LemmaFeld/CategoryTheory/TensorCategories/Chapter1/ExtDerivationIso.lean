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

/-! ## The Derivation-to-Extension Construction

Given a derivation D : A → Hom_k(Y, X), construct the extension 0 → X → E → Y → 0 where:
- E = X × Y as k-vector spaces
- A-action: a • (x, y) = (a • x + D(a)(y), a • y)

This is the "semi-direct product" module structure.
-/

section DerivationToExtension

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
variable [Module k X] [Module k Y] [Module A X] [Module A Y]
variable [IsScalarTower k A X] [IsScalarTower k A Y]

/-- The semi-direct product SMul defined by a derivation D : A → Hom_k(Y, X).
    The A-action is: a • (x, y) = (a • x + D(a)(y), a • y). -/
def SemidirectSMul (D : A → (Y →ₗ[k] X)) (a : A) (p : X × Y) : X × Y :=
  (a • p.1 + D a p.2, a • p.2)

/-- One acts trivially on the X component (up to the derivation) when D(1) = 0. -/
lemma SemidirectSMul.one_smul (D : A → (Y →ₗ[k] X)) (hD1 : D 1 = 0) (p : X × Y) :
    SemidirectSMul D 1 p = p := by
  simp only [SemidirectSMul, hD1, LinearMap.zero_apply, add_zero, _root_.one_smul, Prod.mk.eta]

/-- The derivation-action satisfies the multiplication law when D is a derivation.
    Requires: D(ab) = a • D(b) + D(a) • b (bimodule Leibniz rule). -/
lemma SemidirectSMul.mul_smul' (D : A → (Y →ₗ[k] X))
    (hDmul : ∀ a b : A, D (a * b) = a • D b + D a ∘ₗ DistribMulAction.toLinearMap k Y b)
    (a b : A) (p : X × Y) :
    SemidirectSMul D (a * b) p = SemidirectSMul D a (SemidirectSMul D b p) := by
  simp only [SemidirectSMul]
  ext
  · -- First component: a*b • x + D(ab)(y) = a • (b • x + D(b)(y)) + D(a)(b • y)
    simp only [hDmul, LinearMap.add_apply, LinearMap.comp_apply, DistribMulAction.toLinearMap_apply,
      smul_add, mul_smul, LinearMap.smul_apply]
    abel
  · -- Second component: (a*b) • y = a • (b • y)
    exact mul_smul a b p.2

/-- The derivation-action distributes over addition in X × Y. -/
lemma SemidirectSMul.smul_add (D : A → (Y →ₗ[k] X)) (a : A) (p q : X × Y) :
    SemidirectSMul D a (p + q) = SemidirectSMul D a p + SemidirectSMul D a q := by
  simp only [SemidirectSMul, Prod.fst_add, Prod.snd_add, _root_.smul_add, map_add, Prod.mk_add_mk,
    Prod.mk.injEq]
  exact ⟨by abel, trivial⟩

/-- The derivation-action distributes over addition in A. -/
lemma SemidirectSMul.add_smul (D : A → (Y →ₗ[k] X))
    (hDadd : ∀ a b : A, D (a + b) = D a + D b) (a b : A) (p : X × Y) :
    SemidirectSMul D (a + b) p = SemidirectSMul D a p + SemidirectSMul D b p := by
  simp only [SemidirectSMul, _root_.add_smul, hDadd, LinearMap.add_apply, Prod.mk_add_mk,
    Prod.mk.injEq]
  exact ⟨by abel, trivial⟩

/-- The inclusion X → X × Y in the semi-direct product. -/
abbrev SemidirectInclusion (k : Type*) (X Y : Type*)
    [Semiring k] [AddCommMonoid X] [AddCommMonoid Y] [Module k X] [Module k Y] : X →ₗ[k] X × Y :=
  LinearMap.inl k X Y

/-- The projection X × Y → Y in the semi-direct product. -/
abbrev SemidirectProjection (k : Type*) (X Y : Type*)
    [Semiring k] [AddCommMonoid X] [AddCommMonoid Y] [Module k X] [Module k Y] : X × Y →ₗ[k] Y :=
  LinearMap.snd k X Y

/-- The projection is a split epimorphism with section y ↦ (0, y). -/
abbrev SemidirectSection (k : Type*) (X Y : Type*)
    [Semiring k] [AddCommMonoid X] [AddCommMonoid Y] [Module k X] [Module k Y] : Y →ₗ[k] X × Y :=
  LinearMap.inr k X Y

/-- The section property: projection ∘ section = id. -/
lemma SemidirectProjection_Section (k : Type*) (X Y : Type*)
    [Semiring k] [AddCommMonoid X] [AddCommMonoid Y] [Module k X] [Module k Y] (y : Y) :
    SemidirectProjection k X Y (SemidirectSection k X Y y) = y := rfl

/-- The inclusion lands in the kernel of projection. -/
lemma SemidirectInclusion_mem_ker (k : Type*) (X Y : Type*)
    [Semiring k] [AddCommMonoid X] [AddCommMonoid Y] [Module k X] [Module k Y] (x : X) :
    SemidirectProjection k X Y (SemidirectInclusion k X Y x) = 0 := rfl

/-- The sequence is exact: ker(projection) = range(inclusion). -/
lemma Semidirect_exact (k : Type*) (X Y : Type*)
    [Semiring k] [AddCommMonoid X] [AddCommMonoid Y] [Module k X] [Module k Y] :
    LinearMap.ker (SemidirectProjection k X Y) = LinearMap.range (SemidirectInclusion k X Y) := by
  ext ⟨x, y⟩
  simp only [LinearMap.mem_ker, LinearMap.mem_range, SemidirectProjection, SemidirectInclusion,
    LinearMap.snd_apply, LinearMap.inl_apply, Prod.mk.injEq]
  constructor
  · intro hy; exact ⟨x, rfl, hy.symm⟩
  · rintro ⟨x', _, hy⟩; exact hy.symm

end DerivationToExtension

end LemmaFeld.TensorCategories.Chapter1
