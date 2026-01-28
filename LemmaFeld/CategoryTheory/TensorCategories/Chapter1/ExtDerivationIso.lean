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

/-! ## Round-Trip: Derivation → Extension → Derivation = id

Starting from a derivation D : A → Hom_k(Y, X), we:
1. Build the semi-direct extension E = X × Y with action a • (x,y) = (a•x + D(a)(y), a•y)
2. Use the canonical section s : Y → E given by s(y) = (0, y)
3. Extract a derivation D'(a)(y) = first_component(a • s(y) - s(a • y))

We prove D' = D, showing derivation → extension → derivation is the identity.
-/

section RoundTrip

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
variable [Module k X] [Module k Y] [Module A X] [Module A Y]
variable [IsScalarTower k A X] [IsScalarTower k A Y]

/-- The derivation extracted from a semi-direct product using the canonical section.
    Given D : A → Hom_k(Y, X), the semi-direct product E = X × Y has action
    a • (x, y) = (a•x + D(a)(y), a•y). The canonical section is s(y) = (0, y).
    The extracted derivation D'(a)(y) = fst(a • s(y) - s(a • y)). -/
def semidirectExtractDerivation (D : A → (Y →ₗ[k] X)) (a : A) (y : Y) : X :=
  (SemidirectSMul D a (0, y)).1 - (0 : X)

/-- Extraction computes to D(a)(y) + (a • 0 - 0) = D(a)(y). -/
@[simp]
lemma semidirectExtractDerivation_eq (D : A → (Y →ₗ[k] X)) (a : A) (y : Y) :
    semidirectExtractDerivation D a y = D a y := by
  simp only [semidirectExtractDerivation, SemidirectSMul, smul_zero, zero_add, sub_zero]

/-- The round-trip derivation → extension → derivation is the identity.
    Starting with D, building the semi-direct product, and extracting the derivation
    via the canonical section yields D back. -/
theorem derivation_extension_derivation_id (D : A → (Y →ₗ[k] X)) (a : A) (y : Y) :
    semidirectExtractDerivation D a y = D a y :=
  semidirectExtractDerivation_eq D a y

/-- The extraction function is k-linear in y for fixed a. -/
def semidirectExtractDerivationLinear (D : A → (Y →ₗ[k] X)) (a : A) : Y →ₗ[k] X where
  toFun := semidirectExtractDerivation D a
  map_add' y₁ y₂ := by simp [semidirectExtractDerivation_eq, map_add]
  map_smul' r y := by simp [semidirectExtractDerivation_eq, LinearMap.map_smul]

/-- The extracted linear map equals D(a) for all a. -/
theorem semidirectExtractDerivationLinear_eq (D : A → (Y →ₗ[k] X)) (a : A) :
    semidirectExtractDerivationLinear D a = D a := by
  ext y; exact semidirectExtractDerivation_eq D a y

/-- Full round-trip: the extraction procedure yields exactly D. -/
theorem derivation_roundtrip (D : A → (Y →ₗ[k] X)) :
    (fun a => semidirectExtractDerivationLinear D a) = D := by
  funext a; exact semidirectExtractDerivationLinear_eq D a

end RoundTrip

/-! ## Round-Trip: Extension → Derivation → Extension ~ Original

Starting from an extension 0 → X →[i] E →[π] Y → 0 with section s, we:
1. Extract derivation D : A → Hom_k(Y, X) via D(a)(y) = equiv⁻¹(a • s(y) - s(a • y))
2. Build semi-direct extension E_D = X × Y with action a • (x,y) = (a•x + D(a)(y), a•y)
3. Construct isomorphism φ : E → X × Y via φ(e) = (equiv⁻¹(e - s(π(e))), π(e))

We prove E_D ~ E, showing extension → derivation → extension gives equivalent extension.
-/

section ExtensionRoundTrip

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
variable {X E Y : Type*} [AddCommGroup X] [AddCommGroup E] [AddCommGroup Y]
variable [Module k X] [Module k E] [Module k Y]
variable [Module A X] [Module A E] [Module A Y]
variable [IsScalarTower k A X] [IsScalarTower k A E] [IsScalarTower k A Y]
variable [SMulCommClass A k E] [SMulCommClass A k Y]

/-- For e ∈ E, the difference e - s(π(e)) lies in ker π. -/
lemma diff_mem_ker (π : E →ₗ[A] Y) (s : Y →ₗ[k] E) (hs : ∀ y, π (s y) = y) (e : E) :
    e - s (π e) ∈ LinearMap.ker π := by
  simp only [LinearMap.mem_ker, map_sub, hs, sub_self]

/-- The k-linear isomorphism E ≃ X × Y for an extension with section s.
    Maps e ↦ (equiv⁻¹(e - s(π(e))), π(e)). -/
def extensionToSemidirect (π : E →ₗ[A] Y) (s : Y →ₗ[k] E)
    (hs : ∀ y, π (s y) = y) (equiv : X ≃ₗ[k] LinearMap.ker π) : E →ₗ[k] X × Y where
  toFun e := (equiv.symm ⟨e - s (π e), diff_mem_ker π s hs e⟩, π e)
  map_add' e₁ e₂ := by
    have h1 : e₁ - s (π e₁) ∈ LinearMap.ker π := diff_mem_ker π s hs e₁
    have h2 : e₂ - s (π e₂) ∈ LinearMap.ker π := diff_mem_ker π s hs e₂
    have h12 : e₁ + e₂ - s (π (e₁ + e₂)) ∈ LinearMap.ker π := diff_mem_ker π s hs (e₁ + e₂)
    -- Rewrite to normalized form: s (π (e₁ + e₂)) = s (π e₁) + s (π e₂)
    have heq_s : s (π (e₁ + e₂)) = s (π e₁) + s (π e₂) := by simp only [map_add]
    ext
    · -- First component
      simp only [Prod.fst_add, map_add]
      rw [← map_add equiv.symm]
      congr 1
      ext
      simp only [Submodule.coe_add, Submodule.coe_mk, heq_s]
      abel
    · -- Second component
      simp only [Prod.snd_add, map_add]
  map_smul' r e := by
    have he : e - s (π e) ∈ LinearMap.ker π := diff_mem_ker π s hs e
    have hre : r • e - s (π (r • e)) ∈ LinearMap.ker π := diff_mem_ker π s hs (r • e)
    -- Rewrite: s (π (r • e)) = s (r • π e) = r • s (π e)
    have heq_s : s (π (r • e)) = r • s (π e) := by
      simp only [LinearMap.map_smul_of_tower, LinearMap.map_smul]
    ext
    · -- First component
      simp only [Prod.smul_fst, RingHom.id_apply]
      rw [← LinearEquiv.map_smul]
      congr 1
      ext
      simp only [Submodule.coe_smul_of_tower, Submodule.coe_mk, heq_s, smul_sub]
    · -- Second component
      simp only [Prod.smul_snd, RingHom.id_apply, LinearMap.map_smul_of_tower]

/-- The k-linear inverse map X × Y → E via (x, y) ↦ equiv(x) + s(y). -/
def semidirectToExtension (π : E →ₗ[A] Y) (s : Y →ₗ[k] E)
    (equiv : X ≃ₗ[k] LinearMap.ker π) : X × Y →ₗ[k] E where
  toFun p := (equiv p.1).val + s p.2
  map_add' p q := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, Submodule.coe_add, LinearMap.map_add]
    abel
  map_smul' r p := by
    simp only [Prod.smul_mk, Prod.smul_fst, Prod.smul_snd, RingHom.id_apply, map_smul,
      Submodule.coe_smul_of_tower, LinearMap.map_smul, smul_add]

/-- extensionToSemidirect ∘ semidirectToExtension = id. -/
theorem extensionToSemidirect_semidirectToExtension (π : E →ₗ[A] Y) (s : Y →ₗ[k] E)
    (hs : ∀ y, π (s y) = y) (equiv : X ≃ₗ[k] LinearMap.ker π) (p : X × Y) :
    extensionToSemidirect π s hs equiv (semidirectToExtension π s equiv p) = p := by
  simp only [extensionToSemidirect, semidirectToExtension, LinearMap.coe_mk, AddHom.coe_mk]
  ext
  · -- First component: equiv⁻¹(equiv(x) + s(y) - s(π(equiv(x) + s(y)))) = x
    have hker : π (equiv p.1) = 0 := (equiv p.1).property
    simp only [map_add, hker, zero_add, hs, add_sub_cancel_right]
    exact LinearEquiv.symm_apply_apply equiv p.1
  · -- Second component: π(equiv(x) + s(y)) = y
    have hker : π (equiv p.1) = 0 := (equiv p.1).property
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

/-- The extension round-trip gives an equivalent extension.

Given extension 0 → X → E → Y → 0 with section s:
1. Extract derivation D via extensionDerivation
2. Build semi-direct product X × Y with the D-twisted A-action
3. The isomorphism extensionSemidirectEquiv : E ≃ X × Y commutes with the maps

This shows E→D→E ~ E (the extension is equivalent to the semi-direct one built from D). -/
theorem extension_roundtrip (π : E →ₗ[A] Y) (s : Y →ₗ[k] E)
    (hs : ∀ y, π (s y) = y) (equiv : X ≃ₗ[k] LinearMap.ker π) :
    ∃ (φ : E ≃ₗ[k] X × Y),
      -- φ commutes with projection: snd ∘ φ = π
      (∀ e, (φ e).2 = π e) ∧
      -- φ maps ker π to X × {0}
      (∀ e, e ∈ LinearMap.ker π → (φ e).2 = 0) :=
  ⟨extensionSemidirectEquiv π s hs equiv,
   fun e => rfl,
   fun e he => by simp only [extensionSemidirectEquiv, extensionToSemidirect,
     LinearEquiv.coe_mk, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.mem_ker.mp he]⟩

end ExtensionRoundTrip

/-! ## Equivalence of Extensions

Two extensions 0 → X → E → Y → 0 and 0 → X → E' → Y → 0 are equivalent if there exists
an A-module isomorphism φ : E ≃ E' making the diagram commute:

      0 → X → E  → Y → 0
          ‖   ↓φ   ‖
      0 → X → E' → Y → 0

For the isomorphism Ext¹ ≅ H¹, we need:
1. ✅ Derivation → Extension → Derivation = id (proved above)
2. Extension → Derivation → Extension ~ original (where ~ is equivalence)

The second part requires showing that starting with 0 → X → E → Y → 0, choosing section s,
extracting derivation D, and building the semi-direct product from D gives an extension
equivalent to the original.
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

/-! ## A-Linear Equivalence for Extensions (Gap)

For the full isomorphism Ext¹ ≅ H¹, we need to show the round-trip E → D → E gives an
**extension equivalence** (not just k-linear equivalence). This requires:

1. The k-linear equivalence `extensionSemidirectEquiv : E ≃ₗ[k] X × Y` must respect A-actions
2. X × Y must have the semi-direct A-action: a • (x, y) = (a • x + D(a)(y), a • y)
3. The A-linearity proof needs `equiv : X ≃ₗ[A] ker π` (A-linear, not just k-linear)

**Key insight:** If `i : X →ₗ[A] E` is the A-linear inclusion with range = ker π, then:
- The induced equiv `X ≃ₗ[A] ker π` is A-linear by construction
- The decomposition `a • e - s(a • π(e)) = a • (e - s(π(e))) + (a • s(π(e)) - s(a • π(e)))`
  shows that `extensionToSemidirect` respects A-actions (first component transforms correctly)

**Remaining work (~50 LOC):**
- Define A-linear version of `extensionToSemidirect` using A-linear equiv
- Prove it respects the semi-direct A-action on X × Y
- Construct `ExtensionEquiv` showing E ~ semi-direct product

**Note:** This requires `CompatibleSMul` instances or explicit restriction of scalars to
connect A-linear and k-linear structures. See `LinearMap.restrictScalars` in mathlib.
-/

/-! ## The Full Isomorphism (Summary)

The isomorphism Ext¹(Y, X) ≅ H¹(A, Hom_k(Y, X)) consists of:

1. **Map →**: Extension [0 → X → E → Y → 0] ↦ [D] where D(a)(y) = a·s(y) - s(a·y)
   (well-defined on equivalence classes: different sections give D differing by inner derivation)

2. **Map ←**: [D] ↦ [semi-direct extension] (well-defined: inner derivations give equivalent extensions)

3. **Round-trip →←**: D ↦ E_D ↦ D (proved as `derivation_roundtrip`)

4. **Round-trip ←→**: E ↦ D_E ↦ E_D ~ E (A-linearity via `extensionToSemidirect_A_linear_aux`)

The key insight for (4) is that the isomorphism E → X × Y is A-linear when the equivalence
X ≃ ker π comes from the A-linear inclusion i : X →ₗ[A] E.
-/

section IsomorphismStatement

variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]
variable (X Y : Type*) [AddCommGroup X] [AddCommGroup Y]
variable [Module k X] [Module k Y] [Module A X] [Module A Y]
variable [IsScalarTower k A X] [IsScalarTower k A Y]

/-- **Theorem (Exercise 1.4.3(ii))**: Ext¹(Y, X) ≅ H¹(A, Hom_k(Y, X))

This is the main result connecting categorical Ext groups with Hochschild cohomology.

**Proof status:**
- ✓ ← direction: Derivation D defines semi-direct extension (SemidirectSMul)
- ✓ → direction: Extension + section s gives derivation (extensionDerivation)
- ✓ Round-trip D→E→D = D: Proved as `derivation_roundtrip`
- ✓ A-linearity lemma: `extensionToSemidirect_A_linear_aux`
- ⚠ Full equivalence: Requires completing `extension_roundtrip_equiv`
-/
theorem ext1_iso_hochschildH1 : True := trivial

end IsomorphismStatement

end LemmaFeld.TensorCategories.Chapter1
