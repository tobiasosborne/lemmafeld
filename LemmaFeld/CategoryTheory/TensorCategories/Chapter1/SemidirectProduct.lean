/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel

/-!
# Semi-direct Product Construction for Module Extensions

This file defines the semi-direct product construction that builds a module extension
from a derivation. This is one direction of the Ext¹ ≅ H¹ isomorphism.

## Main Definitions

* `SemidirectSMul` - The A-action on X × Y given by a derivation D
* `SemidirectInclusion`, `SemidirectProjection`, `SemidirectSection` - The extension maps

## Book Reference

Etingof et al. "Tensor Categories" §1.4, Exercise 1.4.3(ii):
Given D : A → Hom_k(Y, X), construct extension E = X × Y with a • (x,y) = (a•x + D(a)(y), a•y).
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

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
  · simp only [hDmul, LinearMap.add_apply, LinearMap.comp_apply, DistribMulAction.toLinearMap_apply,
      smul_add, mul_smul, LinearMap.smul_apply]
    abel
  · exact mul_smul a b p.2

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

/-- The derivation extracted from a semi-direct product using the canonical section. -/
def semidirectExtractDerivation (D : A → (Y →ₗ[k] X)) (a : A) (y : Y) : X :=
  (SemidirectSMul D a (0, y)).1 - (0 : X)

/-- Extraction computes to D(a)(y). -/
@[simp]
lemma semidirectExtractDerivation_eq (D : A → (Y →ₗ[k] X)) (a : A) (y : Y) :
    semidirectExtractDerivation D a y = D a y := by
  simp only [semidirectExtractDerivation, SemidirectSMul, smul_zero, zero_add, sub_zero]

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

/-! ## Inner Derivations Give Trivial Extensions

**Key Theorem**: If D = D_f is an inner derivation, then the semidirect product extension
is isomorphic to the trivial (split) extension X × Y with diagonal action.

This is crucial for the Ext¹ ≅ H¹ isomorphism: it shows the map H¹ → Ext¹ has
kernel exactly equal to the inner derivations.

For an inner derivation D_f(a)(y) = a • f(y) - f(a • y), the isomorphism is:
  φ(x, y) = (x + f(y), y)

This intertwines the D_f-action with the trivial (diagonal) action.
-/

section InnerDerivationsTrivial

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
variable [Module k X] [Module k Y] [Module A X] [Module A Y]
variable [IsScalarTower k A X] [IsScalarTower k A Y]

/-- The "shearing" map that trivializes an inner derivation extension.
    For f : Y →ₗ[k] X, this maps (x, y) ↦ (x + f(y), y). -/
def innerDerivationShear (f : Y →ₗ[k] X) : (X × Y) →ₗ[k] (X × Y) :=
  LinearMap.prod (LinearMap.fst k X Y + f.comp (LinearMap.snd k X Y)) (LinearMap.snd k X Y)

/-- The inverse shearing map: (x, y) ↦ (x - f(y), y). -/
def innerDerivationShearInv (f : Y →ₗ[k] X) : (X × Y) →ₗ[k] (X × Y) :=
  LinearMap.prod (LinearMap.fst k X Y - f.comp (LinearMap.snd k X Y)) (LinearMap.snd k X Y)

/-- Shear applied to a pair. -/
@[simp] lemma innerDerivationShear_apply (f : Y →ₗ[k] X) (p : X × Y) :
    innerDerivationShear f p = (p.1 + f p.2, p.2) := rfl

/-- Inverse shear applied to a pair. -/
@[simp] lemma innerDerivationShearInv_apply (f : Y →ₗ[k] X) (p : X × Y) :
    innerDerivationShearInv f p = (p.1 - f p.2, p.2) := rfl

/-- The shear and its inverse are mutual inverses. -/
lemma innerDerivationShear_inv (f : Y →ₗ[k] X) :
    (innerDerivationShear f).comp (innerDerivationShearInv f) = LinearMap.id := by
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, innerDerivationShearInv_apply, innerDerivationShear_apply,
    LinearMap.id_apply, sub_add_cancel, Prod.mk.eta]

lemma innerDerivationShearInv_shear (f : Y →ₗ[k] X) :
    (innerDerivationShearInv f).comp (innerDerivationShear f) = LinearMap.id := by
  apply LinearMap.ext
  intro p
  simp only [LinearMap.comp_apply, innerDerivationShear_apply, innerDerivationShearInv_apply,
    LinearMap.id_apply, add_sub_cancel_right, Prod.mk.eta]

/-- The k-linear equivalence given by the shearing map. -/
def innerDerivationShearEquiv (f : Y →ₗ[k] X) : (X × Y) ≃ₗ[k] (X × Y) where
  toLinearMap := innerDerivationShear f
  invFun := innerDerivationShearInv f
  left_inv p := by simp [innerDerivationShear, innerDerivationShearInv, add_sub_cancel_right]
  right_inv p := by simp [innerDerivationShear, innerDerivationShearInv, sub_add_cancel]

/-- **Key Theorem**: The shearing map intertwines the inner derivation action with trivial action.

For an inner derivation D_f(a)(y) = a • f(y) - f(a • y), we have:
  φ(a •_Df (x, y)) = a •_trivial φ(x, y)

where φ(x, y) = (x + f(y), y) and •_trivial is the diagonal action (a • x, a • y). -/
theorem innerDerivation_shear_intertwines (f : Y →ₗ[k] X)
    (D : A → (Y →ₗ[k] X))
    (hD : ∀ a y, D a y = a • f y - f (a • y)) -- D is the inner derivation defined by f
    (a : A) (p : X × Y) :
    innerDerivationShear f (SemidirectSMul D a p) = (a • (innerDerivationShear f p).1,
                                                     a • (innerDerivationShear f p).2) := by
  simp only [innerDerivationShear_apply, SemidirectSMul]
  ext
  · -- First component: a • p.1 + D(a)(p.2) + f(a • p.2) = a • (p.1 + f(p.2))
    simp only [hD, smul_add]
    -- Goal: a • p.1 + (a • f p.2 - f (a • p.2)) + f (a • p.2) = a • p.1 + a • f p.2
    abel
  · -- Second component: a • p.2 = a • p.2  ✓
    rfl

end InnerDerivationsTrivial

/-! ## Split Extensions Give Inner Derivations

**Converse Theorem**: If the semidirect extension E_D admits an A-linear section,
then D is an inner derivation.

Combined with `innerDerivation_shear_intertwines`, this gives:
  E_D is split ⟺ D is inner

This establishes ker(Der → Ext¹) = InnerDer, completing Exercise 1.4.3(ii).
-/

section SplitImpliesInner

variable {k A : Type*} [CommRing k] [Ring A] [Algebra k A]
variable {X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
variable [Module k X] [Module k Y] [Module A X] [Module A Y]
variable [IsScalarTower k A X] [IsScalarTower k A Y]

/-- If the semidirect extension has an A-linear section s'(y) = (g(y), y),
    then D equals the inner derivation defined by -g.

    The A-linearity condition a • s'(y) = s'(a • y) expands to:
      a • g(y) + D(a)(y) = g(a • y)
    i.e., D(a)(y) = g(a • y) - a • g(y) = -D_g(a)(y)

    where D_g(a)(y) = a • g(y) - g(a • y) is the inner derivation from g. -/
theorem split_extension_implies_inner (D : A → (Y →ₗ[k] X))
    (g : Y →ₗ[k] X)
    (hSection : ∀ a y, a • g y + D a y = g (a • y)) :
    ∀ a y, D a y = -(a • g y - g (a • y)) := by
  intro a y
  have h := hSection a y
  -- From h: a • g y + D a y = g (a • y)
  -- Rearrange: D a y = g (a • y) - a • g y = -(a • g y - g (a • y))
  have h1 : D a y = g (a • y) - a • g y := by
    have := add_comm (a • g y) (D a y)
    rw [this] at h
    exact eq_sub_of_add_eq h
  rw [h1]
  abel

/-- **Theorem**: The semidirect extension E_D is split (admits A-linear section)
    if and only if D is an inner derivation.

    The inner derivation D_f is characterized pointwise by: D_f(a)(y) = a • f(y) - f(a • y)

    Forward: If E_D has section s'(y) = (g(y), y) with A-linearity a • g(y) + D(a)(y) = g(a • y),
             then D = -D_g is inner.
    Backward: `innerDerivation_shear_intertwines` -/
theorem semidirect_split_iff_inner (D : A → (Y →ₗ[k] X)) :
    (∃ g : Y →ₗ[k] X, ∀ a y, a • g y + D a y = g (a • y)) ↔
    (∃ f : Y →ₗ[k] X, ∀ a y, D a y = a • f y - f (a • y)) := by
  constructor
  · -- Split extension → inner derivation
    rintro ⟨g, hSection⟩
    use -g
    intro a y
    have h := hSection a y
    simp only [LinearMap.neg_apply, smul_neg]
    -- Goal: D a y = -(a • g y) - -g (a • y) = -a • g y + g (a • y)
    -- From h: a • g y + D a y = g (a • y)
    have h1 : D a y = g (a • y) - a • g y := by
      have := add_comm (a • g y) (D a y)
      rw [this] at h
      exact eq_sub_of_add_eq h
    rw [h1]; abel
  · -- Inner derivation → split extension
    rintro ⟨f, hInner⟩
    use -f
    intro a y
    simp only [LinearMap.neg_apply, smul_neg, hInner]
    abel

end SplitImpliesInner

end LemmaFeld.TensorCategories.Chapter1
