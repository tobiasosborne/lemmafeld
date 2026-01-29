/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.InnerDerivations
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.HochschildH1
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.BimoduleDerivations
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Chapter 1, Exercise 1.4.3(ii): Ext¹ as Derivations

This file documents Exercise 1.4.3(ii) from Etingof et al. "Tensor Categories" §1.4.

## Book Statement

**Exercise 1.4.3(ii)**: Let A be an algebra over an algebraically closed field k, and
let C = A-mod be the category of A-modules. Show that

  Ext¹(Y, X) = Der(A, Homₖ(Y, X)) / B(Y, X)

where:
- Der(A, Homₖ(Y, X)) = {D : A → Homₖ(Y, X) | D(ab) = D(a)b + aD(b)}
  (derivations from A to the A-bimodule Homₖ(Y, X))
- B(Y, X) = inner derivations, i.e., D(a) = [f, a] for some f ∈ Homₖ(Y, X)

## Mathematical Background

For A-modules X and Y, the k-vector space Homₖ(Y, X) carries an A-bimodule structure:
- Left action: (a · f)(y) = a · f(y)
- Right action: (f · a)(y) = f(a · y)

A derivation D : A → Homₖ(Y, X) satisfies:
  D(ab) = a · D(b) + D(a) · b = a D(b) + D(a) b

An inner derivation is of the form D_f(a) = a · f - f · a = [a, f] for some f ∈ Homₖ(Y, X).

The quotient Der(A, M) / InnerDer(A, M) is the first Hochschild cohomology H¹(A, M).

## Connection to Extensions

Given an extension 0 → X → E → Y → 0 of A-modules, choose a k-linear splitting s : Y → E.
Define D(a)(y) = a · s(y) - s(a · y). This is a derivation, and different splittings
give derivations differing by an inner derivation.

Conversely, given a derivation D : A → Homₖ(Y, X), construct the extension with:
- E = X ⊕ Y as k-vector spaces
- A-action: a · (x, y) = (a · x + D(a)(y), a · y)

This establishes the isomorphism Ext¹(Y, X) ≅ H¹(A, Homₖ(Y, X)).

## File Organization

The implementation is split across multiple files:

* `InnerDerivations.lean` — `InnerDerivation` structure, `InnerDerivations` submodule
* `HochschildH1.lean` — `HochschildH1` quotient module
* `BimoduleDerivations.lean` — `BimoduleDerivations` submodule and inclusion theorem
* `ExtAsDerivations.lean` (this file) — overview, bimodule structure, Ext context

## Mathlib Status

### What Mathlib Has

| Concept | Mathlib | Import |
|---------|---------|--------|
| Derivation R A M | `Derivation R A M` | `Mathlib.RingTheory.Derivation.Basic` |
| Leibniz rule | `Derivation.leibniz` | same |
| Derivations form A-module | `Module A (Derivation R A M)` | same |
| Ext^n(X, Y) | `Ext X Y n` | `Mathlib.Algebra.Homology.DerivedCategory.Ext` |
| ModuleCat | `ModuleCat R` | `Mathlib.Algebra.Category.ModuleCat.Basic` |

### What Mathlib Lacks (Gaps)

1. **Hochschild cohomology**: No H^n(A, M) = Ext^n_{A^e}(A, M) formalization
2. **The isomorphism**: No proof that Ext¹_A(Y, X) ≅ H¹(A, Homₖ(Y, X))

## References

- Etingof et al. "Tensor Categories" (AMS 2015), §1.4, Exercise 1.4.3(ii)
- Weibel "An Introduction to Homological Algebra" (CUP 1994), §9.1-9.2 (Hochschild cohomology)

-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory

/-! ## Derivations in Mathlib

Mathlib defines derivations from an R-algebra A to an A-module M.
-/

section DerivationsInMathlib

variable (R A M : Type*) [CommSemiring R] [CommSemiring A] [AddCommMonoid M]
variable [Algebra R A] [Module A M] [Module R M]

-- A derivation is an R-linear map D : A → M satisfying the Leibniz rule
-- D(ab) = a • D(b) + b • D(a)
example : Type _ := Derivation R A M

-- Derivations form an R-module (under appropriate conditions)
example : AddCommMonoid (Derivation R A M) := inferInstance

-- The Leibniz rule
example (D : Derivation R A M) (a b : A) : D (a * b) = a • D b + b • D a :=
  D.leibniz a b

-- D(1) = 0
example (D : Derivation R A M) : D 1 = 0 := D.map_one_eq_zero

end DerivationsInMathlib

/-! ## The A-bimodule Structure on Hom_k(Y, X)

For A-modules X and Y, Hom_k(Y, X) has a natural A-bimodule structure.
-/

section BimoduleStructure

variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]
variable (X Y : Type*) [AddCommGroup X] [AddCommGroup Y]
variable [Module k X] [Module k Y] [Module A X] [Module A Y]

-- Hom_k(Y, X) as a k-module
example : Module k (Y →ₗ[k] X) := inferInstance

/-! ### Left A-module structure on Hom_k(Y, X)

The LEFT action (a • f)(y) = a • f(y) requires:
- `[Module A X]` for A to act on the codomain
- `[SMulCommClass k A X]` for k and A actions to commute on X
-/

-- With SMulCommClass, the standard Module instance gives us left action
variable [SMulCommClass k A X]

-- This is the left A-module structure: (a • f)(y) = a • f(y)
example : Module A (Y →ₗ[k] X) := inferInstance

-- Verify the action is what we expect
example (a : A) (f : Y →ₗ[k] X) (y : Y) : (a • f) y = a • f y := rfl

/-! ### Right A-module structure (Aᵐᵒᵖ action) on Hom_k(Y, X)

The RIGHT action (f • a)(y) = f(a • y) is given by precomposition.
This is modeled as a left Aᵐᵒᵖ-action: (op a • f)(y) = f(a • y).

We define the SMul instance explicitly via precomposition with scalar mult.
-/

variable [SMulCommClass A k Y]

/-- Right A-action on Hom_k(Y, X) via precomposition: `(f ⬝ a)(y) = f(a • y)`.
    Modeled as Aᵐᵒᵖ left-action. -/
def HomRightSMul (a : Aᵐᵒᵖ) (f : Y →ₗ[k] X) : Y →ₗ[k] X :=
  f.comp (DistribMulAction.toLinearMap k Y (MulOpposite.unop a))

-- Verify this gives the expected formula
example (a : A) (f : Y →ₗ[k] X) (y : Y) :
    HomRightSMul k A X Y (MulOpposite.op a) f y = f (a • y) := rfl

end BimoduleStructure

/-! ## Ext in ModuleCat

For the category of A-modules, Ext groups are defined.
-/

section ExtInModuleCat

universe u
variable (R : Type u) [CommRing R]

-- ModuleCat R is an abelian category
example : CategoryTheory.Abelian (ModuleCat.{u} R) := inferInstance

-- Therefore Ext groups exist (with appropriate universe constraints)
-- Ext X Y n : Type for X, Y : ModuleCat R and n : ℕ

end ExtInModuleCat

/-! ## Summary

Exercise 1.4.3(ii) asserts: Ext¹_A(Y, X) ≅ Der(A, Hom_k(Y, X)) / InnerDer(A, Hom_k(Y, X)).

This module (across split files) provides: `InnerDerivation`, `InnerDerivations`,
`HochschildH1`, `HomRightSMul`, `BimoduleDerivations`, `InnerDerivations_le_BimoduleDerivations`.

**Gap:** The explicit isomorphism Ext¹ ≅ H¹ is not yet formalized.
-/

end LemmaFeld.TensorCategories.Chapter1
