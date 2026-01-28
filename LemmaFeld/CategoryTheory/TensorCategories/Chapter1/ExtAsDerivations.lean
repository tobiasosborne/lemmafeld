/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.RingTheory.Derivation.Basic
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

1. **Inner derivations**: No explicit `InnerDerivation` type or `innerDerivation f` constructor
2. **Hochschild cohomology**: No H^n(A, M) = Ext^n_{A^e}(A, M) formalization
3. **The isomorphism**: No proof that Ext¹_A(Y, X) ≅ H¹(A, Homₖ(Y, X))

## Implementation Notes

The full proof of Exercise 1.4.3(ii) would require:

1. Define inner derivations for an A-bimodule M:
   ```
   def InnerDerivation (R A M) [Algebra R A] [Module A M] [Module Aᵐᵒᵖ M] := ...
   ```

2. Show inner derivations form a submodule of derivations

3. Define the quotient as first Hochschild cohomology:
   ```
   def HochschildH1 (A M) := Derivation k A M ⧸ InnerDerivation k A M
   ```

4. For A-modules X, Y, make Homₖ(Y, X) into an A-bimodule

5. Construct explicit maps between extensions and derivations

6. Show the maps are inverses up to the appropriate equivalences

This is a significant formalization project beyond the scope of a single session.

## References

- Etingof et al. "Tensor Categories" (AMS 2015), §1.4, Exercise 1.4.3(ii)
- Weibel "An Introduction to Homological Algebra" (CUP 1994), §9.1-9.2 (Hochschild cohomology)
- Loday "Cyclic Homology" (Springer 1992), Ch. 1

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
-- Note: Module A (Derivation R A M) requires additional SMulCommClass conditions
example : AddCommMonoid (Derivation R A M) := inferInstance

-- The Leibniz rule
example (D : Derivation R A M) (a b : A) : D (a * b) = a • D b + b • D a :=
  D.leibniz a b

-- D(1) = 0
example (D : Derivation R A M) : D 1 = 0 := D.map_one_eq_zero

end DerivationsInMathlib

/-! ## Inner Derivations (Not in Mathlib)

For an A-bimodule M, an inner derivation is D_f(a) = a • f - f • a for some f ∈ M.

In the case M = Hom_k(Y, X) with Y, X being A-modules:
- Left action: (a • φ)(y) = a · φ(y)
- Right action: (φ • a)(y) = φ(a · y)

So D_f(a)(y) = a · f(y) - f(a · y) = [a, f](y)
-/

section InnerDerivations

-- NOTE: Inner derivations are NOT formalized in mathlib
-- The book's B(Y, X) would be defined as:
--
-- structure InnerDerivation (R A M) [CommSemiring R] [CommSemiring A]
--     [AddCommMonoid M] [Algebra R A] [Module A M] [Module Aᵐᵒᵖ M] [Module R M] where
--   element : M
--
-- def InnerDerivation.toDerivation (D : InnerDerivation R A M) : Derivation R A M where
--   toLinearMap := { toFun := fun a => a • D.element - D.element • a, ... }
--   ...

end InnerDerivations

/-! ## The A-bimodule Structure on Hom_k(Y, X)

For A-modules X and Y, Hom_k(Y, X) has a natural A-bimodule structure.
-/

section BimoduleStructure

variable (k A : Type*) [CommRing k] [Ring A] [Algebra k A]
variable (X Y : Type*) [AddCommGroup X] [AddCommGroup Y]
variable [Module k X] [Module k Y] [Module A X] [Module A Y]

-- Hom_k(Y, X) as a k-module
example : Module k (Y →ₗ[k] X) := inferInstance

-- The A-module structure on Hom_k(Y, X) via composition:
-- For the LEFT action (a • f)(y) = a • f(y):
-- This requires [Module A X] and compatibility [IsScalarTower k A X] typically

-- For the RIGHT action (f • a)(y) = f(a • y):
-- This requires [Module A Y] and the action to commute appropriately

-- Full bimodule structure would need Aᵐᵒᵖ action as well

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

Exercise 1.4.3(ii) asserts the isomorphism:

  Ext¹_A(Y, X) ≅ Der(A, Hom_k(Y, X)) / InnerDer(A, Hom_k(Y, X))

This is a classical result connecting:
- Categorical cohomology (Ext groups)
- Hochschild cohomology (derivations modulo inner derivations)

The proof involves:
1. From extension to derivation: use a k-linear splitting
2. From derivation to extension: construct the semi-direct product module

Mathlib has the building blocks (Derivation, Ext, ModuleCat) but not:
- Inner derivations
- The Hom bimodule structure
- The explicit isomorphism

This is noted as a gap for potential future formalization work.
-/

end LemmaFeld.TensorCategories.Chapter1
