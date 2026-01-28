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

/-! ### Inner Derivations (Not in Mathlib)

For a bimodule M (with left A-action and right A-action via Aᵐᵒᵖ), an inner derivation
D_f is defined by an element f ∈ M as:
  D_f(a) = a • f - f • a

where the right action "f • a" is expressed as `MulOpposite.op a • f`.

Inner derivations satisfy the bimodule Leibniz rule:
  D_f(ab) = a · D_f(b) + D_f(a) · b

This is a different form than mathlib's `Derivation` which uses D(ab) = a • D(b) + b • D(a).
-/

/-- An inner derivation in a bimodule, defined by an element f ∈ M.
For a bimodule M (with left A-action and right Aᵐᵒᵖ-action), the inner derivation
D_f sends a ↦ a • f - MulOpposite.op a • f (i.e., a • f - f • a in bimodule notation).

This corresponds to the book's B(Y, X) = inner derivations for Hom_k(Y, X). -/
structure InnerDerivation (R A M : Type*) [CommSemiring R] [CommSemiring A]
    [AddCommGroup M] [Algebra R A] [Module A M] [Module Aᵐᵒᵖ M] [Module R M] where
  /-- The element defining the inner derivation -/
  element : M

namespace InnerDerivation

variable {R A M : Type*} [CommSemiring R] [CommSemiring A] [AddCommGroup M]
variable [Algebra R A] [Module A M] [Module Aᵐᵒᵖ M] [Module R M]

/-- The underlying function of an inner derivation: a ↦ a • f - MulOpposite.op a • f -/
def toFun (D : InnerDerivation R A M) (a : A) : M :=
  a • D.element - MulOpposite.op a • D.element

section LinearMap

variable [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]

/-- The inner derivation as an R-linear map.
Requires scalar tower and commutativity conditions for R-linearity. -/
def toLinearMap (D : InnerDerivation R A M) : A →ₗ[R] M where
  toFun := D.toFun
  map_add' a b := by simp only [toFun, add_smul, MulOpposite.op_add, add_sub_add_comm]
  map_smul' r a := by
    simp only [toFun, RingHom.id_apply, Algebra.smul_def]
    rw [mul_smul, MulOpposite.op_mul, mul_smul, smul_sub]
    congr 1
    · rw [algebraMap_smul]
    · rw [show MulOpposite.op (algebraMap R A r) = algebraMap R Aᵐᵒᵖ r by
        simp [Algebra.algebraMap_eq_smul_one]]
      rw [algebraMap_smul, smul_comm]

end LinearMap

-- Convenience: coerce to function
instance : CoeFun (InnerDerivation R A M) (fun _ => A → M) where
  coe := toFun

@[simp]
lemma toFun_apply (D : InnerDerivation R A M) (a : A) :
    D a = a • D.element - MulOpposite.op a • D.element := rfl

end InnerDerivation

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

-- SMulCommClass A k Y means: ∀ a : A, ∀ c : k, ∀ y : Y, a • (c • y) = c • (a • y)
-- This is typically derivable from IsScalarTower k A Y
variable [SMulCommClass A k Y]

-- Right action defined via precomposition: (op a • f) = f ∘ (a • ·)
-- Use DistribMulAction.toLinearMap which gives a k-linear endomorphism from A-action
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
