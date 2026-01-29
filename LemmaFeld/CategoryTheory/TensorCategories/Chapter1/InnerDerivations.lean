/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.RingTheory.Derivation.Basic

/-!
# Inner Derivations

This file defines inner derivations for bimodules, which are derivations of the form
D_f(a) = a • f - f • a for some element f.

## Main Definitions

* `InnerDerivation R A M` — structure for an inner derivation defined by f ∈ M
* `innerDerivationMap R A M` — the R-linear map f ↦ D_f
* `InnerDerivations R A M` — submodule of linear maps that are inner derivations

## References

- Etingof et al. "Tensor Categories" (AMS 2015), §1.4, Exercise 1.4.3(ii)
- Weibel "An Introduction to Homological Algebra" (CUP 1994), §9.1-9.2

-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

/-! ### Inner Derivations

For a bimodule M (with left A-action and right A-action via Aᵐᵒᵖ), an inner derivation
D_f is defined by an element f ∈ M as:
  D_f(a) = a • f - f • a

where the right action "f • a" is expressed as `MulOpposite.op a • f`.

Inner derivations satisfy the bimodule Leibniz rule:
  D_f(ab) = a · D_f(b) + D_f(a) · b
-/

section InnerDerivations

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

/-! ### Inner Derivations as a Submodule

The map f ↦ D_f is R-linear, so its range (the inner derivations) forms a submodule
of the R-module of R-linear maps A →ₗ[R] M.
-/

section InnerDerivationsSubmodule

variable (R A M : Type*) [CommSemiring R] [CommSemiring A] [AddCommGroup M]
variable [Algebra R A] [Module A M] [Module Aᵐᵒᵖ M] [Module R M]
variable [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]

/-- The map f ↦ D_f sending an element to its inner derivation.
This is R-linear, so its range is a submodule. -/
def innerDerivationMap : M →ₗ[R] (A →ₗ[R] M) where
  toFun f := (InnerDerivation.mk f).toLinearMap
  map_add' f g := by
    ext a
    simp only [InnerDerivation.toLinearMap, InnerDerivation.toFun, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.add_apply]
    -- Goal: a • (f + g) - op a • (f + g) = (a • f - op a • f) + (a • g - op a • g)
    rw [smul_add, smul_add]
    abel
  map_smul' r f := by
    ext a
    simp only [InnerDerivation.toLinearMap, InnerDerivation.toFun, LinearMap.coe_mk,
      AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply, smul_sub]
    -- Goal: a • (r • f) - op a • (r • f) = r • (a • f - op a • f)
    -- Need SMulCommClass R A M for a • (r • f) = r • (a • f)
    rw [smul_comm r a f, smul_comm r (MulOpposite.op a) f]

/-- The submodule of inner derivations in the space of R-linear maps A →ₗ[R] M.
An inner derivation is D_f(a) = a • f - (op a) • f for some f ∈ M. -/
def InnerDerivations : Submodule R (A →ₗ[R] M) :=
  LinearMap.range (innerDerivationMap R A M)

/-- An element of M maps to an inner derivation. -/
lemma mem_innerDerivations (f : M) :
    (InnerDerivation.mk f).toLinearMap ∈ InnerDerivations R A M :=
  ⟨f, rfl⟩

/-- Characterization: a linear map is an inner derivation iff it equals D_f for some f. -/
lemma mem_innerDerivations_iff (D : A →ₗ[R] M) :
    D ∈ InnerDerivations R A M ↔ ∃ f : M, D = (InnerDerivation.mk f).toLinearMap := by
  simp only [InnerDerivations, LinearMap.mem_range]
  constructor <;> rintro ⟨f, hf⟩ <;> exact ⟨f, hf.symm⟩

end InnerDerivationsSubmodule

end InnerDerivations

end LemmaFeld.TensorCategories.Chapter1
