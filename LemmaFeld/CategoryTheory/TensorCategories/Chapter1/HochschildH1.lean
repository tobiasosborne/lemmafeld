/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.InnerDerivations
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# First Hochschild Cohomology

This file defines the first Hochschild cohomology H¹(A, M) as a quotient module.

## Main Definitions

* `HochschildH1 R A M` — the quotient (A →ₗ[R] M) / InnerDerivations
* `HochschildH1.mk` — the quotient map

## Mathematical Background

The first Hochschild cohomology H¹(A, M) is defined as:
  H¹(A, M) = Der(A, M) / InnerDer(A, M)

For the full definition, we should quotient the bimodule derivations Der(A, M).
Here we define a preliminary version as the quotient of all linear maps
by inner derivations.

## References

- Etingof et al. "Tensor Categories" (AMS 2015), §1.4, Exercise 1.4.3(ii)
- Weibel "An Introduction to Homological Algebra" (CUP 1994), §9.1-9.2

-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

section HochschildH1

variable (R A M : Type*) [CommRing R] [CommRing A] [AddCommGroup M]
variable [Algebra R A] [Module A M] [Module Aᵐᵒᵖ M] [Module R M]
variable [IsScalarTower R A M] [IsScalarTower R Aᵐᵒᵖ M] [SMulCommClass R Aᵐᵒᵖ M]

/-- The first Hochschild cohomology H¹(A, M) as a quotient module.

Formally, H¹(A, M) should be Der(A, M) / InnerDer(A, M) where Der(A, M) consists
of maps satisfying the bimodule Leibniz rule. This definition gives the quotient
of all R-linear maps by inner derivations, which equals H¹ when restricted to
maps satisfying the Leibniz rule.

For A-modules X, Y and M = Hom_k(Y, X), Exercise 1.4.3(ii) shows:
  Ext¹(Y, X) ≅ H¹(A, Hom_k(Y, X))
-/
abbrev HochschildH1 := (A →ₗ[R] M) ⧸ InnerDerivations R A M

/-- The quotient map from linear maps to H¹. -/
def HochschildH1.mk : (A →ₗ[R] M) →ₗ[R] HochschildH1 R A M :=
  (InnerDerivations R A M).mkQ

/-- An element represents the zero class in H¹ iff it is an inner derivation. -/
theorem HochschildH1.mk_eq_zero (D : A →ₗ[R] M) :
    HochschildH1.mk R A M D = 0 ↔ D ∈ InnerDerivations R A M :=
  Submodule.Quotient.mk_eq_zero (InnerDerivations R A M)

/-- Two linear maps represent the same class in H¹ iff they differ by inner derivation. -/
theorem HochschildH1.mk_eq_mk (D₁ D₂ : A →ₗ[R] M) :
    HochschildH1.mk R A M D₁ = HochschildH1.mk R A M D₂ ↔
    D₁ - D₂ ∈ InnerDerivations R A M := by
  rw [← sub_eq_zero, ← LinearMap.map_sub, HochschildH1.mk_eq_zero]

/-- H¹ is zero iff every linear map is inner. -/
theorem HochschildH1.eq_bot_iff :
    (⊤ : Submodule R (HochschildH1 R A M)) = ⊥ ↔
    InnerDerivations R A M = ⊤ := by
  rw [Submodule.eq_bot_iff, Submodule.eq_top_iff']
  constructor
  · intro h D
    have hmem : HochschildH1.mk R A M D ∈ (⊤ : Submodule R (HochschildH1 R A M)) :=
      Submodule.mem_top
    have heq : HochschildH1.mk R A M D = 0 := h _ hmem
    rwa [HochschildH1.mk_eq_zero] at heq
  · intro h x _
    obtain ⟨D, rfl⟩ := (InnerDerivations R A M).mkQ_surjective x
    simp only [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact h D

end HochschildH1

end LemmaFeld.TensorCategories.Chapter1
