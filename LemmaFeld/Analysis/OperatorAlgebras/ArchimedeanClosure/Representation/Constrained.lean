/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Algebra.FreeStarAlgebra
import Mathlib.Algebra.Star.StarAlgHom
import Mathlib.Analysis.InnerProductSpace.Positive

/-! # Constrained *-Representations

A constrained *-representation is a *-algebra homomorphism π : A₀ → B(H) to
bounded operators on a Hilbert space, where each generator maps to a positive operator.

## Main definitions

* `ConstrainedStarRep n` - A *-representation π with π(gⱼ) ≥ 0 for all j

## Mathematical Background

The generators gⱼ of the free *-algebra represent positive observables (position, etc.).
A constrained representation respects this positivity: π(gⱼ) is a positive operator.
-/

open scoped ComplexOrder

namespace ArchimedeanClosure

variable {n : ℕ}

/-- A constrained *-representation bundles:
    - A complex Hilbert space H
    - A *-algebra homomorphism π : FreeStarAlgebra n → B(H)
    - The constraint that π(gⱼ) ≥ 0 (positive operator) for each generator j -/
structure ConstrainedStarRep (n : ℕ) where
  /-- The Hilbert space -/
  H : Type*
  /-- H is a normed additive commutative group -/
  instNormedAddCommGroup : NormedAddCommGroup H
  /-- H has an inner product space structure over ℂ -/
  instInnerProductSpace : InnerProductSpace ℂ H
  /-- H is complete (Hilbert space) -/
  instCompleteSpace : CompleteSpace H
  /-- The *-algebra homomorphism to bounded operators on H -/
  toStarAlgHom : FreeStarAlgebra n →⋆ₐ[ℝ] (H →L[ℂ] H)
  /-- Each generator maps to a positive operator -/
  generator_positive : ∀ j : Fin n, (toStarAlgHom (FreeStarAlgebra.generator j)).IsPositive

attribute [instance] ConstrainedStarRep.instNormedAddCommGroup
attribute [instance] ConstrainedStarRep.instInnerProductSpace
attribute [instance] ConstrainedStarRep.instCompleteSpace

namespace ConstrainedStarRep

variable (π : ConstrainedStarRep n)

/-- Apply the representation to an algebra element. -/
noncomputable def apply (a : FreeStarAlgebra n) : π.H →L[ℂ] π.H :=
  π.toStarAlgHom a

/-- Notation: π(a) for representation application. -/
noncomputable instance :
    CoeFun (ConstrainedStarRep n) (fun π => FreeStarAlgebra n → (π.H →L[ℂ] π.H)) where
  coe π := π.apply

/-- The representation of a generator is positive. -/
theorem apply_generator_isPositive (j : Fin n) :
    (π (FreeStarAlgebra.generator j)).IsPositive :=
  π.generator_positive j

/-- The representation preserves identity. -/
@[simp]
theorem apply_one : π 1 = 1 := π.toStarAlgHom.map_one

/-- The representation preserves multiplication. -/
@[simp]
theorem apply_mul (a b : FreeStarAlgebra n) : π (a * b) = π a * π b :=
  π.toStarAlgHom.map_mul a b

/-- The representation preserves star. -/
@[simp]
theorem apply_star (a : FreeStarAlgebra n) : π (star a) = star (π a) :=
  π.toStarAlgHom.map_star' a

end ConstrainedStarRep

end ArchimedeanClosure
