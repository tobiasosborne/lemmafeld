/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Algebra.QuadraticModule
import Mathlib.Algebra.Module.LinearMap.Basic

/-! # M-Positive States

This file defines M-positive states on the free *-algebra over ℝ.

## Main definitions

* `MPositiveState n` - A state φ with φ(1)=1, φ(star a)=φ(a), and φ(m)≥0 for m∈M
* `MPositiveStateSet n` - The set S_M of all M-positive states

## Mathematical Background

An M-positive state is an ℝ-linear functional φ : A₀ → ℝ satisfying:
1. φ(star a) = φ(a) (symmetry - automatically real-valued on self-adjoints)
2. φ(1) = 1 (normalization)
3. φ(m) ≥ 0 for all m ∈ M (M-positivity)

Since the codomain is ℝ, positivity condition needs no separate "real part" check.

## Implementation Notes

Since FreeStarAlgebra is an ℝ-algebra, we use ℝ-linear maps to ℝ. The `map_star`
condition ensures the functional is symmetric (φ(star a) = φ(a)), which means it
takes real values on self-adjoint elements and is determined by its values there.

See LEARNINGS.md for why this design was chosen over ℂ-linear functionals.
-/

namespace FreeStarAlgebra

variable {n : ℕ}

/-- An M-positive state: ℝ-linear functional with symmetry, φ(1)=1, and φ(m)≥0 for m∈M.

The key properties are:
- Symmetry: φ(star a) = φ(a) (determines values on all elements from self-adjoints)
- Normalization: φ(1) = 1
- M-positivity: φ(m) ≥ 0 for m ∈ M
-/
structure MPositiveState (n : ℕ) where
  /-- The underlying ℝ-linear functional. -/
  toFun : FreeStarAlgebra n →ₗ[ℝ] ℝ
  /-- The functional is symmetric: φ(star a) = φ(a). -/
  map_star : ∀ a, toFun (star a) = toFun a
  /-- The state maps 1 to 1. -/
  map_one : toFun 1 = 1
  /-- Elements of M map to nonnegative values. -/
  map_m_nonneg : ∀ m ∈ QuadraticModule n, 0 ≤ toFun m

namespace MPositiveState

/-- Coercion from MPositiveState to function type. -/
instance : FunLike (MPositiveState n) (FreeStarAlgebra n) ℝ where
  coe φ := φ.toFun
  coe_injective' := by
    intro φ ψ h
    cases φ; cases ψ
    simp only [mk.injEq]
    ext x
    exact congrFun h x

variable (φ : MPositiveState n)

/-- The state maps 1 to 1. -/
@[simp]
theorem apply_one : φ 1 = 1 := φ.map_one

/-- The state is symmetric. -/
theorem apply_star (a : FreeStarAlgebra n) : φ (star a) = φ a := φ.map_star a

/-- Elements of M have nonnegative value under φ. -/
theorem apply_m_nonneg {m : FreeStarAlgebra n} (hm : m ∈ QuadraticModule n) :
    0 ≤ φ m := φ.map_m_nonneg m hm

/-- φ(star a * a) ≥ 0 since star a * a ∈ M. -/
theorem apply_star_mul_self_nonneg (a : FreeStarAlgebra n) :
    0 ≤ φ (star a * a) :=
  φ.apply_m_nonneg (star_mul_self_mem a)

/-- Linearity: φ(a + b) = φ(a) + φ(b). -/
theorem map_add (a b : FreeStarAlgebra n) :
    φ (a + b) = φ a + φ b := φ.toFun.map_add a b

/-- Linearity: φ(c • a) = c * φ(a) for c : ℝ. -/
theorem map_smul (c : ℝ) (a : FreeStarAlgebra n) :
    φ (c • a) = c * φ a := φ.toFun.map_smul c a

end MPositiveState

/-- The set S_M of all M-positive states. -/
def MPositiveStateSet (n : ℕ) : Set (MPositiveState n) := Set.univ

end FreeStarAlgebra
