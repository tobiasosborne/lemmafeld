/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.State.MPositiveState
import Mathlib.Topology.Constructions
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Algebra.Ring.Real

/-! # Closedness of State Conditions

This file proves that the conditions defining M-positive states are closed
in the product topology on `FreeStarAlgebra n → ℝ`.

## Main results

* `isClosed_additivity` - Additive functions form a closed set
* `isClosed_homogeneity` - ℝ-homogeneous functions form a closed set
* `isClosed_star_symmetry` - Star-symmetric functions form a closed set
* `isClosed_m_nonneg` - M-nonnegative functions form a closed set
* `isClosed_normalized` - Functions with f(1)=1 form a closed set

## Proof Strategy

Each condition is expressed as a preimage of a closed set under a continuous map.
In the product topology, evaluation at a point is continuous, so:
- Equalities like f(a+b) = f(a) + f(b) are preimages of {0} under continuous maps
- Inequalities like f(m) ≥ 0 are preimages of [0,∞) under continuous evaluation

See LEARNINGS_misc.md for details on this approach.
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ}

open Topology

/-- Evaluation at a point is continuous in the product topology. -/
theorem continuous_eval (a : FreeStarAlgebra n) :
    Continuous (fun f : FreeStarAlgebra n → ℝ => f a) :=
  continuous_apply a

/-- The set of functions satisfying f(a+b) = f(a) + f(b) for fixed a,b is closed. -/
theorem isClosed_add_eq (a b : FreeStarAlgebra n) :
    IsClosed {f : FreeStarAlgebra n → ℝ | f (a + b) = f a + f b} := by
  have h : {f : FreeStarAlgebra n → ℝ | f (a + b) = f a + f b} =
      (fun f => f (a + b) - (f a + f b)) ⁻¹' {0} := by
    ext f; simp [Set.mem_preimage, sub_eq_zero]
  rw [h]
  apply IsClosed.preimage
  · exact continuous_eval (a + b) |>.sub (continuous_eval a |>.add (continuous_eval b))
  · exact isClosed_singleton

/-- The set of additive functions is closed (intersection over all pairs). -/
theorem isClosed_additivity :
    IsClosed {f : FreeStarAlgebra n → ℝ | ∀ a b, f (a + b) = f a + f b} := by
  have h : {f : FreeStarAlgebra n → ℝ | ∀ a b, f (a + b) = f a + f b} =
      ⋂ a, ⋂ b, {f | f (a + b) = f a + f b} := by
    ext f; simp
  rw [h]
  apply isClosed_iInter; intro a
  apply isClosed_iInter; intro b
  exact isClosed_add_eq a b

/-- The set of functions satisfying f(c•a) = c * f(a) for fixed c,a is closed. -/
theorem isClosed_smul_eq (c : ℝ) (a : FreeStarAlgebra n) :
    IsClosed {f : FreeStarAlgebra n → ℝ | f (c • a) = c * f a} := by
  have h : {f : FreeStarAlgebra n → ℝ | f (c • a) = c * f a} =
      (fun f => f (c • a) - c * f a) ⁻¹' {0} := by
    ext f; simp [Set.mem_preimage, sub_eq_zero]
  rw [h]
  apply IsClosed.preimage
  · exact continuous_eval (c • a) |>.sub (continuous_const.mul (continuous_eval a))
  · exact isClosed_singleton

/-- The set of ℝ-homogeneous functions is closed. -/
theorem isClosed_homogeneity :
    IsClosed {f : FreeStarAlgebra n → ℝ | ∀ c a, f (c • a) = c * f a} := by
  have h : {f : FreeStarAlgebra n → ℝ | ∀ c a, f (c • a) = c * f a} =
      ⋂ c, ⋂ a, {f | f (c • a) = c * f a} := by
    ext f; simp
  rw [h]
  apply isClosed_iInter; intro c
  apply isClosed_iInter; intro a
  exact isClosed_smul_eq c a

/-- The set of star-symmetric functions is closed. -/
theorem isClosed_star_symmetry :
    IsClosed {f : FreeStarAlgebra n → ℝ | ∀ a, f (star a) = f a} := by
  have h : {f : FreeStarAlgebra n → ℝ | ∀ a, f (star a) = f a} =
      ⋂ a, {f | f (star a) = f a} := by
    ext f; simp
  rw [h]
  apply isClosed_iInter; intro a
  have h2 : {f : FreeStarAlgebra n → ℝ | f (star a) = f a} =
      (fun f => f (star a) - f a) ⁻¹' {0} := by
    ext f; simp [Set.mem_preimage, sub_eq_zero]
  rw [h2]
  apply IsClosed.preimage
  · exact continuous_eval (star a) |>.sub (continuous_eval a)
  · exact isClosed_singleton

/-- The set of functions with f(m) ≥ 0 for fixed m is closed. -/
theorem isClosed_nonneg_at (m : FreeStarAlgebra n) :
    IsClosed {f : FreeStarAlgebra n → ℝ | 0 ≤ f m} := by
  have h : {f : FreeStarAlgebra n → ℝ | 0 ≤ f m} = (fun f => f m) ⁻¹' Set.Ici 0 := by
    ext f; simp [Set.mem_preimage, Set.mem_Ici]
  rw [h]
  apply IsClosed.preimage (continuous_eval m)
  exact isClosed_Ici

/-- The set of M-nonnegative functions is closed. -/
theorem isClosed_m_nonneg :
    IsClosed {f : FreeStarAlgebra n → ℝ | ∀ m ∈ QuadraticModule n, 0 ≤ f m} := by
  have h : {f : FreeStarAlgebra n → ℝ | ∀ m ∈ QuadraticModule n, 0 ≤ f m} =
      ⋂ m ∈ QuadraticModule n, {f | 0 ≤ f m} := by
    ext f; simp
  rw [h]
  apply isClosed_biInter
  intro m _
  exact isClosed_nonneg_at m

/-- The set of normalized functions (f(1) = 1) is closed. -/
theorem isClosed_normalized :
    IsClosed {f : FreeStarAlgebra n → ℝ | f 1 = 1} := by
  have h : {f : FreeStarAlgebra n → ℝ | f 1 = 1} = (fun f => f 1) ⁻¹' {1} := by
    ext f; simp [Set.mem_preimage]
  rw [h]
  apply IsClosed.preimage (continuous_eval 1)
  exact isClosed_singleton

end MPositiveState

end FreeStarAlgebra
