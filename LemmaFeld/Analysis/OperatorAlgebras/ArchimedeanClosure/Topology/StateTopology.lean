/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.State.MPositiveState
import Mathlib.Topology.Algebra.Module.WeakDual
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Topology on State Space

This file defines the weak-* topology (pointwise convergence) on M-positive states.

## Main definitions

* `MPositiveState.instTopologicalSpace` - Pointwise convergence topology on S_M

## Main results

* `MPositiveState.eval_continuous` - Evaluation at any element is continuous

## Mathematical Background

The topology on S_M is the subspace topology inherited from the weak-* topology
on the dual space. Concretely, a net φᵢ → φ iff φᵢ(a) → φ(a) for all a ∈ A₀.
-/

namespace FreeStarAlgebra

variable {n : ℕ}

namespace MPositiveState

/-- The pointwise convergence topology on M-positive states.

This is the coarsest topology making all evaluation maps continuous.
Equivalently, φᵢ → φ iff φᵢ(a) → φ(a) for all a. -/
instance instTopologicalSpace : TopologicalSpace (MPositiveState n) :=
  TopologicalSpace.induced
    (fun φ => fun a => φ a)
    Pi.topologicalSpace

/-- Evaluation at a fixed element is continuous. -/
theorem eval_continuous (a : FreeStarAlgebra n) :
    Continuous (fun φ : MPositiveState n => φ a) := by
  apply Continuous.comp (continuous_apply a) continuous_induced_dom

end MPositiveState

end FreeStarAlgebra
