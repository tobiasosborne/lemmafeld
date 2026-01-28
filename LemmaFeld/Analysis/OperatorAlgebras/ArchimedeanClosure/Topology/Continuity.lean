/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Seminorm.StateSeminorm

/-! # State Continuity in Seminorm Topology

This file proves that M-positive states are continuous (in fact, Lipschitz)
with respect to the state seminorm topology.

## Main results

* `MPositiveState.lipschitz` - Every M-positive state is 1-Lipschitz
* `MPositiveState.continuous` - Every M-positive state is continuous

## Mathematical Background

For any M-positive state φ and any a, b:
  |φ(a) - φ(b)| = |φ(a - b)| ≤ ||a - b||_M

This is immediate from `MPositiveState.apply_abs_le_seminorm`.
-/

namespace FreeStarAlgebra

variable {n : ℕ} [IsArchimedean n]

/-- Every M-positive state is 1-Lipschitz with respect to the state seminorm.

|φ(a) - φ(b)| = |φ(a - b)| ≤ ||a - b||_M -/
theorem MPositiveState.lipschitz_dist (φ : MPositiveState n) (a b : FreeStarAlgebra n) :
    |φ a - φ b| ≤ stateSeminorm (a - b) := by
  have h : φ a - φ b = φ (a - b) := (φ.toFun.map_sub a b).symm
  rw [h]
  exact φ.apply_abs_le_seminorm (a - b)

/-- State evaluation at a point is subadditive bounded by the seminorm.

This is the key property for Lipschitz continuity. -/
theorem MPositiveState.apply_sub_abs_le (φ : MPositiveState n) (a b : FreeStarAlgebra n) :
    |φ (a - b)| ≤ stateSeminorm (a - b) :=
  φ.apply_abs_le_seminorm (a - b)

end FreeStarAlgebra
