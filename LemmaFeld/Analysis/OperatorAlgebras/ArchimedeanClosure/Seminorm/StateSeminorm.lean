/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.State.MPositiveState
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.State.NonEmptiness
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Boundedness.ArchimedeanBound
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Group

/-! # The State Seminorm ||·||_M

This file defines the state seminorm on the free *-algebra:
  ||a||_M = sup{|φ(a)| : φ ∈ S_M}

## Main definitions

* `stateSeminorm` - The state seminorm ||a||_M = sup{|φ(a)| : φ ∈ S_M}

## Main results

* `stateSeminorm_le` - ||a||_M ≤ √Nₐ (bounded by Archimedean bound)
* `stateSeminorm_nonneg` - 0 ≤ ||a||_M
* `stateSeminorm_add` - ||a + b||_M ≤ ||a||_M + ||b||_M (triangle inequality)

## Mathematical Background

The Archimedean property ensures that |φ(a)| ≤ √Nₐ for all φ ∈ S_M,
so the supremum is finite. The nonemptiness of S_M ensures the supremum
is well-defined.
-/

namespace FreeStarAlgebra

variable {n : ℕ} [IsArchimedean n]

/-- S_M is nonempty (scalarState witnesses this). -/
instance MPositiveState.instNonempty : Nonempty (MPositiveState n) := ⟨scalarState⟩

/-- The set of absolute values {|φ(a)| : φ ∈ S_M} is bounded above by √Nₐ. -/
theorem bddAbove_abs_range (a : FreeStarAlgebra n) :
    BddAbove (Set.range fun φ : MPositiveState n => |φ a|) := by
  use Real.sqrt (archimedeanBound a)
  intro x hx
  obtain ⟨φ, rfl⟩ := hx
  exact φ.apply_abs_le a

/-- The state seminorm: ||a||_M = sup{|φ(a)| : φ ∈ S_M}. -/
noncomputable def stateSeminorm (a : FreeStarAlgebra n) : ℝ :=
  ⨆ φ : MPositiveState n, |φ a|

/-- The state seminorm is bounded above by √Nₐ. -/
theorem stateSeminorm_le (a : FreeStarAlgebra n) :
    stateSeminorm a ≤ Real.sqrt (archimedeanBound a) := by
  apply ciSup_le
  intro φ
  exact φ.apply_abs_le a

/-- The state seminorm is nonnegative. -/
theorem stateSeminorm_nonneg (a : FreeStarAlgebra n) : 0 ≤ stateSeminorm a := by
  have φ₀ : MPositiveState n := scalarState
  calc 0 ≤ |φ₀ a| := abs_nonneg _
    _ ≤ stateSeminorm a := le_ciSup (bddAbove_abs_range a) φ₀

/-- Every state value is bounded by the seminorm. -/
theorem MPositiveState.apply_abs_le_seminorm (φ : MPositiveState n) (a : FreeStarAlgebra n) :
    |φ a| ≤ stateSeminorm a :=
  le_ciSup (bddAbove_abs_range a) φ

/-- Triangle inequality: ||a + b||_M ≤ ||a||_M + ||b||_M. -/
theorem stateSeminorm_add (a b : FreeStarAlgebra n) :
    stateSeminorm (a + b) ≤ stateSeminorm a + stateSeminorm b := by
  unfold stateSeminorm
  have hbdd : BddAbove (Set.range fun φ : MPositiveState n => |φ a| + |φ b|) := by
    use Real.sqrt (archimedeanBound a) + Real.sqrt (archimedeanBound b)
    intro x hx
    obtain ⟨φ, rfl⟩ := hx
    exact add_le_add (φ.apply_abs_le a) (φ.apply_abs_le b)
  calc ⨆ φ : MPositiveState n, |φ (a + b)|
      ≤ ⨆ φ : MPositiveState n, (|φ a| + |φ b|) := by
        apply ciSup_mono hbdd
        intro φ
        simp only [φ.map_add]
        exact abs_add_le (φ a) (φ b)
    _ ≤ (⨆ φ : MPositiveState n, |φ a|) + (⨆ φ : MPositiveState n, |φ b|) :=
        ciSup_add_le_ciSup_add_ciSup (bddAbove_abs_range a) (bddAbove_abs_range b)

end FreeStarAlgebra
