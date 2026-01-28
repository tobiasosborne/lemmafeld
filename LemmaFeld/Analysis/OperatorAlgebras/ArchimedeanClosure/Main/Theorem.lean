/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Main.DualCharacterization
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Representation.GNSConstrained

/-! # Main Theorem: Archimedean Closure Characterization

This file proves the main theorem of the formalization:

  A ∈ M̄ ⟺ A ≥ 0 in all constrained *-representations

## Main results

* `main_theorem` - The main characterization theorem

## Proof Structure

The proof chains three equivalences:
1. A ∈ M̄ ⟺ φ(A) ≥ 0 for all M-positive states (dual_characterization)
2. φ(A) ≥ 0 for all states ⟹ π(A) ≥ 0 for all reps (state_nonneg_implies_rep_positive)
3. π(A) ≥ 0 for all reps ⟹ φ(A) ≥ 0 for all states (gns_constrained_implies_state_nonneg)
-/

namespace ArchimedeanClosure

variable {n : ℕ} [FreeStarAlgebra.IsArchimedean n]

/-- Main Theorem: A ∈ M̄ ⟺ A ≥ 0 in all constrained *-representations.

This characterizes positivity in constrained representations in terms of
membership in the closure of the quadratic module.

Note: We use universe level 0 for the Hilbert space to match the GNS construction. -/
theorem main_theorem {A : FreeStarAlgebra n} (hA : IsSelfAdjoint A) :
    A ∈ FreeStarAlgebra.quadraticModuleClosure ↔
    ∀ π : ConstrainedStarRep.{0} n, (π A).IsPositive := by
  constructor
  · -- Forward: A ∈ M̄ ⟹ π(A) ≥ 0 for all constrained reps
    intro hAcl
    -- A ∈ M̄ ⟹ φ(A) ≥ 0 for all states (by dual_characterization)
    have hA_states := FreeStarAlgebra.dual_characterization hA |>.mp hAcl
    -- φ(A) ≥ 0 for all states ⟹ π(A) ≥ 0 for all reps
    exact state_nonneg_implies_rep_positive A hA hA_states
  · -- Backward: π(A) ≥ 0 for all reps ⟹ A ∈ M̄
    intro hA_reps
    -- π(A) ≥ 0 for all reps ⟹ φ(A) ≥ 0 for all states (by GNS)
    have hA_states : ∀ φ : FreeStarAlgebra.MPositiveState n, 0 ≤ φ A :=
      fun φ => gns_constrained_implies_state_nonneg φ A hA hA_reps
    -- φ(A) ≥ 0 for all states ⟹ A ∈ M̄ (by dual_characterization)
    exact FreeStarAlgebra.dual_characterization hA |>.mpr hA_states

end ArchimedeanClosure
