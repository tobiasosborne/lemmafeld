/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Dual.Forward
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Dual.Normalization

/-! # Dual Characterization Theorem

This file proves the dual characterization of the quadratic module closure:

  A ∈ M̄ ⟺ φ(A) ≥ 0 for all M-positive states φ

## Main results

* `dual_characterization` - The iff characterization (Theorem 5.1)

## Proof

Forward direction: `closure_implies_nonneg` from Dual/Forward.lean
Backward direction: Contrapositive of `exists_MPositiveState_negative` from Dual/Normalization.lean
-/

namespace FreeStarAlgebra

variable {n : ℕ} [IsArchimedean n]

/-- Dual characterization: A ∈ M̄ ⟺ φ(A) ≥ 0 for all M-positive states φ.

This is Theorem 5.1 in the formalization. -/
theorem dual_characterization {A : FreeStarAlgebra n} (hA : IsSelfAdjoint A) :
    A ∈ quadraticModuleClosure ↔ ∀ φ : MPositiveState n, 0 ≤ φ A := by
  constructor
  · -- Forward: A ∈ M̄ ⟹ φ(A) ≥ 0
    exact fun hAcl φ => closure_implies_nonneg hAcl φ
  · -- Backward: (∀ φ, φ(A) ≥ 0) ⟹ A ∈ M̄
    -- Contrapositive: A ∉ M̄ ⟹ ∃ φ, φ(A) < 0
    intro hA_nonneg
    by_contra hA_not
    obtain ⟨φ, hφ_neg⟩ := exists_MPositiveState_negative hA hA_not
    have := hA_nonneg φ
    linarith

end FreeStarAlgebra
