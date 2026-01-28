/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Seminorm.Closure

/-! # Forward Direction: A ∈ M̄ ⟹ φ(A) ≥ 0

This file proves the forward direction of the dual characterization:
If A is in the closure of the quadratic module M (in the ||·||_M topology),
then φ(A) ≥ 0 for all M-positive states φ.

## Main results

* `closure_implies_nonneg` - A ∈ M̄ implies φ(A) ≥ 0 for all φ ∈ S_M

## Proof Strategy

Given A ∈ M̄ and φ ∈ S_M, for any ε > 0 there exists m ∈ M with ||A - m||_M < ε.
Since |φ(A - m)| ≤ ||A - m||_M < ε and φ(m) ≥ 0 (M-positivity), we have
φ(A) ≥ φ(m) - ε ≥ -ε. Since ε was arbitrary, φ(A) ≥ 0.
-/

namespace FreeStarAlgebra

variable {n : ℕ} [IsArchimedean n]

omit [IsArchimedean n] in
/-- φ(a - m) = φ(a) - φ(m) by linearity. -/
theorem MPositiveState.apply_sub (φ : MPositiveState n) (a m : FreeStarAlgebra n) :
    φ (a - m) = φ a - φ m := by
  change φ.toFun (a - m) = φ.toFun a - φ.toFun m
  rw [φ.toFun.map_sub]

/-- If A ∈ M̄, then φ(A) ≥ 0 for all M-positive states φ.

The proof uses the ε-δ characterization of closure: for any ε > 0, there exists
m ∈ M with ||A - m||_M < ε. Since |φ(A - m)| ≤ ||A - m||_M and φ(m) ≥ 0,
we get φ(A) > -ε for all ε > 0, hence φ(A) ≥ 0. -/
theorem closure_implies_nonneg {A : FreeStarAlgebra n}
    (hAcl : A ∈ quadraticModuleClosure) (φ : MPositiveState n) :
    0 ≤ φ A := by
  -- Prove by contradiction: assume φ(A) < 0
  by_contra h
  push_neg at h
  -- Use ε = -φ(A) > 0
  have hε : 0 < -φ A := neg_pos.mpr h
  -- Get m ∈ M with ||A - m||_M < -φ(A)
  obtain ⟨m, hm_in_M, hm_close⟩ := hAcl (-φ A) hε
  -- φ(m) ≥ 0 since m ∈ M
  have hm_nonneg : 0 ≤ φ m := φ.apply_m_nonneg hm_in_M
  -- |φ(A - m)| ≤ ||A - m||_M < -φ(A)
  have hφ_bound : |φ (A - m)| < -φ A :=
    calc |φ (A - m)| ≤ stateSeminorm (A - m) := φ.apply_abs_le_seminorm (A - m)
      _ < -φ A := hm_close
  -- From |φ(A - m)| < -φ(A), get -φ(A) < φ(A - m) and φ(A - m) < -φ(A)
  have habs : -(-φ A) < φ (A - m) ∧ φ (A - m) < -φ A := abs_lt.mp hφ_bound
  -- φ(A - m) = φ(A) - φ(m), so φ(A) - φ(m) < -φ(A)
  rw [φ.apply_sub] at habs
  -- From φ(A) - φ(m) < -φ(A): 2*φ(A) < φ(m)
  -- But φ(A) < 0 gives 2*φ(A) < 0 ≤ φ(m) -- that's consistent, not a contradiction
  -- Need the other direction: φ(A) < φ(A) - φ(m), i.e., 0 < -φ(m)
  -- From habs.1: φ(A) < φ(A) - φ(m), so φ(m) < 0
  linarith

end FreeStarAlgebra
