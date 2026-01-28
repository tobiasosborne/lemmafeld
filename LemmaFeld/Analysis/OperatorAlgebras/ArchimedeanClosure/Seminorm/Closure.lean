/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Seminorm.SeminormProps
import Mathlib.Tactic.Abel

/-! # Closure of Quadratic Module

This file defines the closure of the quadratic module M in the ||·||_M topology.

## Main definitions

* `quadraticModuleClosure` - The closure of M in the seminorm topology

## Main results

* `quadraticModule_subset_closure` - M ⊆ M̄
* `closure_add_mem` - M̄ is closed under addition
* `closure_smul_mem` - M̄ is closed under nonnegative scalar multiplication
-/

namespace FreeStarAlgebra

variable {n : ℕ} [IsArchimedean n]

/-- The closure of M in the ||·||_M seminorm topology.

An element a is in the closure iff for every ε > 0, there exists m ∈ M
with ||a - m||_M < ε.
-/
def quadraticModuleClosure : Set (FreeStarAlgebra n) :=
  {a | ∀ ε > 0, ∃ m ∈ QuadraticModule n, stateSeminorm (a - m) < ε}

section BasicMembership
/-! ### Basic membership results (use stateSeminorm_zero only) -/

omit [IsArchimedean n] in
/-- M is contained in its closure. -/
theorem quadraticModule_subset_closure :
    (QuadraticModule n : Set (FreeStarAlgebra n)) ⊆ quadraticModuleClosure := by
  intro m hm ε hε
  exact ⟨m, hm, by simp [stateSeminorm_zero, hε]⟩

omit [IsArchimedean n] in
/-- Zero is in the closure. -/
theorem zero_mem_closure : (0 : FreeStarAlgebra n) ∈ quadraticModuleClosure := by
  intro ε hε
  refine ⟨0, ?_, by simp [stateSeminorm_zero, hε]⟩
  have h : (0 : FreeStarAlgebra n) = star 0 * 0 := by simp
  rw [h]
  exact star_mul_self_mem 0

end BasicMembership

section ClosureProperties
/-! ### Closure is a cone -/

/-- The closure is closed under addition. -/
theorem closure_add_mem {a b : FreeStarAlgebra n}
    (ha : a ∈ quadraticModuleClosure) (hb : b ∈ quadraticModuleClosure) :
    a + b ∈ quadraticModuleClosure := by
  intro ε hε
  obtain ⟨ma, hma, ha'⟩ := ha (ε / 2) (by linarith)
  obtain ⟨mb, hmb, hb'⟩ := hb (ε / 2) (by linarith)
  refine ⟨ma + mb, QuadraticModule.add_mem hma hmb, ?_⟩
  calc stateSeminorm (a + b - (ma + mb))
      = stateSeminorm ((a - ma) + (b - mb)) := by congr 1; abel
    _ ≤ stateSeminorm (a - ma) + stateSeminorm (b - mb) := stateSeminorm_add _ _
    _ < ε / 2 + ε / 2 := add_lt_add ha' hb'
    _ = ε := by ring

omit [IsArchimedean n] in
/-- The closure is closed under nonnegative scalar multiplication. -/
theorem closure_smul_mem {c : ℝ} (hc : 0 ≤ c) {a : FreeStarAlgebra n}
    (ha : a ∈ quadraticModuleClosure) :
    c • a ∈ quadraticModuleClosure := by
  intro ε hε
  by_cases hc0 : c = 0
  · simp only [hc0, zero_smul]
    exact ⟨0, by simpa using star_mul_self_mem 0, by simp [stateSeminorm_zero, hε]⟩
  · have hcpos : 0 < c := lt_of_le_of_ne hc (ne_comm.mpr hc0)
    obtain ⟨m, hm, hma⟩ := ha (ε / c) (div_pos hε hcpos)
    refine ⟨c • m, QuadraticModule.smul_mem hc hm, ?_⟩
    calc stateSeminorm (c • a - c • m)
        = stateSeminorm (c • (a - m)) := by rw [smul_sub]
      _ = |c| * stateSeminorm (a - m) := stateSeminorm_smul c (a - m)
      _ = c * stateSeminorm (a - m) := by rw [abs_of_nonneg hc]
      _ < c * (ε / c) := by exact mul_lt_mul_of_pos_left hma hcpos
      _ = ε := mul_div_cancel₀ ε (ne_of_gt hcpos)

end ClosureProperties

end FreeStarAlgebra
