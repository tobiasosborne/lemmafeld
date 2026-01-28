/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Dual.Forward

/-! # Span Intersection Lemma

This file proves that if A ∉ M̄, then positive scalar multiples of A are not in M.
This is the key result needed for constructing the separating functional in the
Riesz extension argument.

## Main results

* `positive_smul_not_in_M` - If A ∉ M̄ and c > 0, then c • A ∉ M
* `separating_nonneg_on_span_cap_M` - A separating functional ψ₀(λA) = -λε
  is automatically nonneg on M ∩ span{A}

## Proof Strategy

For c > 0: If c • A ∈ M, then A = (1/c) • (c • A) ∈ M by the cone property,
so A ∈ M ⊆ M̄, contradicting A ∉ M̄.

For the separating functional:
- λ > 0 case: excluded by positive_smul_not_in_M
- λ ≤ 0 case: ψ₀(λA) = -λε ≥ 0 automatically
-/

namespace FreeStarAlgebra

variable {n : ℕ} [IsArchimedean n]

/-! ### Positive scalar multiples -/

omit [IsArchimedean n] in
/-- If A ∉ M̄ and c > 0, then c • A ∉ M.

Proof: If c • A ∈ M, then A = (1/c) • (c • A) ∈ M by cone property (since 1/c > 0),
hence A ∈ M ⊆ M̄, contradicting A ∉ M̄. -/
theorem positive_smul_not_in_M {A : FreeStarAlgebra n}
    (hA_not : A ∉ quadraticModuleClosure) {c : ℝ} (hc : 0 < c) :
    c • A ∉ QuadraticModule n := by
  intro h_cA_in_M
  -- If c • A ∈ M, then A = (1/c) • (c • A) ∈ M
  have h_inv_pos : 0 ≤ c⁻¹ := le_of_lt (inv_pos.mpr hc)
  have h_A_in_M : A ∈ QuadraticModule n := by
    have h_eq : A = c⁻¹ • (c • A) := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hc), one_smul]
    rw [h_eq]
    exact QuadraticModule.smul_mem h_inv_pos h_cA_in_M
  -- A ∈ M ⊆ M̄, contradiction
  exact hA_not (quadraticModule_subset_closure h_A_in_M)

omit [IsArchimedean n] in
/-- Corollary: A itself is not in M if A ∉ M̄. -/
theorem self_not_in_M {A : FreeStarAlgebra n}
    (hA_not : A ∉ quadraticModuleClosure) :
    A ∉ QuadraticModule n := by
  have h := positive_smul_not_in_M hA_not (by linarith : (0 : ℝ) < 1)
  simp only [one_smul] at h
  exact h

/-! ### Separating functional nonnegativity -/

omit [IsArchimedean n] in
/-- For A ∉ M̄ and ε > 0, the functional ψ₀(λA) = -λε is nonneg on M ∩ span{A}.

This is the key property needed for Riesz extension. Elements of M ∩ span{A}
have the form λA for some λ ∈ ℝ. We show:
- λ > 0 is impossible (by positive_smul_not_in_M)
- λ ≤ 0 gives ψ₀(λA) = -λε ≥ 0
-/
theorem separating_nonneg_on_span_cap_M {A : FreeStarAlgebra n}
    (hA_not : A ∉ quadraticModuleClosure) {ε : ℝ} (hε : 0 < ε)
    {x : FreeStarAlgebra n} (hx_in_M : x ∈ QuadraticModule n)
    {coeff : ℝ} (hx_eq : x = coeff • A) :
    0 ≤ -coeff * ε := by
  -- Case split on sign of coeff
  by_cases hcoeff_pos : 0 < coeff
  · -- coeff > 0: contradiction, since coeff • A ∉ M
    exfalso
    rw [hx_eq] at hx_in_M
    exact positive_smul_not_in_M hA_not hcoeff_pos hx_in_M
  · -- coeff ≤ 0: -coeff ≥ 0, so -coeff * ε ≥ 0
    push_neg at hcoeff_pos
    have h_neg_nonneg : 0 ≤ -coeff := neg_nonneg.mpr hcoeff_pos
    exact mul_nonneg h_neg_nonneg (le_of_lt hε)

/-! ### Characterization of M ∩ span{A} -/

omit [IsArchimedean n] in
/-- Elements of M ∩ span{A} when A ∉ M̄ must have non-positive coefficient.

This partially characterizes M ∩ span{A}: it cannot contain λA for λ > 0. -/
theorem span_cap_M_nonpos_coeff {A : FreeStarAlgebra n}
    (hA_not : A ∉ quadraticModuleClosure)
    {coeff : ℝ} (hcoeff_smul_in_M : coeff • A ∈ QuadraticModule n) :
    coeff ≤ 0 := by
  by_contra h
  push_neg at h
  exact positive_smul_not_in_M hA_not h hcoeff_smul_in_M

end FreeStarAlgebra
