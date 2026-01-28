/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Dual.SpanIntersection
import Mathlib.LinearAlgebra.LinearPMap

/-! # Constructing the Separating Functional on span{A}

This file constructs a linear functional ψ₀ on span{A} that separates A from M.
When A ∉ M̄, we define ψ₀(λA) = -λ, achieving ψ₀(A) = -1 < 0 while ψ₀ ≥ 0 on M ∩ span{A}.

## Main definitions

* `separatingOnSpan` - The linear map ψ₀ : span{A} →ₗ[ℝ] ℝ with ψ₀(A) = -1

## Main results

* `not_in_closure_ne_zero` - A ∉ M̄ implies A ≠ 0
* `separatingOnSpan_apply_A` - ψ₀(A) = -1 < 0
* `separatingOnSpan_nonneg_on_M_cap_span` - ψ₀ ≥ 0 on M ∩ span{A}

## Proof Strategy

Since 0 ∈ M ⊆ M̄, if A ∉ M̄ then A ≠ 0. This allows us to use `LinearPMap.mkSpanSingleton`
to define a linear map on span{A} sending A ↦ -1. By `separating_nonneg_on_span_cap_M`,
this functional is nonneg on M ∩ span{A}.
-/

namespace FreeStarAlgebra

variable {n : ℕ} [IsArchimedean n]

/-! ### A ∉ closure implies A ≠ 0 -/

omit [IsArchimedean n] in
/-- If A ∉ M̄, then A ≠ 0.

Proof: 0 = star 0 * 0 ∈ M ⊆ M̄, so if A ∉ M̄ then A ≠ 0. -/
theorem not_in_closure_ne_zero {A : FreeStarAlgebra n}
    (hA_not : A ∉ quadraticModuleClosure) : A ≠ 0 := by
  intro hA_zero
  rw [hA_zero] at hA_not
  exact hA_not zero_mem_closure

/-! ### The separating functional -/

/-- The separating functional ψ₀ on span{A}, defined by ψ₀(λA) = -λ.

When A ∉ M̄, this functional satisfies:
- ψ₀(A) = -1 < 0
- ψ₀ ≥ 0 on M ∩ span{A} (since positive multiples of A cannot be in M)

We use `LinearPMap.mkSpanSingleton` which requires A ≠ 0 (guaranteed by A ∉ M̄). -/
noncomputable def separatingOnSpan {A : FreeStarAlgebra n}
    (hA_not : A ∉ quadraticModuleClosure) :
    Submodule.span ℝ {A} →ₗ[ℝ] ℝ :=
  (LinearPMap.mkSpanSingleton (K := ℝ) A (-1 : ℝ) (not_in_closure_ne_zero hA_not)).toFun

omit [IsArchimedean n] in
/-- ψ₀(A) = -1. -/
theorem separatingOnSpan_apply_A {A : FreeStarAlgebra n}
    (hA_not : A ∉ quadraticModuleClosure) :
    separatingOnSpan hA_not ⟨A, Submodule.mem_span_singleton_self A⟩ = -1 := by
  unfold separatingOnSpan
  exact LinearPMap.mkSpanSingleton_apply ℝ (not_in_closure_ne_zero hA_not) (-1)

omit [IsArchimedean n] in
/-- ψ₀(A) < 0. -/
theorem separatingOnSpan_apply_A_neg {A : FreeStarAlgebra n}
    (hA_not : A ∉ quadraticModuleClosure) :
    separatingOnSpan hA_not ⟨A, Submodule.mem_span_singleton_self A⟩ < 0 := by
  rw [separatingOnSpan_apply_A]
  norm_num

/-! ### Nonnegativity on M ∩ span{A} -/

omit [IsArchimedean n] in
/-- ψ₀(c • A) = c * (-1) = -c. -/
theorem separatingOnSpan_apply_smul {A : FreeStarAlgebra n}
    (hA_not : A ∉ quadraticModuleClosure) (c : ℝ) :
    separatingOnSpan hA_not ⟨c • A, Submodule.mem_span_singleton.mpr ⟨c, rfl⟩⟩ = -c := by
  -- ⟨c • A, _⟩ = c • ⟨A, _⟩ in the submodule
  have h : (⟨c • A, Submodule.mem_span_singleton.mpr ⟨c, rfl⟩⟩ : Submodule.span ℝ {A}) =
           c • ⟨A, Submodule.mem_span_singleton_self A⟩ := rfl
  rw [h, LinearMap.map_smul, separatingOnSpan_apply_A]
  simp only [smul_eq_mul, mul_neg, mul_one]

omit [IsArchimedean n] in
/-- ψ₀ ≥ 0 on M ∩ span{A}.

For x ∈ M ∩ span{A}, we have x = c • A for some c, and ψ₀(x) = -c.
By `separating_nonneg_on_span_cap_M`, if c • A ∈ M then c ≤ 0, hence -c ≥ 0. -/
theorem separatingOnSpan_nonneg_on_M_cap_span {A : FreeStarAlgebra n}
    (hA_not : A ∉ quadraticModuleClosure)
    {x : FreeStarAlgebra n} (hx_in_M : x ∈ QuadraticModule n)
    (hx_in_span : x ∈ Submodule.span ℝ {A}) :
    0 ≤ separatingOnSpan hA_not ⟨x, hx_in_span⟩ := by
  -- Get the coefficient c with x = c • A
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hx_in_span
  -- Rewrite using the smul formula
  have h_eq : (⟨x, hx_in_span⟩ : Submodule.span ℝ {A}) =
              ⟨c • A, Submodule.mem_span_singleton.mpr ⟨c, rfl⟩⟩ := by
    simp only [Subtype.mk.injEq]
    exact hc.symm
  rw [h_eq, separatingOnSpan_apply_smul]
  -- -c ≥ 0 follows from c ≤ 0, which follows from c • A ∈ M and A ∉ M̄
  have hc_nonpos : c ≤ 0 := by
    rw [← hc] at hx_in_M
    exact span_cap_M_nonpos_coeff hA_not hx_in_M
  linarith

end FreeStarAlgebra
