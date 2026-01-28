/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Topology.SeminormTopology
import Mathlib.Analysis.Convex.Cone.Dual

/-! # Separating Functional via Geometric Hahn-Banach

This file constructs a separating functional for the dual characterization theorem.

## Main results

* `riesz_extension_exists` - For A ∉ M̄, there exists ψ : A₀ → ℝ with ψ ≥ 0 on M and ψ(A) < 0

## Mathematical Background

We use `ProperCone.hyperplane_separation_point` from mathlib, which is a consequence of
the geometric Hahn-Banach separation theorem for locally convex spaces.

### Key Steps

1. **Topology**: FreeStarAlgebra gets a topology from the state seminorm ||·||_M
2. **LocallyConvexSpace**: Seminorm topologies are always locally convex
3. **ProperCone**: M̄ (closure of quadratic module) forms a proper cone:
   - Nonempty (0 ∈ M̄)
   - Closed (by definition of closure)
   - Cone (closed under + and ℝ≥0 scaling)
4. **Separation**: For A ∉ M̄, there exists continuous f with f ≥ 0 on M̄ and f(A) < 0

This avoids the "generating condition" difficulties of the Riesz extension theorem.

## References

* Schmüdgen, "The Moment Problem" (2017), Chapter 3
* Rudin, "Functional Analysis" (1991), Chapter 3 (Hahn-Banach separation)
-/

namespace FreeStarAlgebra

variable {n : ℕ} [IsArchimedean n]

/-! ### ProperCone from Quadratic Module Closure -/

section WithTopology
/-! Setup the seminorm topology and locally convex structure. -/

attribute [local instance] seminormTopology
attribute [local instance] locallyConvexSpace_seminormTopology

/-- The closure M̄ as a ProperCone.

A ProperCone is a nonempty, closed, convex cone. M̄ satisfies:
- Nonempty: 0 ∈ M̄ (from `zero_mem_closure`)
- Closed: by `isClosed_quadraticModuleClosure`
- Cone: closed under + and ℝ≥0 scaling (from `closure_add_mem`, `closure_smul_mem`) -/
noncomputable def quadraticModuleClosureProperCone : ProperCone ℝ (FreeStarAlgebra n) :=
  ⟨{
    toAddSubmonoid := {
      carrier := quadraticModuleClosure
      add_mem' := fun ha hb => closure_add_mem ha hb
      zero_mem' := zero_mem_closure
    }
    smul_mem' := fun c _ ha => closure_smul_mem c.property ha
  }, isClosed_quadraticModuleClosure⟩

/-- Membership in the ProperCone is equivalent to membership in the closure. -/
theorem mem_quadraticModuleClosureProperCone (a : FreeStarAlgebra n) :
    a ∈ quadraticModuleClosureProperCone ↔ a ∈ quadraticModuleClosure := Iff.rfl

/-! ### Main Separation Theorem -/

/-- **Main Theorem**: For A ∉ M̄, there exists a linear functional ψ with
ψ ≥ 0 on M and ψ(A) < 0.

This is the core result for the backward direction of the dual characterization.
The proof uses geometric Hahn-Banach separation: since M̄ is a proper cone in
a locally convex space and A ∉ M̄, there exists a separating hyperplane. -/
theorem riesz_extension_exists {A : FreeStarAlgebra n}
    (_hA : IsSelfAdjoint A) (hA_not : A ∉ quadraticModuleClosure) :
    ∃ ψ : FreeStarAlgebra n →ₗ[ℝ] ℝ,
      (∀ m ∈ QuadraticModule n, 0 ≤ ψ m) ∧ ψ A < 0 := by
  -- Apply ProperCone.hyperplane_separation_point
  obtain ⟨f, hf_nonneg_closure, hf_neg⟩ :=
    ProperCone.hyperplane_separation_point quadraticModuleClosureProperCone hA_not
  -- Convert continuous linear map to linear map
  use f.toLinearMap
  constructor
  · -- ψ ≥ 0 on M follows from M ⊆ M̄ and ψ ≥ 0 on M̄
    intro m hm
    exact hf_nonneg_closure m (quadraticModule_subset_closure hm)
  · -- ψ(A) < 0 is immediate
    exact hf_neg

end WithTopology

end FreeStarAlgebra
