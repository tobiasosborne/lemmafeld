/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Seminorm.Closure
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Closure

/-! # Seminorm Topology on FreeStarAlgebra

This file defines the topology on FreeStarAlgebra induced by the state seminorm,
and shows it is locally convex.

## Main definitions

* `stateSeminormFamily` - The state seminorm as a SeminormFamily (indexed by Unit)
* `seminormTopology` - TopologicalSpace induced by state seminorm

## Main results

* `withSeminorms_stateSeminormFamily` - The topology satisfies WithSeminorms
* `locallyConvexSpace_seminormTopology` - The topology is locally convex
* `quadraticModuleClosure_eq_closure` - ε-δ closure equals topological closure
* `isClosed_quadraticModuleClosure` - The closure M̄ is closed

## Purpose

This infrastructure enables using `ProperCone.hyperplane_separation_point` for
the Riesz extension theorem in AC-P6.4.
-/

namespace FreeStarAlgebra

variable {n : ℕ} [IsArchimedean n]

/-- The state seminorm as a SeminormFamily indexed by Unit. -/
noncomputable def stateSeminormFamily : SeminormFamily ℝ (FreeStarAlgebra n) Unit :=
  fun _ => stateSeminormSeminorm

/-- The topology induced by the state seminorm family. -/
noncomputable def seminormTopology : TopologicalSpace (FreeStarAlgebra n) :=
  stateSeminormFamily.moduleFilterBasis.topology

section WithTopology
/-! ### Results requiring the seminorm topology -/

attribute [local instance] seminormTopology

/-- The topology is exactly the seminorm family topology. -/
theorem withSeminorms_stateSeminormFamily :
    WithSeminorms (stateSeminormFamily (n := n)) :=
  WithSeminorms.mk rfl

/-- The seminorm topology makes FreeStarAlgebra locally convex. -/
theorem locallyConvexSpace_seminormTopology : LocallyConvexSpace ℝ (FreeStarAlgebra n) :=
  WithSeminorms.toLocallyConvexSpace withSeminorms_stateSeminormFamily

/-- For Unit-indexed family, s.sup = the single seminorm (for nonempty s). -/
lemma finset_sup_unit_eq (s : Finset Unit) (hs : s.Nonempty) :
    s.sup (stateSeminormFamily (n := n)) = stateSeminormSeminorm := by
  have h : s = {()} := Finset.eq_singleton_iff_nonempty_unique_mem.mpr ⟨hs, fun _ _ => rfl⟩
  simp only [h, Finset.sup_singleton, stateSeminormFamily]

/-- Seminorm is symmetric under swapping arguments of difference. -/
lemma stateSeminormSeminorm_sub_comm (a m : FreeStarAlgebra n) :
    stateSeminormSeminorm (m - a) = stateSeminorm (a - m) := by
  change stateSeminorm (m - a) = stateSeminorm (a - m)
  rw [← neg_sub a m, stateSeminorm_neg]

/-- The seminorm ball is a neighborhood of its center. -/
lemma seminorm_ball_mem_nhds (a : FreeStarAlgebra n) {r : ℝ} (hr : 0 < r) :
    stateSeminormSeminorm.ball a r ∈ nhds a := by
  rw [withSeminorms_stateSeminormFamily.mem_nhds_iff]
  refine ⟨{()}, r, hr, ?_⟩
  intro x hx; simp only [Finset.sup_singleton, stateSeminormFamily] at hx ⊢; exact hx

/-- Forward: ε-δ closure ⊆ topological closure. -/
theorem quadraticModuleClosure_subset_closure :
    quadraticModuleClosure ⊆ closure (QuadraticModule n : Set (FreeStarAlgebra n)) := by
  intro a ha
  rw [mem_closure_iff]
  intro U hU haU
  rw [withSeminorms_stateSeminormFamily.isOpen_iff_mem_balls] at hU
  obtain ⟨s, r, hr, hball⟩ := hU a haU
  obtain ⟨m, hm, hdist⟩ := ha r hr
  refine ⟨m, ?_, hm⟩
  apply hball
  simp only [Seminorm.mem_ball]
  by_cases hs : s.Nonempty
  · rw [finset_sup_unit_eq s hs, stateSeminormSeminorm_sub_comm]; exact hdist
  · simp only [Finset.not_nonempty_iff_eq_empty] at hs; simp [hs, hr]

/-- Reverse: topological closure ⊆ ε-δ closure. -/
theorem closure_subset_quadraticModuleClosure :
    closure (QuadraticModule n : Set (FreeStarAlgebra n)) ⊆ quadraticModuleClosure := by
  intro a ha ε hε
  have hball : stateSeminormSeminorm.ball a ε ∈ nhds a := seminorm_ball_mem_nhds a hε
  rw [mem_closure_iff_nhds] at ha
  obtain ⟨m, hm_ball, hm⟩ := ha _ hball
  refine ⟨m, hm, ?_⟩
  rw [Seminorm.mem_ball] at hm_ball
  rw [← stateSeminormSeminorm_sub_comm]; exact hm_ball

/-- The ε-δ closure equals the topological closure. -/
theorem quadraticModuleClosure_eq_closure :
    quadraticModuleClosure = closure (QuadraticModule n : Set (FreeStarAlgebra n)) :=
  Set.Subset.antisymm quadraticModuleClosure_subset_closure closure_subset_quadraticModuleClosure

/-- The closure M̄ is closed in the seminorm topology. -/
theorem isClosed_quadraticModuleClosure : IsClosed (quadraticModuleClosure (n := n)) := by
  rw [quadraticModuleClosure_eq_closure]; exact isClosed_closure

end WithTopology

end FreeStarAlgebra
