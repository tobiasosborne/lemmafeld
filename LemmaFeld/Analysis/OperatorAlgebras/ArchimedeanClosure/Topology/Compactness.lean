/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Topology.StateTopology
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Topology.Closedness
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Boundedness.ArchimedeanBound
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.ProperSpace

/-! # Compactness of State Space S_M

This file proves that the set of M-positive states is compact in the pointwise
convergence topology.

## Main results

* `MPositiveState.apply_mem_closedBall` - Each state value is bounded
* `MPositiveState.stateSet_subset_product` - S_M ⊆ product of closed balls

## Proof strategy

1. The Archimedean bound shows |φ(a)| ≤ √Nₐ for all φ ∈ S_M
2. S_M embeds into ∏ₐ closedBall 0 √Nₐ ⊆ (FreeStarAlgebra n → ℝ)
3. This product is compact by Tychonoff
4. S_M is closed (defined by closed conditions)
5. Closed subset of compact is compact
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ}

section Embedding

/-- The embedding of S_M into a product of reals.

Each state φ is mapped to the function a ↦ φ(a). -/
def toProductFun (φ : MPositiveState n) : FreeStarAlgebra n → ℝ := fun a => φ a

/-- The embedding is injective. -/
theorem toProductFun_injective : Function.Injective (toProductFun (n := n)) := by
  intro φ ψ h
  apply DFunLike.coe_injective'
  exact h

end Embedding

section Bounded

variable [IsArchimedean n]

/-- The bound function: maps each element to its Archimedean bound. -/
noncomputable def bound (a : FreeStarAlgebra n) : ℝ := Real.sqrt (archimedeanBound a)

/-- States are bounded: each evaluation lands in a closed ball. -/
theorem apply_mem_closedBall (φ : MPositiveState n) (a : FreeStarAlgebra n) :
    φ a ∈ Metric.closedBall (0 : ℝ) (bound a) := by
  rw [Metric.mem_closedBall, dist_zero_right]
  exact φ.apply_abs_le a

/-- States map into the bounded product set. -/
theorem stateSet_subset_product :
    Set.range (toProductFun (n := n)) ⊆
    { f | ∀ a, f a ∈ Metric.closedBall (0 : ℝ) (bound a) } := by
  intro f ⟨φ, hφ⟩ a
  rw [← hφ]
  exact φ.apply_mem_closedBall a

/-- The product of closed balls is compact (Tychonoff). -/
theorem product_compact :
    IsCompact { f : FreeStarAlgebra n → ℝ | ∀ a, f a ∈ Metric.closedBall (0 : ℝ) (bound a) } := by
  -- Rewrite using Set.pi
  have h_eq : { f : FreeStarAlgebra n → ℝ | ∀ a, f a ∈ Metric.closedBall (0 : ℝ) (bound a) } =
      Set.univ.pi (fun a => Metric.closedBall (0 : ℝ) (bound a)) := by
    ext f
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, true_implies]
  rw [h_eq]
  -- Apply Tychonoff: product of compact sets is compact
  apply isCompact_univ_pi
  intro a
  exact ProperSpace.isCompact_closedBall 0 (bound a)

/-- The set of functions satisfying all state conditions. -/
def stateConditions : Set (FreeStarAlgebra n → ℝ) :=
  {f | (∀ a b, f (a + b) = f a + f b) ∧
       (∀ c a, f (c • a) = c * f a) ∧
       (∀ a, f (star a) = f a) ∧
       (∀ m ∈ QuadraticModule n, 0 ≤ f m) ∧
       f 1 = 1}

omit [IsArchimedean n] in
/-- The state conditions form a closed set. -/
theorem stateConditions_isClosed : IsClosed (stateConditions (n := n)) := by
  unfold stateConditions
  apply IsClosed.inter isClosed_additivity
  apply IsClosed.inter isClosed_homogeneity
  apply IsClosed.inter isClosed_star_symmetry
  apply IsClosed.inter isClosed_m_nonneg
  exact isClosed_normalized

omit [IsArchimedean n] in
/-- The range of toProductFun is contained in stateConditions. -/
theorem range_subset_stateConditions :
    Set.range (toProductFun (n := n)) ⊆ stateConditions := by
  intro f ⟨φ, hφ⟩
  simp only [stateConditions, Set.mem_setOf_eq]
  rw [← hφ]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b; exact φ.map_add a b
  · intro c a; exact φ.map_smul c a
  · intro a; exact φ.apply_star a
  · intro m hm; exact φ.apply_m_nonneg hm
  · exact φ.apply_one

omit [IsArchimedean n] in
/-- Build an MPositiveState from a function satisfying state conditions. -/
def ofFunction (f : FreeStarAlgebra n → ℝ)
    (hf_add : ∀ a b, f (a + b) = f a + f b)
    (hf_smul : ∀ c a, f (c • a) = c * f a)
    (hf_star : ∀ a, f (star a) = f a)
    (hf_m_nonneg : ∀ m ∈ QuadraticModule n, 0 ≤ f m)
    (hf_one : f 1 = 1) : MPositiveState n where
  toFun := {
    toFun := f
    map_add' := hf_add
    map_smul' := by intro c a; simp only [RingHom.id_apply]; exact hf_smul c a
  }
  map_star := hf_star
  map_one := hf_one
  map_m_nonneg := hf_m_nonneg

omit [IsArchimedean n] in
/-- stateConditions is exactly the range of toProductFun. -/
theorem stateConditions_subset_range :
    stateConditions (n := n) ⊆ Set.range toProductFun := by
  intro f hf
  simp only [stateConditions, Set.mem_setOf_eq] at hf
  obtain ⟨hf_add, hf_smul, hf_star, hf_m_nonneg, hf_one⟩ := hf
  exact ⟨ofFunction f hf_add hf_smul hf_star hf_m_nonneg hf_one, rfl⟩

omit [IsArchimedean n] in
/-- The range equals stateConditions. -/
theorem range_eq_stateConditions :
    Set.range (toProductFun (n := n)) = stateConditions :=
  Set.Subset.antisymm range_subset_stateConditions stateConditions_subset_range

omit [IsArchimedean n] in
/-- The state set is closed in the product topology.

The range equals stateConditions (intersection of closed sets). -/
theorem stateSet_isClosed :
    IsClosed (Set.range (toProductFun (n := n))) := by
  rw [range_eq_stateConditions]
  exact stateConditions_isClosed

/-- The state set is compact. -/
theorem stateSet_isCompact :
    IsCompact (Set.range (toProductFun (n := n))) := by
  apply IsCompact.of_isClosed_subset product_compact stateSet_isClosed
  exact stateSet_subset_product

end Bounded

end MPositiveState

end FreeStarAlgebra
