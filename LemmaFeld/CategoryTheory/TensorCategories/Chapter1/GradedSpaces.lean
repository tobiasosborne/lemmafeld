/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Finite
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.GrothendieckGroup

/-!
# Chapter 1, Section 1.5.9: Graded Vector Spaces

Formalizes Example 1.5.9 from Etingof et al. "Tensor Categories" (AMS 2015), §1.5.

## §1.5.9 Example

Book: "Let S be a set and let Vec_S be the category of finite-dimensional k-vector
spaces graded by S (i.e., V = ⊕_{s∈S} V_s where V_s are finite-dimensional).
The simple objects are 1-dimensional spaces concentrated in a single degree s ∈ S.
Thus Gr(Vec_S) ≅ ℤ^S = FreeAbelianGroup S."

## Mathlib Correspondence

| Book | Mathlib | Notes |
|------|---------|-------|
| V = ⊕_s V_s | `DirectSum` | `Mathlib.Algebra.DirectSum.Basic` |
| Finite-dim | `Module.Finite` | `Mathlib.LinearAlgebra.Dimension.Finite` |
| Gr(Vec_S) ≅ ℤ^S | `FreeAbelianGroup S` | `Mathlib.GroupTheory.FreeAbelianGroup` |
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

/-! ## §1.5.9: The category Vec_S -/

section VecS

variable (k : Type*) [Field k] (S : Type*)

/-- An S-graded finite-dimensional vector space over k.

Book §1.5.9: "V = ⊕_{s∈S} V_s where V_s are finite-dimensional."
We represent this as a dependent family of k-modules indexed by S,
each finite-dimensional, with finite support. -/
structure GradedVecS where
  /-- The component vector space at each grade s ∈ S -/
  component : S → Type*
  [instACG : ∀ s, AddCommGroup (component s)]
  [instMod : ∀ s, Module k (component s)]
  [instFin : ∀ s, Module.Finite k (component s)]
  /-- Only finitely many components are nontrivial -/
  support : Finset S
  support_triv : ∀ s, s ∉ support → Subsingleton (component s)

attribute [instance] GradedVecS.instACG GradedVecS.instMod GradedVecS.instFin

/-- A morphism of S-graded vector spaces: a family of k-linear maps,
one for each grade s ∈ S, preserving the grading. -/
structure GradedVecS.Hom (V W : GradedVecS k S) where
  /-- The linear map at each grade -/
  app : ∀ s, V.component s →ₗ[k] W.component s

end VecS

/-! ## §1.5.9: Simple objects in Vec_S

Book: "The simple objects are 1-dimensional spaces concentrated in a single
degree s ∈ S."

We realize k_s using `Fin (if s = s₀ then 1 else 0) → k`:
- At degree s₀: component is `Fin 1 → k` (1-dimensional)
- At other degrees: component is `Fin 0 → k` (0-dimensional, subsingleton)
-/

section SimpleObjects

variable (k : Type*) [Field k] (S : Type*) [DecidableEq S]

/-- The simple object k_s: the field k concentrated in degree s₀.

Book §1.5.9: "1-dimensional spaces concentrated in a single degree s ∈ S." -/
def kConcentrated (s₀ : S) : GradedVecS k S where
  component s := Fin (if s = s₀ then 1 else 0) → k
  support := {s₀}
  support_triv s hs := by
    simp only [Finset.mem_singleton] at hs
    simp only [hs, ↓reduceIte]
    exact inferInstance

/-- The component of k_s₀ at degree s₀ has dimension 1. -/
theorem kConcentrated_finrank_eq (s₀ : S) :
    Module.finrank k ((kConcentrated k S s₀).component s₀) = 1 := by
  change Module.finrank k (Fin (if s₀ = s₀ then 1 else 0) → k) = 1
  simp

/-- The component of k_s₀ at degree s ≠ s₀ has dimension 0. -/
theorem kConcentrated_finrank_ne (s₀ s : S) (h : s ≠ s₀) :
    Module.finrank k ((kConcentrated k S s₀).component s) = 0 := by
  change Module.finrank k (Fin (if s = s₀ then 1 else 0) → k) = 0
  simp [h]

end SimpleObjects

/-! ## §1.5.9: Grothendieck group of Vec_S

Book: "Thus Gr(Vec_S) ≅ ℤ^S = FreeAbelianGroup S."

The key identification: each simple is k_s for a unique s ∈ S,
so iso classes of simples are in bijection with S.
Hence the free abelian group on simples is FreeAbelianGroup S.
-/

section GrothendieckGroupVecS

variable (S : Type*)

/-- The Grothendieck group of Vec_S is the free abelian group on S.

Book §1.5.9: "Gr(Vec_S) ≅ ℤ^S = FreeAbelianGroup S" -/
abbrev GrVecS := FreeAbelianGroup S

/-- The class of the simple object k_s in the Grothendieck group. -/
def classOfGrade (s : S) : GrVecS S := FreeAbelianGroup.of s

variable (k : Type*) [Field k] [DecidableEq S]

/-- The class map [V] ∈ Gr(Vec_S) for an S-graded space V.

Book §1.5.9: "[V] = ∑_s dim(V_s) · [k_s]" where [k_s] = classOfGrade s. -/
def gradedClass (V : GradedVecS k S) : GrVecS S :=
  V.support.sum fun s =>
    (Module.finrank k (V.component s) : ℤ) • FreeAbelianGroup.of s

/-- The class of k_s₀ in the Grothendieck group is the generator s₀.

This confirms that [k_s₀] = s₀ ∈ ℤ^S, as expected from the book. -/
theorem gradedClass_kConcentrated (s₀ : S) :
    gradedClass S k (kConcentrated k S s₀) = classOfGrade S s₀ := by
  unfold gradedClass kConcentrated classOfGrade
  simp only [Finset.sum_singleton]
  change (Module.finrank k (Fin (if s₀ = s₀ then 1 else 0) → k) : ℤ) •
    FreeAbelianGroup.of s₀ = FreeAbelianGroup.of s₀
  simp

end GrothendieckGroupVecS

/-! ## Summary

| Book §1.5.9 | Lean | Notes |
|--------------|------|-------|
| Vec_S | `GradedVecS k S` | S-graded finite-dim k-spaces |
| k_s (simple) | `kConcentrated k S s` | `Fin 1 → k` in degree s, trivial elsewhere |
| dim(k_s at s) = 1 | `kConcentrated_finrank_eq` | Proved |
| dim(k_s at t≠s) = 0 | `kConcentrated_finrank_ne` | Proved |
| Gr(Vec_S) ≅ ℤ^S | `GrVecS S = FreeAbelianGroup S` | Free abelian group on S |
| [V] | `gradedClass k S V` | ∑_s dim(V_s) · s |
| [k_s] = s | `gradedClass_kConcentrated` | Proved |
-/

end LemmaFeld.TensorCategories.Chapter1
