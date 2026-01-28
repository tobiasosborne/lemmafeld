/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Algebra.QuadraticModule

/-! # Archimedean Property

This file defines the Archimedean property for the quadratic module.

## Main definitions

* `IsArchimedean n` - Class asserting ∀a, ∃N, N·1 - a*a ∈ M
* `archimedeanBound a` - The minimal N such that N·1 - a*a ∈ M
* `archimedeanBound_spec` - Proof that the bound works

## Mathematical Background

The Archimedean property ensures that for every element a, its "square" star(a)*a
is bounded by some multiple of the identity in the quadratic module sense.
This is crucial for proving that M-positive states are bounded.
-/

namespace FreeStarAlgebra

variable {n : ℕ}

/-- Archimedean property: ∀a, ∃N, N·1 - a*a ∈ M.

This says that star(a)*a is "bounded" by some N·1 in the sense that
N·1 - star(a)*a belongs to the quadratic module M. -/
class IsArchimedean (n : ℕ) : Prop where
  bound : ∀ a : FreeStarAlgebra n,
    ∃ N : ℕ, (N : ℝ) • (1 : FreeStarAlgebra n) - star a * a ∈ QuadraticModule n

/-- Some N such that N·1 - a*a ∈ M (not necessarily minimal). -/
noncomputable def archimedeanBound [IsArchimedean n] (a : FreeStarAlgebra n) : ℕ :=
  Classical.choose (IsArchimedean.bound a)

/-- The Archimedean bound satisfies the defining property. -/
theorem archimedeanBound_spec [IsArchimedean n] (a : FreeStarAlgebra n) :
    (archimedeanBound a : ℝ) • (1 : FreeStarAlgebra n) - star a * a ∈ QuadraticModule n :=
  Classical.choose_spec (IsArchimedean.bound a)

end FreeStarAlgebra
