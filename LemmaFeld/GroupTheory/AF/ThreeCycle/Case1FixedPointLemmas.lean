/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.ThreeCycle.Case1FixedPointProofs

/-!
# Fixed-Point Lemmas for Case 1: m ≥ 1, k = 0

This file re-exports the fixed-point theorems for the squared product (c₁₃ * c₂₃⁻¹)².
These lemmas show that elements 0, 1, 2 and tail elements are fixed by squaring.

## Key Results

All fixed-point lemmas have been fully proven in Case1FixedPointProofs.lean.
-/

open Equiv Perm

namespace LemmaFeld.GroupTheory.AF.Case1FixedPointLemmas

/-- (c₁₃ * c₂₃⁻¹)²(0) = 0 (2-cycle (0,1) squared) -/
theorem sq_fixes_0 (n m : ℕ) (hm : m ≥ 1) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) ⟨0, by omega⟩ = ⟨0, by omega⟩ :=
  Case1FixedPointProofs.sq_fixes_0 n m hm

/-- (c₁₃ * c₂₃⁻¹)²(1) = 1 (2-cycle (0,1) squared) -/
theorem sq_fixes_1 (n m : ℕ) (hm : m ≥ 1) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) ⟨1, by omega⟩ = ⟨1, by omega⟩ :=
  Case1FixedPointProofs.sq_fixes_1 n m hm

/-- (c₁₃ * c₂₃⁻¹)²(2) = 2 (2-cycle (2, last_tailC) squared) -/
theorem sq_fixes_2 (n m : ℕ) (hm : m ≥ 1) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) ⟨2, by omega⟩ = ⟨2, by omega⟩ :=
  Case1FixedPointProofs.sq_fixes_2 n m hm

/-- (c₁₃ * c₂₃⁻¹)² fixes elements in tailA (indices 6 ≤ x < 6+n) -/
theorem sq_fixes_tailA (n m : ℕ) (x : Omega n 0 m) (hx : 6 ≤ x.val ∧ x.val < 6 + n) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) x = x :=
  Case1FixedPointProofs.sq_fixes_tailA n m x hx

/-- (c₁₃ * c₂₃⁻¹)² fixes elements in tailC (indices 6+n ≤ x < 6+n+m) -/
theorem sq_fixes_tailC (n m : ℕ) (hm : m ≥ 1) (x : Omega n 0 m) (hx : 6 + n ≤ x.val) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) x = x :=
  Case1FixedPointProofs.sq_fixes_tailC n m hm x hx

/-- (c₁₃ * c₂₃⁻¹)² fixes elements ≥ 6 -/
theorem sq_fixes_ge6 (n m : ℕ) (hm : m ≥ 1) (x : Omega n 0 m) (hx : x.val ≥ 6) :
    (SymmetricCase1.c₁₃_times_c₂₃_inv n m ^ 2) x = x :=
  Case1FixedPointProofs.sq_fixes_ge6 n m hm x hx

end LemmaFeld.GroupTheory.AF.Case1FixedPointLemmas
