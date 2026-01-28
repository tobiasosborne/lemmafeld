/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma06
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma07
import LemmaFeld.GroupTheory.AF.BaseCase.Lemma03
import Mathlib.GroupTheory.Perm.Cycle.Concrete

/-!
# Lemma 9: 3-Cycle Extraction

Extract 3-cycles from products of commutators. We compute c₁₂ * c₁₃⁻¹ where:
- c₁₂ = [g₁, g₂] (from Lemma 6)
- c₁₃ = [g₁, g₃] (from Lemma 7)

## Main Results

* `c₁₂_times_c₁₃_inv` - The product c₁₂ * c₁₃⁻¹
* `c₁₂_times_c₁₃_inv_base_case_eq` - In base case: c₁₂ * c₁₃⁻¹ = (0 1 5)(2 3 4)
* `c₁₂_times_c₁₃_inv_mem_H` - The product is in H

## Proof Strategy

Direct computation using `native_decide` for the base case n=k=m=0.
The product c₁₂ * c₁₃⁻¹ is a product of two disjoint 3-cycles.

## Reference

See `examples/lemmas/lemma09_3cycle_extraction.md` for the natural language proof.
-/

open Equiv Perm

-- ============================================
-- DEFINITIONS
-- ============================================

/-- c₁₂ = [g₁, g₂] from Lemma 6 -/
abbrev c₁₂ (n k m : ℕ) : Perm (Omega n k m) := commutator_g₁_g₂ n k m

/-- c₁₃ = [g₁, g₃] from Lemma 7 -/
abbrev c₁₃ (n k m : ℕ) : Perm (Omega n k m) := commutator_g₁_g₃ n k m

/-- The product c₁₂ * c₁₃⁻¹ -/
def c₁₂_times_c₁₃_inv (n k m : ℕ) : Perm (Omega n k m) :=
  c₁₂ n k m * (c₁₃ n k m)⁻¹

-- ============================================
-- BASE CASE: n = k = m = 0 (S₆)
-- ============================================

/-- c₁₂ * c₁₃⁻¹ in base case equals (0 1 5)(2 3 4).
    This is a product of two disjoint 3-cycles. -/
theorem c₁₂_times_c₁₃_inv_base_case_eq :
    c₁₂_times_c₁₃_inv 0 0 0 = c[0, 1, 5] * c[2, 3, 4] := by
  native_decide

-- ============================================
-- ELEMENT-WISE VERIFICATION
-- ============================================

/-- Product action on element 0: 0 → 1 -/
theorem product_action_0 : c₁₂_times_c₁₃_inv 0 0 0 0 = 1 := by native_decide

/-- Product action on element 1: 1 → 5 -/
theorem product_action_1 : c₁₂_times_c₁₃_inv 0 0 0 1 = 5 := by native_decide

/-- Product action on element 2: 2 → 3 -/
theorem product_action_2 : c₁₂_times_c₁₃_inv 0 0 0 2 = 3 := by native_decide

/-- Product action on element 3: 3 → 4 -/
theorem product_action_3 : c₁₂_times_c₁₃_inv 0 0 0 3 = 4 := by native_decide

/-- Product action on element 4: 4 → 2 -/
theorem product_action_4 : c₁₂_times_c₁₃_inv 0 0 0 4 = 2 := by native_decide

/-- Product action on element 5: 5 → 0 -/
theorem product_action_5 : c₁₂_times_c₁₃_inv 0 0 0 5 = 0 := by native_decide

/-- First 3-cycle (0 1 5) closes: 0 → 1 → 5 → 0 -/
theorem first_cycle_closes :
    c₁₂_times_c₁₃_inv 0 0 0 (c₁₂_times_c₁₃_inv 0 0 0 (c₁₂_times_c₁₃_inv 0 0 0 0)) = 0 := by
  native_decide

/-- Second 3-cycle (2 3 4) closes: 2 → 3 → 4 → 2 -/
theorem second_cycle_closes :
    c₁₂_times_c₁₃_inv 0 0 0 (c₁₂_times_c₁₃_inv 0 0 0 (c₁₂_times_c₁₃_inv 0 0 0 2)) = 2 := by
  native_decide

-- ============================================
-- 3-CYCLE COMPONENTS
-- ============================================

/-- The first component c[0, 1, 5] -/
def first_3cycle_L9 : Perm (Omega 0 0 0) := c[0, 1, 5]

/-- The second component c[2, 3, 4] -/
def second_3cycle_L9 : Perm (Omega 0 0 0) := c[2, 3, 4]

/-- The two 3-cycles are disjoint -/
theorem cycles_L9_disjoint :
    Disjoint (first_3cycle_L9).support (second_3cycle_L9).support := by
  native_decide

-- ============================================
-- MEMBERSHIP IN H
-- ============================================

/-- c₁₂ * c₁₃⁻¹ is in H since both c₁₂ and c₁₃ are in H -/
theorem c₁₂_times_c₁₃_inv_mem_H : c₁₂_times_c₁₃_inv 0 0 0 ∈ H 0 0 0 := by
  unfold c₁₂_times_c₁₃_inv c₁₂ c₁₃
  apply Subgroup.mul_mem
  · exact commutator_g₁_g₂_mem_H
  · exact Subgroup.inv_mem _ commutator_g₁_g₃_mem_H

-- ============================================
-- BASE CASE ANALYSIS: Individual 3-cycles NOT in H₆
-- ============================================

/-! ### Important: Base Case Structure

In the base case (n=k=m=0), H₆ ≅ S₄ with |H₆| = 24 (Lemma 3-4).
H₆ preserves the block structure B₀ = {{0,3}, {1,4}, {2,5}} (Lemma 1-3).

The individual 3-cycles c[0,1,5] and c[2,3,4] are NOT in H₆ because they
break this block structure:
- c[0,1,5] maps Block1 = {0,3} to {1,3}, which is not a block
- c[2,3,4] maps Block3 = {2,5} to {3,5}, which is not a block

The PRODUCT c[0,1,5] * c[2,3,4] = c₁₂ * c₁₃⁻¹ IS in H₆, but the individual
cycles cannot be extracted in the base case.

For the general case (n+k+m ≥ 1), the Main Theorem uses a different strategy:
squaring (c₁₂ * c₁₃⁻¹)² eliminates 2-cycles and yields a single 3-cycle.
See MainTheorem.lean for the correct 3-cycle extraction. -/

/-- c[0,1,5] does NOT preserve block B₀ - it maps {0,3} to {1,3} -/
theorem first_3cycle_L9_breaks_blocks :
    Block1.image first_3cycle_L9 ∉ B₀ := by native_decide

/-- c[2,3,4] does NOT preserve block B₀ - it maps {2,5} to {3,5} -/
theorem second_3cycle_L9_breaks_blocks :
    Block3.image second_3cycle_L9 ∉ B₀ := by native_decide

/-- c[0,1,5] is NOT in H₆ (base case) because it breaks the block structure -/
theorem first_3cycle_L9_not_mem_H₆ : first_3cycle_L9 ∉ H 0 0 0 := by
  intro h
  have hpres := LemmaFeld.GroupTheory.AF.BaseCase.H₆_imprimitive ⟨first_3cycle_L9, h⟩ Block1 Block1_mem_B₀
  exact first_3cycle_L9_breaks_blocks hpres

/-- c[2,3,4] is NOT in H₆ (base case) because it breaks the block structure -/
theorem second_3cycle_L9_not_mem_H₆ : second_3cycle_L9 ∉ H 0 0 0 := by
  intro h
  have hpres := LemmaFeld.GroupTheory.AF.BaseCase.H₆_imprimitive ⟨second_3cycle_L9, h⟩ Block3 Block3_mem_B₀
  exact second_3cycle_L9_breaks_blocks hpres

-- ============================================
-- 3-CYCLE PROPERTIES
-- ============================================

/-- The product c₁₂ * c₁₃⁻¹ has order 3 (since it's a product of disjoint 3-cycles) -/
theorem c₁₂_times_c₁₃_inv_cubed :
    (c₁₂_times_c₁₃_inv 0 0 0) ^ 3 = 1 := by
  native_decide

/-- H contains elements with 3-cycles -/
theorem H_contains_3cycle_product :
    ∃ σ ∈ H 0 0 0, σ = c[0, 1, 5] * c[2, 3, 4] :=
  ⟨c₁₂_times_c₁₃_inv 0 0 0, c₁₂_times_c₁₃_inv_mem_H, c₁₂_times_c₁₃_inv_base_case_eq⟩

-- ============================================
-- SQUARED PRODUCT (for 3-cycle extraction)
-- ============================================

/-- The squared product (c₁₂ * c₁₃⁻¹)².
    Squaring products of 3-cycles: (abc)² = (acb).
    So c[0,1,5]² = c[0,5,1] and c[2,3,4]² = c[2,4,3]. -/
def c₁₂_times_c₁₃_inv_squared : Perm (Omega 0 0 0) :=
  (c₁₂_times_c₁₃_inv 0 0 0) ^ 2

/-- The squared product equals c[0,5,1] * c[2,4,3] -/
theorem c₁₂_times_c₁₃_inv_squared_eq :
    c₁₂_times_c₁₃_inv_squared = c[0, 5, 1] * c[2, 4, 3] := by
  native_decide

/-- The squared product is in H -/
theorem c₁₂_times_c₁₃_inv_squared_mem_H : c₁₂_times_c₁₃_inv_squared ∈ H 0 0 0 := by
  unfold c₁₂_times_c₁₃_inv_squared
  exact Subgroup.pow_mem _ c₁₂_times_c₁₃_inv_mem_H 2
