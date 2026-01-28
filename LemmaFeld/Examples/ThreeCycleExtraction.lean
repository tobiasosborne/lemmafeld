/-
  Verification of 3-Cycle Extraction Method for Corrected Lemma 9

  GIVEN (verified results):
  - c₁₂ = [g₁, g₂] = (1 7 5)(2 4 6) - two disjoint 3-cycles
  - c₁₃ = [g₁, g₃] = (1 2 3 4 5 6) - a 6-cycle

  PROPOSED EXTRACTION METHOD:
  1. Compute c₁₃²
  2. Compute c₁₂ · (c₁₃²)⁻¹

  This file computationally verifies the extraction produces (3 7 5).
-/

import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.Perm.Fin

open Equiv Perm

-- We work in Perm (Fin 7), elements labeled 0-6 (representing 1-7)
-- Convention: element k in our notation corresponds to Fin.mk (k-1) in Lean

-- Define the commutator c₁₂ = (1 7 5)(2 4 6)
-- In 0-indexed: (0 6 4)(1 3 5)
def c₁₂ : Perm (Fin 7) :=
  c[0, 6, 4] * c[1, 3, 5]

-- Define the commutator c₁₃ = (1 2 3 4 5 6), fixing 7
-- In 0-indexed: (0 1 2 3 4 5), fixing 6
def c₁₃ : Perm (Fin 7) :=
  c[0, 1, 2, 3, 4, 5]

-- Compute c₁₃² = (1 3 5)(2 4 6)
-- In 0-indexed: (0 2 4)(1 3 5)
def c₁₃_sq : Perm (Fin 7) := c₁₃ * c₁₃

-- The extracted 3-cycle should be (3 7 5)
-- In 0-indexed: (2 6 4)
def extracted_3cycle : Perm (Fin 7) := c₁₂ * c₁₃_sq⁻¹

-- Expected result: (3 7 5) in 1-indexed = (2 6 4) in 0-indexed
def expected_3cycle : Perm (Fin 7) := c[2, 6, 4]

-- ============================================
-- VERIFICATION THEOREMS
-- ============================================

-- Verify c₁₃² = (0 2 4)(1 3 5)
theorem c13_sq_is_two_3cycles : c₁₃_sq = c[0, 2, 4] * c[1, 3, 5] := by
  native_decide

-- Verify c₁₃² applied to each element
theorem c13_sq_action_0 : c₁₃_sq 0 = 2 := by native_decide  -- 1 → 3
theorem c13_sq_action_1 : c₁₃_sq 1 = 3 := by native_decide  -- 2 → 4
theorem c13_sq_action_2 : c₁₃_sq 2 = 4 := by native_decide  -- 3 → 5
theorem c13_sq_action_3 : c₁₃_sq 3 = 5 := by native_decide  -- 4 → 6
theorem c13_sq_action_4 : c₁₃_sq 4 = 0 := by native_decide  -- 5 → 1
theorem c13_sq_action_5 : c₁₃_sq 5 = 1 := by native_decide  -- 6 → 2
theorem c13_sq_action_6 : c₁₃_sq 6 = 6 := by native_decide  -- 7 → 7 (fixed)

-- Verify (c₁₃²)⁻¹ applied to each element
theorem c13_sq_inv_action_0 : c₁₃_sq⁻¹ 0 = 4 := by native_decide  -- 1 → 5
theorem c13_sq_inv_action_1 : c₁₃_sq⁻¹ 1 = 5 := by native_decide  -- 2 → 6
theorem c13_sq_inv_action_2 : c₁₃_sq⁻¹ 2 = 0 := by native_decide  -- 3 → 1
theorem c13_sq_inv_action_3 : c₁₃_sq⁻¹ 3 = 1 := by native_decide  -- 4 → 2
theorem c13_sq_inv_action_4 : c₁₃_sq⁻¹ 4 = 2 := by native_decide  -- 5 → 3
theorem c13_sq_inv_action_5 : c₁₃_sq⁻¹ 5 = 3 := by native_decide  -- 6 → 4
theorem c13_sq_inv_action_6 : c₁₃_sq⁻¹ 6 = 6 := by native_decide  -- 7 → 7 (fixed)

-- ============================================
-- MAIN THEOREM: The extraction produces (3 7 5)
-- ============================================

theorem extraction_is_3_7_5 : extracted_3cycle = expected_3cycle := by
  native_decide

-- Verify the extracted permutation is indeed a 3-cycle by checking its action
theorem extracted_action_0 : extracted_3cycle 0 = 0 := by native_decide  -- 1 fixed
theorem extracted_action_1 : extracted_3cycle 1 = 1 := by native_decide  -- 2 fixed
theorem extracted_action_2 : extracted_3cycle 2 = 6 := by native_decide  -- 3 → 7
theorem extracted_action_3 : extracted_3cycle 3 = 3 := by native_decide  -- 4 fixed
theorem extracted_action_4 : extracted_3cycle 4 = 2 := by native_decide  -- 5 → 3
theorem extracted_action_5 : extracted_3cycle 5 = 5 := by native_decide  -- 6 fixed
theorem extracted_action_6 : extracted_3cycle 6 = 4 := by native_decide  -- 7 → 5

-- Verify it's a 3-cycle: 3 → 7 → 5 → 3 (in 1-indexed)
-- That is: 2 → 6 → 4 → 2 (in 0-indexed)
theorem cycle_check_3 : extracted_3cycle 2 = 6 := by native_decide
theorem cycle_check_7 : extracted_3cycle 6 = 4 := by native_decide
theorem cycle_check_5 : extracted_3cycle 4 = 2 := by native_decide

-- Verify the cycle closes
theorem cycle_closes : extracted_3cycle (extracted_3cycle (extracted_3cycle 2)) = 2 := by
  native_decide

-- ============================================
-- STEP-BY-STEP TRACE VERIFICATION
-- ============================================

-- For each x, trace through (c₁₃²)⁻¹ then c₁₂
-- The composition is: x ↦ (c₁₃²)⁻¹(x) ↦ c₁₂((c₁₃²)⁻¹(x))

-- x=1 (0-indexed: 0): (c₁₃²)⁻¹(0)=4, c₁₂(4)=0. Result: 0 (fixed)
theorem trace_0 : c₁₂ (c₁₃_sq⁻¹ 0) = 0 := by native_decide

-- x=2 (0-indexed: 1): (c₁₃²)⁻¹(1)=5, c₁₂(5)=1. Result: 1 (fixed)
theorem trace_1 : c₁₂ (c₁₃_sq⁻¹ 1) = 1 := by native_decide

-- x=3 (0-indexed: 2): (c₁₃²)⁻¹(2)=0, c₁₂(0)=6. Result: 2→6 (3→7)
theorem trace_2 : c₁₂ (c₁₃_sq⁻¹ 2) = 6 := by native_decide

-- x=4 (0-indexed: 3): (c₁₃²)⁻¹(3)=1, c₁₂(1)=3. Result: 3 (fixed)
theorem trace_3 : c₁₂ (c₁₃_sq⁻¹ 3) = 3 := by native_decide

-- x=5 (0-indexed: 4): (c₁₃²)⁻¹(4)=2, c₁₂(2)=2. Result: 4→2 (5→3)
theorem trace_4 : c₁₂ (c₁₃_sq⁻¹ 4) = 2 := by native_decide

-- x=6 (0-indexed: 5): (c₁₃²)⁻¹(5)=3, c₁₂(3)=5. Result: 5 (fixed)
theorem trace_5 : c₁₂ (c₁₃_sq⁻¹ 5) = 5 := by native_decide

-- x=7 (0-indexed: 6): (c₁₃²)⁻¹(6)=6, c₁₂(6)=4. Result: 6→4 (7→5)
theorem trace_6 : c₁₂ (c₁₃_sq⁻¹ 6) = 4 := by native_decide

-- ============================================
-- SUMMARY THEOREM
-- ============================================

/--
The 3-cycle extraction method works:
Given c₁₂ = (1 7 5)(2 4 6) and c₁₃ = (1 2 3 4 5 6),
the product c₁₂ · (c₁₃²)⁻¹ = (3 7 5), a single 3-cycle.
-/
theorem three_cycle_extraction_works :
    c₁₂ * c₁₃_sq⁻¹ = c[2, 6, 4] := by
  native_decide

-- Verify c₁₂ structure: (1 7 5)(2 4 6) in 1-indexed = (0 6 4)(1 3 5) in 0-indexed
theorem c12_structure : c₁₂ = c[0, 6, 4] * c[1, 3, 5] := rfl

-- Verify c₁₃ structure: (1 2 3 4 5 6) in 1-indexed = (0 1 2 3 4 5) in 0-indexed
theorem c13_structure : c₁₃ = c[0, 1, 2, 3, 4, 5] := rfl
