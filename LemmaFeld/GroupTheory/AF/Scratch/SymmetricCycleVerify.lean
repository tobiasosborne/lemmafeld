/-
Scratch file to verify cycle structures for ThreeCycleSymmetric.lean
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma06
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma07
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma08

open Equiv Perm

-- ============================================
-- CASE 1: m ≥ 1, k = 0: (c₁₃ * c₂₃⁻¹)²
-- ============================================

def c₁₃_times_c₂₃_inv (n m : ℕ) : Perm (Omega n 0 m) :=
  commutator_g₁_g₃ n 0 m * (commutator_g₂_g₃ n 0 m)⁻¹

-- Verify the 3-cycle is (3,4,5) for various n, m
-- n=0, m=1
#eval (c₁₃_times_c₂₃_inv 0 1 ^ 2) ⟨3, by omega⟩  -- expect 4
#eval (c₁₃_times_c₂₃_inv 0 1 ^ 2) ⟨4, by omega⟩  -- expect 5
#eval (c₁₃_times_c₂₃_inv 0 1 ^ 2) ⟨5, by omega⟩  -- expect 3

-- n=1, m=1
#eval (c₁₃_times_c₂₃_inv 1 1 ^ 2) ⟨3, by omega⟩  -- expect 4
#eval (c₁₃_times_c₂₃_inv 1 1 ^ 2) ⟨4, by omega⟩  -- expect 5
#eval (c₁₃_times_c₂₃_inv 1 1 ^ 2) ⟨5, by omega⟩  -- expect 3

-- n=2, m=2
#eval (c₁₃_times_c₂₃_inv 2 2 ^ 2) ⟨3, by omega⟩  -- expect 4
#eval (c₁₃_times_c₂₃_inv 2 2 ^ 2) ⟨4, by omega⟩  -- expect 5
#eval (c₁₃_times_c₂₃_inv 2 2 ^ 2) ⟨5, by omega⟩  -- expect 3

-- Verify fixed points
#eval (c₁₃_times_c₂₃_inv 1 1 ^ 2) ⟨0, by omega⟩  -- expect 0
#eval (c₁₃_times_c₂₃_inv 1 1 ^ 2) ⟨1, by omega⟩  -- expect 1
#eval (c₁₃_times_c₂₃_inv 1 1 ^ 2) ⟨2, by omega⟩  -- expect 2
#eval (c₁₃_times_c₂₃_inv 1 1 ^ 2) ⟨6, by omega⟩  -- tailA, expect 6
#eval (c₁₃_times_c₂₃_inv 1 1 ^ 2) ⟨7, by omega⟩  -- tailC, expect 7

-- Support cardinality check
theorem case1_support_3 : (c₁₃_times_c₂₃_inv 1 1 ^ 2).support.card = 3 := by native_decide

-- ============================================
-- CASE 2: k ≥ 1: (iteratedComm_g₂')²
-- ============================================

def iteratedComm_g₂' (n k m : ℕ) : Perm (Omega n k m) :=
  (commutator_g₁_g₂ n k m)⁻¹ * (g₂ n k m)⁻¹ * commutator_g₁_g₂ n k m * g₂ n k m

-- Verify the 3-cycle is (1,2,3)
-- n=0, k=1, m=0
#eval (iteratedComm_g₂' 0 1 0 ^ 2) ⟨1, by omega⟩  -- expect 2
#eval (iteratedComm_g₂' 0 1 0 ^ 2) ⟨2, by omega⟩  -- expect 3
#eval (iteratedComm_g₂' 0 1 0 ^ 2) ⟨3, by omega⟩  -- expect 1

-- n=1, k=1, m=0
#eval (iteratedComm_g₂' 1 1 0 ^ 2) ⟨1, by omega⟩  -- expect 2
#eval (iteratedComm_g₂' 1 1 0 ^ 2) ⟨2, by omega⟩  -- expect 3
#eval (iteratedComm_g₂' 1 1 0 ^ 2) ⟨3, by omega⟩  -- expect 1

-- n=0, k=2, m=0
#eval (iteratedComm_g₂' 0 2 0 ^ 2) ⟨1, by omega⟩  -- expect 2
#eval (iteratedComm_g₂' 0 2 0 ^ 2) ⟨2, by omega⟩  -- expect 3
#eval (iteratedComm_g₂' 0 2 0 ^ 2) ⟨3, by omega⟩  -- expect 1

-- n=1, k=2, m=1
#eval (iteratedComm_g₂' 1 2 1 ^ 2) ⟨1, by omega⟩  -- expect 2
#eval (iteratedComm_g₂' 1 2 1 ^ 2) ⟨2, by omega⟩  -- expect 3
#eval (iteratedComm_g₂' 1 2 1 ^ 2) ⟨3, by omega⟩  -- expect 1

-- Verify fixed points
#eval (iteratedComm_g₂' 1 1 0 ^ 2) ⟨0, by omega⟩  -- expect 0
#eval (iteratedComm_g₂' 1 1 0 ^ 2) ⟨4, by omega⟩  -- expect 4
#eval (iteratedComm_g₂' 1 1 0 ^ 2) ⟨5, by omega⟩  -- expect 5
#eval (iteratedComm_g₂' 1 1 0 ^ 2) ⟨6, by omega⟩  -- tailA, expect 6
#eval (iteratedComm_g₂' 1 1 0 ^ 2) ⟨7, by omega⟩  -- tailB, expect 7

-- Support cardinality check
theorem case2_support_3 : (iteratedComm_g₂' 1 1 0 ^ 2).support.card = 3 := by native_decide

-- ============================================
-- Single application values for Case 1
-- ============================================
#eval c₁₃_times_c₂₃_inv 1 1 ⟨0, by omega⟩
#eval c₁₃_times_c₂₃_inv 1 1 ⟨1, by omega⟩
#eval c₁₃_times_c₂₃_inv 1 1 ⟨2, by omega⟩
#eval c₁₃_times_c₂₃_inv 1 1 ⟨3, by omega⟩
#eval c₁₃_times_c₂₃_inv 1 1 ⟨4, by omega⟩
#eval c₁₃_times_c₂₃_inv 1 1 ⟨5, by omega⟩

-- ============================================
-- Single application values for Case 2
-- ============================================
#eval iteratedComm_g₂' 1 1 0 ⟨0, by omega⟩
#eval iteratedComm_g₂' 1 1 0 ⟨1, by omega⟩
#eval iteratedComm_g₂' 1 1 0 ⟨2, by omega⟩
#eval iteratedComm_g₂' 1 1 0 ⟨3, by omega⟩
#eval iteratedComm_g₂' 1 1 0 ⟨4, by omega⟩
#eval iteratedComm_g₂' 1 1 0 ⟨5, by omega⟩
