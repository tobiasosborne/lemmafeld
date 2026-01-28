import LemmaFeld.GroupTheory.AF.ThreeCycle.Case1CommutatorLemmas
import LemmaFeld.GroupTheory.AF.ThreeCycle.SymmetricCase1Helpers

open Equiv Perm LemmaFeld.GroupTheory.AF.SymmetricCase1 LemmaFeld.GroupTheory.AF.Case1CommutatorLemmas

-- Verify sq(0) = 0 for n=1, m=1
#eval (c₁₃_times_c₂₃_inv 1 1 ^ 2) ⟨0, by omega⟩  -- expect ⟨0, _⟩

-- Verify sq(1) = 1 for n=1, m=1
#eval (c₁₃_times_c₂₃_inv 1 1 ^ 2) ⟨1, by omega⟩  -- expect ⟨1, _⟩

-- Verify sq(2) = 2 for n=1, m=1
#eval (c₁₃_times_c₂₃_inv 1 1 ^ 2) ⟨2, by omega⟩  -- expect ⟨2, _⟩

-- Verify sq(6) = 6 for n=1, m=1 (tailA element)
#eval (c₁₃_times_c₂₃_inv 1 1 ^ 2) ⟨6, by omega⟩  -- expect ⟨6, _⟩

-- Verify sq(7) = 7 for n=1, m=1 (tailC element)
#eval (c₁₃_times_c₂₃_inv 1 1 ^ 2) ⟨7, by omega⟩  -- expect ⟨7, _⟩

-- Verify 3-cycle
#eval (c₁₃_times_c₂₃_inv 1 1 ^ 2) ⟨3, by omega⟩  -- expect ⟨4, _⟩
#eval (c₁₃_times_c₂₃_inv 1 1 ^ 2) ⟨4, by omega⟩  -- expect ⟨5, _⟩
#eval (c₁₃_times_c₂₃_inv 1 1 ^ 2) ⟨5, by omega⟩  -- expect ⟨3, _⟩
