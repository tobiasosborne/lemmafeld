import LemmaFeld.GroupTheory.AF.ThreeCycle.Case1CommutatorLemmas
import LemmaFeld.GroupTheory.AF.ThreeCycle.SymmetricCase1Helpers

open Equiv Perm LemmaFeld.GroupTheory.AF.SymmetricCase1 LemmaFeld.GroupTheory.AF.Case1CommutatorLemmas

-- Trace single application: prod(0) = ?
#eval (c₁₃_times_c₂₃_inv 1 1) ⟨0, by omega⟩  

-- Trace single application: prod(1) = ?
#eval (c₁₃_times_c₂₃_inv 1 1) ⟨1, by omega⟩

-- Trace single application: prod(2) = ?
#eval (c₁₃_times_c₂₃_inv 1 1) ⟨2, by omega⟩

-- Trace tailA element: prod(6) = ?
#eval (c₁₃_times_c₂₃_inv 1 1) ⟨6, by omega⟩

-- Trace tailC element: prod(7) = ?
#eval (c₁₃_times_c₂₃_inv 1 1) ⟨7, by omega⟩
