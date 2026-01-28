/-
  LemmaFeld.GroupTheory.AF.Core - Root module for core definitions

  This module re-exports all core components needed for the AF-Tests formalization:
  - Omega: The permutation domain Fin(6+n+k+m)
  - Generators: The three generators g₁, g₂, g₃
  - GroupH: The subgroup H = ⟨g₁, g₂, g₃⟩
  - Blocks: Block structure for primitivity analysis
-/

import LemmaFeld.GroupTheory.AF.Core.Omega
import LemmaFeld.GroupTheory.AF.Core.Generators
import LemmaFeld.GroupTheory.AF.Core.GroupH
import LemmaFeld.GroupTheory.AF.Core.Blocks
