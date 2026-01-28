/-
  LemmaFeld - A monorepo for Lean 4 formalizations

  ## Structure

  - Analysis/OperatorAlgebras/: GNS construction, Archimedean closure
  - GroupTheory/AF: H = An or Sn for permutation groups
  - CategoryTheory/TensorCategories: (Planned) Tensor categories
  - Examples: Standalone proof examples

  ## Projects

  ### GNS Construction
  The Gelfand-Naimark-Segal construction for C*-algebras.

  ### Archimedean Closure
  Characterization: A ∈ M̄ ⟺ A ≥ 0 in all constrained *-representations.

  ### AF (Alternating Groups)
  H = ⟨g₁, g₂, g₃⟩ equals Aₙ or Sₙ for Ω = Fin(6+n+k+m).
-/

-- Analysis / Operator Algebras
import LemmaFeld.Analysis.OperatorAlgebras.GNS
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure

-- Group Theory
import LemmaFeld.GroupTheory.AF

-- Category Theory (uncomment when chapters are added)
-- import LemmaFeld.CategoryTheory.TensorCategories

-- Examples (standalone proofs)
import LemmaFeld.Examples.Sqrt2Irrational
import LemmaFeld.Examples.InfinitelyManyPrimes
