/-
  LemmaFeld.Analysis.OperatorAlgebras.GNS

  The Gelfand-Naimark-Segal (GNS) Construction for C*-algebras.

  ## Main Results

  * `State.gns_theorem` - Every state on a C*-algebra arises as a vector state

  ## Structure

  - State/: State definitions and Cauchy-Schwarz inequalities
  - NullSpace/: The null space N_φ and its properties
  - PreHilbert/: Pre-Hilbert space structure on A/N_φ
  - Representation/: The *-representation π_φ
  - HilbertSpace/: Completion to Hilbert space H_φ
  - Main/: The main GNS theorem and uniqueness
-/

-- State theory
import LemmaFeld.Analysis.OperatorAlgebras.GNS.State.Basic
import LemmaFeld.Analysis.OperatorAlgebras.GNS.State.Positivity
import LemmaFeld.Analysis.OperatorAlgebras.GNS.State.CauchySchwarz
import LemmaFeld.Analysis.OperatorAlgebras.GNS.State.CauchySchwarzTight

-- Null space
import LemmaFeld.Analysis.OperatorAlgebras.GNS.NullSpace.Basic
import LemmaFeld.Analysis.OperatorAlgebras.GNS.NullSpace.LeftIdeal
import LemmaFeld.Analysis.OperatorAlgebras.GNS.NullSpace.Quotient

-- Pre-Hilbert space
import LemmaFeld.Analysis.OperatorAlgebras.GNS.PreHilbert.InnerProduct
import LemmaFeld.Analysis.OperatorAlgebras.GNS.PreHilbert.Positive
import LemmaFeld.Analysis.OperatorAlgebras.GNS.PreHilbert.Seminorm

-- Representation
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Representation.PreRep
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Representation.Star
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Representation.Bounded
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Representation.Extension

-- Hilbert space
import LemmaFeld.Analysis.OperatorAlgebras.GNS.HilbertSpace.Completion
import LemmaFeld.Analysis.OperatorAlgebras.GNS.HilbertSpace.CyclicVector

-- Main theorem
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Main.VectorState
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Main.Theorem
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Main.Uniqueness
import LemmaFeld.Analysis.OperatorAlgebras.GNS.Main.UniquenessTheorem
