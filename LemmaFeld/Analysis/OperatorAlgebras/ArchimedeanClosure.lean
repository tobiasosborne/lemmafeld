/-
  LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure

  Characterization of the Archimedean closure in *-algebras.

  ## Main Results

  * `main_theorem` - A ∈ M̄ ⟺ A ≥ 0 in all constrained *-representations

  ## Structure

  - Algebra/: Archimedean *-algebras and quadratic modules
  - State/: M-positive states
  - Seminorm/: State seminorms and closure properties
  - Topology/: Weak-* topology and compactness
  - Boundedness/: Cauchy-Schwarz and generating cones
  - Dual/: Dual characterization via states
  - GNS/: GNS construction for *-algebras
  - Representation/: Constrained representations
  - Main/: The main theorem
-/

-- Algebra foundations
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Algebra.Archimedean
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Algebra.QuadraticModule
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Algebra.FreeStarAlgebra

-- States
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.State.MPositiveState
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.State.MPositiveStateProps
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.State.NonEmptiness

-- Seminorms
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Seminorm.StateSeminorm
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Seminorm.SeminormProps
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Seminorm.Closure

-- Topology
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Topology.StateTopology
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Topology.SeminormTopology
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Topology.Continuity
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Topology.Compactness
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Topology.Closedness

-- Boundedness
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Boundedness.CauchySchwarzM
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Boundedness.ArchimedeanBound
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Boundedness.GeneratingCone

-- Dual characterization
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Dual.SpanIntersection
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Dual.SeparatingFunctional
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Dual.Normalization
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Dual.ComplexExtension
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Dual.RieszApplication
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Dual.Forward

-- GNS for *-algebras
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.NullSpace
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Quotient
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.PreRep
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Star
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Bounded
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Completion
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.CompleteSpace
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Extension
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.CyclicIdentity
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Constrained

-- Complexification
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Complexify
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.ComplexifyInner
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.ComplexifyMap
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.ComplexifyGNS
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.StarComplex
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.ExtensionComplex

-- Representations
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Representation.VectorState
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Representation.Constrained
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Representation.GNSConstrained

-- Main theorem
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Main.DualCharacterization
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.Main.Theorem
