/-
  LemmaFeld.GroupTheory.AF - Root module for the AF formalization

  This module re-exports all components of the formalization proving:
  H = ⟨g₁, g₂, g₃⟩ equals Aₙ (if n,k,m all odd) or Sₙ (otherwise)
  for Ω = Fin(6+n+k+m).

  ## Structure

  - Core: Fundamental definitions (Omega, Generators, GroupH, Blocks)
  - BaseCase: Lemmas 1-4 (base case n=k=m=0)
  - Transitivity: Lemma 5 (H acts transitively)
  - ThreeCycle: Lemmas 6-9 (commutators and 3-cycle extraction)
  - Primitivity: Lemmas 10-11 (H acts primitively when n+k+m≥1)
  - SignAnalysis: Lemmas 12-15 (Jordan, sign, parity, classification)
  - MainTheorem: Final result combining all lemmas
-/

-- ============================================
-- CORE DEFINITIONS
-- ============================================
import LemmaFeld.GroupTheory.AF.Core

-- ============================================
-- BASE CASE (Lemmas 1-4)
-- ============================================
import LemmaFeld.GroupTheory.AF.BaseCase.Lemma01
import LemmaFeld.GroupTheory.AF.BaseCase.Lemma02
import LemmaFeld.GroupTheory.AF.BaseCase.Lemma03
import LemmaFeld.GroupTheory.AF.BaseCase.Lemma04

-- ============================================
-- TRANSITIVITY (Lemma 5)
-- ============================================
import LemmaFeld.GroupTheory.AF.Transitivity.Lemma05

-- ============================================
-- THREE-CYCLE EXTRACTION (Lemmas 6-9)
-- ============================================
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma06
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma07
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma08
import LemmaFeld.GroupTheory.AF.ThreeCycle.Lemma09

-- ============================================
-- PRIMITIVITY (Lemmas 10-11)
-- ============================================
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma10
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_1
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_2
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_3
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_4
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11

-- ============================================
-- SIGN ANALYSIS (Lemmas 12-15)
-- ============================================
import LemmaFeld.GroupTheory.AF.SignAnalysis.Lemma12
import LemmaFeld.GroupTheory.AF.SignAnalysis.Lemma13
import LemmaFeld.GroupTheory.AF.SignAnalysis.Lemma14
import LemmaFeld.GroupTheory.AF.SignAnalysis.Lemma15

-- ============================================
-- MAIN THEOREM
-- ============================================
import LemmaFeld.GroupTheory.AF.MainTheorem
