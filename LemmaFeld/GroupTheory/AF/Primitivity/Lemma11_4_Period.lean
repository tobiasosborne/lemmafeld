/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_4_Defs
import Mathlib.GroupTheory.GroupAction.Period
import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
import Mathlib.Data.ZMod.QuotientGroup

/-!
# Lemma 11.4: Block Orbit - Period Machinery

Connects block orbit size to MulAction periods and proves divisibility.

## Main Results

* `block_orbit_divides_cycle_length`: The orbit size r divides the cycle length ℓ
* `blockOrbitSize_eq_setPeriod`: Orbit size equals the period of σ acting on B
-/

open Equiv Equiv.Perm Set MulAction
open scoped Pointwise

variable {α : Type*} [DecidableEq α] [Fintype α]

-- ============================================
-- CYCLE LENGTH AND ZPOWERS
-- ============================================

/-- For a cycle, the cyclic subgroup has order equal to the cycle length -/
theorem zpowers_card_eq_cycle_length {σ : Perm α} (hσ : σ.IsCycle) :
    Nat.card (Subgroup.zpowers σ) = cycleLength σ := by
  simp only [cycleLength, Nat.card_eq_fintype_card, Fintype.card_zpowers]
  exact hσ.orderOf

/-- The pointwise action: σ • B = σ '' B for permutations acting on sets -/
theorem perm_smul_set_eq_image (σ : Perm α) (B : Set α) : σ • B = σ '' B := by
  ext x
  simp only [Set.mem_smul_set, Set.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, Perm.smul_def σ y⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (Perm.smul_def σ y).symm⟩

/-- The orbit under zpowers is exactly the block orbit -/
theorem blockOrbit_eq_orbit (σ : Perm α) (B : Set α) :
    blockOrbit σ B = { C | ∃ k : ℤ, C = σ ^ k • B } := by
  ext C
  simp only [blockOrbit, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, rfl⟩
    use k
    rw [perm_smul_set_eq_image]
  · rintro ⟨k, rfl⟩
    use k
    rw [perm_smul_set_eq_image]

-- ============================================
-- PERIOD MACHINERY
-- ============================================

/-- The period of σ acting on a set B (via pointwise action) -/
noncomputable def setPeriod (σ : Perm α) (B : Set α) : ℕ := MulAction.period σ B

/-- Period divides orderOf for permutation action on sets -/
theorem setPeriod_dvd_orderOf (σ : Perm α) (B : Set α) : setPeriod σ B ∣ orderOf σ :=
  MulAction.period_dvd_orderOf σ B

/-- blockOrbit equals the MulAction orbit under zpowers -/
theorem blockOrbit_eq_MulAction_orbit (σ : Perm α) (B : Set α) :
    blockOrbit σ B = (MulAction.orbit (Subgroup.zpowers σ) B : Set (Set α)) := by
  ext C
  rw [blockOrbit_eq_orbit]
  simp only [MulAction.mem_orbit_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨⟨σ ^ k, ⟨k, rfl⟩⟩, rfl⟩
  · rintro ⟨⟨_, ⟨k, rfl⟩⟩, rfl⟩
    exact ⟨k, rfl⟩

/-- Orbit ncard equals period via minimalPeriod relationship -/
theorem orbit_ncard_eq_period (σ : Perm α) (B : Set α) :
    (MulAction.orbit (Subgroup.zpowers σ) B : Set (Set α)).ncard = MulAction.period σ B := by
  rw [MulAction.period_eq_minimalPeriod]
  haveI : Fintype (Set α) := Set.fintype
  haveI : Fintype ↑(MulAction.orbit (↥(Subgroup.zpowers σ)) B) := Fintype.ofFinite _
  rw [Set.ncard_eq_toFinset_card', Set.toFinset_card, MulAction.minimalPeriod_eq_card]

/-- The orbit size equals the period -/
theorem blockOrbitSize_eq_setPeriod {σ : Perm α} (hσ : σ.IsCycle) (B : Set α) :
    blockOrbitSize σ B = setPeriod σ B := by
  unfold blockOrbitSize setPeriod
  rw [blockOrbit_eq_MulAction_orbit, orbit_ncard_eq_period]

-- ============================================
-- MAIN DIVISIBILITY RESULT
-- ============================================

/-- **Block orbit divides cycle length**

    If σ is a cycle and B is a block with B ∩ supp(σ) ≠ ∅ in a σ-invariant
    block system, then the orbit size r divides the cycle length ℓ. -/
theorem block_orbit_divides_cycle_length {σ : Perm α} (hσ : σ.IsCycle)
    {B : Set α} {Blocks : Set (Set α)} (_hInv : BlockSystemInvariant σ Blocks)
    (_hB : B ∈ Blocks) (_hMeet : (B ∩ (σ.support : Set α)).Nonempty) :
    blockOrbitSize σ B ∣ cycleLength σ := by
  rw [blockOrbitSize_eq_setPeriod hσ]
  calc setPeriod σ B ∣ orderOf σ := setPeriod_dvd_orderOf σ B
    _ = cycleLength σ := by unfold cycleLength; exact hσ.orderOf
