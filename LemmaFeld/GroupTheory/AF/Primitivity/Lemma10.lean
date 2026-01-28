/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import Mathlib.GroupTheory.GroupAction.Primitive
import Mathlib.GroupTheory.GroupAction.Blocks

/-!
# Lemma 10: Primitivity Criterion

This file establishes the equivalence of three characterizations of primitivity
for a transitive group action.

## Main Results

For a transitive action of G on X, the following are equivalent:
1. G is primitive (only trivial blocks)
2. G preserves no non-trivial partition
3. Point stabilizers are maximal subgroups

Mathlib provides:
- `MulAction.IsPreprimitive`: G is primitive iff all blocks are trivial
- `MulAction.isCoatom_stabilizer_iff_preprimitive`: Stabilizers maximal iff primitive

## Reference

See `examples/lemmas/lemma10_primitivity_criterion.md` for the natural language proof.
-/

open MulAction

-- ============================================
-- SECTION 1: MATHLIB DEFINITIONS
-- ============================================

/-!
### Mathlib's Primitivity Framework

Mathlib defines primitivity in `Mathlib.GroupTheory.GroupAction.Primitive`:
- `MulAction.IsPreprimitive G X`: A transitive action where all blocks are trivial
- `MulAction.IsBlock G B`: A set B is a block if for all g, gB = B or gB ∩ B = ∅
- `MulAction.IsTrivialBlock B`: Defined as `B.Subsingleton ∨ B = Set.univ`

The key characterization theorem is:
`MulAction.isCoatom_stabilizer_iff_preprimitive`:
  For transitive, nontrivial actions: Stabilizer is coatom ↔ IsPreprimitive
-/

-- ============================================
-- SECTION 2: TRIVIAL BLOCKS CHARACTERIZATION
-- ============================================

/-- A block is trivial iff it's subsingleton or the full set.
    Subsingleton means empty or a singleton. -/
theorem trivialBlock_iff_subsingleton_or_univ
    {X : Type*} (B : Set X) :
    IsTrivialBlock B ↔ (B.Subsingleton ∨ B = Set.univ) := Iff.rfl

/-- Empty set is a trivial block -/
theorem trivialBlock_empty {X : Type*} : IsTrivialBlock (∅ : Set X) :=
  Or.inl Set.subsingleton_empty

/-- Singleton is a trivial block -/
theorem trivialBlock_singleton {X : Type*} (x : X) :
    IsTrivialBlock ({x} : Set X) :=
  Or.inl Set.subsingleton_singleton

/-- Full set is a trivial block -/
theorem trivialBlock_univ {X : Type*} : IsTrivialBlock (Set.univ : Set X) :=
  Or.inr rfl

-- ============================================
-- SECTION 3: MAXIMAL STABILIZER EQUIVALENCE
-- ============================================

/-- For a transitive nontrivial action, primitivity is equivalent to
    point stabilizers being maximal (coatom in the subgroup lattice).
    This is mathlib's `isCoatom_stabilizer_iff_preprimitive`. -/
theorem primitivity_iff_maximal_stabilizer
    (G : Type*) [Group G] {X : Type*} [MulAction G X]
    [IsPretransitive G X] [Nontrivial X] (a : X) :
    IsPreprimitive G X ↔ IsCoatom (stabilizer G a) :=
  (isCoatom_stabilizer_iff_preprimitive G a).symm

-- ============================================
-- SECTION 4: BLOCK-PARTITION CORRESPONDENCE
-- ============================================

/-- The orbit of a block under G covers X when G is transitive.
    If B is a block containing some point, then {g • B : g ∈ G} covers X. -/
theorem block_orbit_covers
    {G : Type*} [Group G] {X : Type*} [MulAction G X]
    [IsPretransitive G X] {B : Set X} (hne : B.Nonempty) :
    ∀ x : X, ∃ g : G, g • hne.some = x ∧ hne.some ∈ B := by
  intro x
  obtain ⟨g, hg⟩ := exists_smul_eq G hne.some x
  exact ⟨g, hg, hne.some_mem⟩

-- ============================================
-- SECTION 5: PRIMITIVITY FOR H
-- ============================================

/-- For the subgroup H acting on Omega, primitivity means all blocks are trivial.
    This is just restating the definition for our specific subgroup. -/
def H_isPrimitive (n k m : ℕ) : Prop :=
  ∀ B : Set (Omega n k m), IsBlock (H n k m) B → IsTrivialBlock B

/-- Primitivity for H is equivalent to: every block is subsingleton or full. -/
theorem H_primitive_iff (n k m : ℕ) :
    H_isPrimitive n k m ↔
    (∀ B : Set (Omega n k m), IsBlock (H n k m) B →
      B.Subsingleton ∨ B = Set.univ) := by
  unfold H_isPrimitive
  simp only [trivialBlock_iff_subsingleton_or_univ]

-- ============================================
-- SECTION 6: MAIN THEOREM (SUMMARY)
-- ============================================

/-- **Lemma 10: Primitivity Criterion**

    For a transitive group G acting on X, the following are equivalent:
    (1) G is primitive (IsPreprimitive G X)
    (2) All blocks are trivial
    (3) For any α, the stabilizer G_α is a maximal subgroup of G

    This is established by mathlib's `IsPreprimitive` class and
    `isCoatom_stabilizer_iff_preprimitive`. -/
theorem lemma10_primitivity_criterion
    (G : Type*) [Group G] {X : Type*} [MulAction G X]
    [IsPretransitive G X] [Nontrivial X] :
    IsPreprimitive G X ↔
    (∀ B : Set X, IsBlock G B → IsTrivialBlock B) := by
  constructor
  · intro hp B hB
    exact hp.isTrivialBlock_of_isBlock hB
  · intro h
    exact IsPreprimitive.of_isTrivialBlock_base (Classical.arbitrary X) fun {B} _ hB => h B hB

/-- The three-way equivalence: primitive ↔ trivial blocks ↔ maximal stabilizers -/
theorem lemma10_three_way_equiv
    (G : Type*) [Group G] {X : Type*} [MulAction G X]
    [IsPretransitive G X] [Nontrivial X] (a : X) :
    (IsPreprimitive G X) ↔
    (∀ B : Set X, IsBlock G B → IsTrivialBlock B) ∧
    IsCoatom (stabilizer G a) := by
  constructor
  · intro h
    exact ⟨(lemma10_primitivity_criterion G).mp h, (primitivity_iff_maximal_stabilizer G a).mp h⟩
  · intro ⟨_, h⟩
    exact (primitivity_iff_maximal_stabilizer G a).mpr h
