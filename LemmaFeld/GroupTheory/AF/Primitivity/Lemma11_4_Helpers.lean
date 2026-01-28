/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_4_Period
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Fintype.Card

/-!
# Lemma 11.4: Block Orbit - Helper Lemmas

Helper lemmas for proving the support intersection cardinality result.
-/

open Equiv Equiv.Perm Set MulAction
open scoped Pointwise

variable {α : Type*} [DecidableEq α] [Fintype α]

-- ============================================
-- BLOCK ORBIT SUBSET BLOCKS
-- ============================================

/-- Positive powers preserve block membership -/
lemma pow_image_mem_blocks {σ : Perm α} {B : Set α} {Blocks : Set (Set α)}
    (hInv : BlockSystemInvariant σ Blocks) (hB : B ∈ Blocks) (n : ℕ) :
    (σ ^ n) '' B ∈ Blocks := by
  induction n with
  | zero => simpa
  | succ n ih =>
    rw [pow_succ', Perm.coe_mul, Set.image_comp]
    exact hInv _ ih

/-- Inverse preserves block membership (finiteness argument) -/
lemma inv_image_mem_blocks {σ : Perm α} {Blocks : Set (Set α)}
    (hInv : BlockSystemInvariant σ Blocks) (hFin : Blocks.Finite)
    {B : Set α} (hB : B ∈ Blocks) :
    σ.symm '' B ∈ Blocks := by
  let f : Blocks → Blocks := fun ⟨b, hb⟩ => ⟨σ '' b, hInv b hb⟩
  have hInj : Function.Injective f := by
    intro ⟨b1, hb1⟩ ⟨b2, hb2⟩ heq
    -- f ⟨b1, hb1⟩ = f ⟨b2, hb2⟩ means ⟨σ '' b1, _⟩ = ⟨σ '' b2, _⟩
    simp only [f, Subtype.mk.injEq] at heq
    -- heq : σ '' b1 = σ '' b2
    simp only [Subtype.mk.injEq]
    ext x
    constructor
    · intro hx
      have h1 : σ x ∈ σ '' b1 := Set.mem_image_of_mem σ hx
      rw [heq] at h1
      obtain ⟨y, hy, heqy⟩ := h1
      rwa [← σ.injective heqy]
    · intro hx
      have h1 : σ x ∈ σ '' b2 := Set.mem_image_of_mem σ hx
      rw [← heq] at h1
      obtain ⟨y, hy, heqy⟩ := h1
      rwa [← σ.injective heqy]
  haveI : Finite Blocks := hFin
  have hSurj := Finite.surjective_of_injective hInj
  obtain ⟨⟨C, hC⟩, hfC⟩ := hSurj ⟨B, hB⟩
  simp only [f, Subtype.mk.injEq] at hfC
  -- hfC : σ '' C = B
  convert hC using 1
  ext y
  simp only [mem_image]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← hfC] at hx
    obtain ⟨z, hz, hzeq⟩ := hx
    convert hz using 1
    rw [← hzeq, Equiv.symm_apply_apply]
  · intro hy
    exact ⟨σ y, by rw [← hfC]; exact mem_image_of_mem σ hy, Equiv.symm_apply_apply σ y⟩

/-- Inverse powers preserve block membership -/
lemma inv_pow_image_mem_blocks {σ : Perm α} {B : Set α} {Blocks : Set (Set α)}
    (hInv : BlockSystemInvariant σ Blocks) (hFin : Blocks.Finite)
    (hB : B ∈ Blocks) (n : ℕ) :
    (σ.symm ^ n) '' B ∈ Blocks := by
  induction n with
  | zero => simpa
  | succ n ih =>
    rw [pow_succ', Perm.coe_mul, Set.image_comp]
    exact inv_image_mem_blocks hInv hFin ih

/-- Integer powers preserve block membership -/
lemma zpow_image_mem_blocks {σ : Perm α} {B : Set α} {Blocks : Set (Set α)}
    (hInv : BlockSystemInvariant σ Blocks) (hFin : Blocks.Finite)
    (hB : B ∈ Blocks) (k : ℤ) :
    (σ ^ k) '' B ∈ Blocks := by
  rcases k with (n | n)
  · simp only [Int.ofNat_eq_coe, zpow_natCast]
    exact pow_image_mem_blocks hInv hB n
  · have heq : (σ ^ Int.negSucc n : Perm α) = σ.symm ^ (n + 1) := by
      simp only [zpow_negSucc]
      rfl
    rw [heq]
    exact inv_pow_image_mem_blocks hInv hFin hB (n + 1)

/-- Block orbit is contained in the block system -/
theorem blockOrbit_subset_blocks {σ : Perm α} {B : Set α} {Blocks : Set (Set α)}
    (hInv : BlockSystemInvariant σ Blocks) (hFin : Blocks.Finite)
    (hB : B ∈ Blocks) :
    blockOrbit σ B ⊆ Blocks := fun _ hC => by
  obtain ⟨k, rfl⟩ := hC
  exact zpow_image_mem_blocks hInv hFin hB k

-- ============================================
-- ORBIT INTERSECTIONS DISJOINTNESS
-- ============================================

/-- Orbit intersections with support are pairwise disjoint -/
theorem orbit_intersections_pairwise_disjoint {σ : Perm α} {B : Set α} {Blocks : Set (Set α)}
    (hInv : BlockSystemInvariant σ Blocks) (hFin : Blocks.Finite)
    (hB : B ∈ Blocks) (hDisj : Blocks.PairwiseDisjoint id) :
    (blockOrbit σ B).PairwiseDisjoint (fun C => C ∩ (σ.support : Set α)) := by
  intro C1 hC1 C2 hC2 hne
  have h1 : C1 ∈ Blocks := blockOrbit_subset_blocks hInv hFin hB hC1
  have h2 : C2 ∈ Blocks := blockOrbit_subset_blocks hInv hFin hB hC2
  simp only [Function.onFun]
  exact Disjoint.mono inter_subset_left inter_subset_left (hDisj h1 h2 hne)
