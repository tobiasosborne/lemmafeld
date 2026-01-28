/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.Transitivity.Lemma05
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma10
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5
import Mathlib.GroupTheory.GroupAction.Primitive

/-!
# Lemma 11: Primitivity of H on Omega

If n + k + m ≥ 1, then H acts primitively on Ω.

## Main Results

* `lemma11_H_isPrimitive` - H acts primitively on Omega when n + k + m ≥ 1

## Proof Structure

This is a direct application of three established results:
1. **Transitivity (Lemma 5)**: H acts transitively on Ω via support graph connectivity
2. **No non-trivial blocks (Lemma 11.5)**: H admits no non-trivial block system
3. **Primitivity criterion (Lemma 10)**: Transitive + trivial blocks only → primitive

## Reference

See `examples/lemmas/lemma11_primitivity.md` for the natural language proof.
-/

namespace LemmaFeld.GroupTheory.AF.Primitivity

open MulAction Equiv.Perm Set
open scoped Pointwise

variable {n k m : ℕ}

/-- H acts transitively on Omega (from Lemma 5) -/
theorem H_transitive (n k m : ℕ) :
    IsPretransitive (H n k m) (Omega n k m) :=
  LemmaFeld.GroupTheory.AF.Transitivity.H_isPretransitive n k m

/-- Omega has at least 2 elements when 6 + n + k + m ≥ 2 (always true) -/
instance omega_nontrivial (n k m : ℕ) : Nontrivial (Omega n k m) := by
  have h : 6 + n + k + m ≥ 2 := by omega
  exact Fin.nontrivial_iff_two_le.mpr h

-- Helper: subgroup smul equals perm image
private lemma H_smul_eq_image (h : H n k m) (B : Set (Omega n k m)) :
    h • B = (h : Equiv.Perm (Omega n k m)) '' B := by
  ext x; simp only [mem_smul_set_iff_inv_smul_mem, mem_image]
  constructor
  · intro hx; exact ⟨h⁻¹ • x, hx, by simp [Subgroup.smul_def, Equiv.Perm.smul_def]⟩
  · rintro ⟨y, hy, hyx⟩; simp only [Subgroup.smul_def, Equiv.Perm.smul_def] at hyx ⊢
    simp [← hyx, hy]

-- Helper: non-trivial blocks are nonempty
private lemma nontrivial_block_nonempty {B : Set (Omega n k m)} (hNT : ¬IsTrivialBlock B) :
    B.Nonempty := by
  by_contra h; apply hNT; left
  simp only [not_nonempty_iff_eq_empty] at h; rw [h]; exact subsingleton_empty

-- Helper: non-trivial block has proper size
private lemma nontrivial_block_size {B : Set (Omega n k m)} (hNT : ¬IsTrivialBlock B) :
    1 < B.ncard ∧ B.ncard < 6 + n + k + m := by
  constructor
  · by_contra h; push_neg at h; apply hNT; left
    intro a ha b hb; exact (ncard_le_one_iff (toFinite B)).mp h ha hb
  · by_contra h; push_neg at h; apply hNT; right
    have hB : B.ncard = (univ : Set (Omega n k m)).ncard := le_antisymm
      (ncard_le_ncard (subset_univ B)) (by convert h; simp [ncard_univ, Fintype.card_fin])
    exact eq_of_subset_of_ncard_le (subset_univ B) (by rw [hB])

-- The set of H-translates as image-based definition
private def blockSystemBlocks (B : Set (Omega n k m)) : Set (Set (Omega n k m)) :=
  { C | ∃ h : H n k m, C = (h : Equiv.Perm (Omega n k m)) '' B }

-- Block system equals smul-based range
private lemma blockSystemBlocks_eq_range (B : Set (Omega n k m)) :
    blockSystemBlocks B = range (fun h : H n k m => h • B) := by
  ext C; simp only [blockSystemBlocks, mem_setOf_eq, mem_range]
  constructor
  · rintro ⟨h, hC⟩; exact ⟨h, by rw [H_smul_eq_image, hC]⟩
  · rintro ⟨h, hC⟩; exact ⟨h, by rw [← hC, H_smul_eq_image]⟩

-- Partition property from mathlib's IsBlock.isBlockSystem
private lemma blockSystemBlocks_isPartition {B : Set (Omega n k m)}
    (hB : IsBlock (H n k m) B) (hBne : B.Nonempty) :
    (blockSystemBlocks B).PairwiseDisjoint id ∧ ⋃₀ (blockSystemBlocks B) = univ := by
  rw [blockSystemBlocks_eq_range]
  haveI : IsPretransitive (H n k m) (Omega n k m) := H_transitive n k m
  have hBS := hB.isBlockSystem hBne
  exact ⟨hBS.1.pairwiseDisjoint, hBS.1.sUnion_eq_univ⟩

-- All blocks have same ncard
private lemma blockSystemBlocks_allSameSize {B : Set (Omega n k m)} :
    ∀ C ∈ blockSystemBlocks B, C.ncard = B.ncard := by
  intro C hC
  simp only [blockSystemBlocks, mem_setOf_eq] at hC
  obtain ⟨h, rfl⟩ := hC
  exact ncard_image_of_injective B (Equiv.injective (h : Equiv.Perm (Omega n k m)))

-- Generators preserve the block system
private lemma blockSystemBlocks_invariant (B : Set (Omega n k m))
    (g : Equiv.Perm (Omega n k m)) (hg : g ∈ H n k m) :
    BlockSystemInvariant g (blockSystemBlocks B) := by
  intro C hC
  simp only [blockSystemBlocks, mem_setOf_eq] at hC ⊢
  obtain ⟨h, rfl⟩ := hC
  exact ⟨⟨g * ↑h, Subgroup.mul_mem _ hg h.2⟩, by simp [image_image]⟩

/-- Convert a non-trivial IsBlock to a BlockSystemOn. -/
theorem block_to_system (_hne : n + k + m ≥ 1)
    {B : Set (Omega n k m)} (hB : IsBlock (H n k m) B) (hNT : ¬IsTrivialBlock B) :
    ∃ BS : BlockSystemOn n k m, IsHInvariant BS ∧ IsNontrivial BS := by
  let BS : BlockSystemOn n k m := {
    blocks := blockSystemBlocks B
    blockSize := B.ncard
    isPartition := blockSystemBlocks_isPartition hB (nontrivial_block_nonempty hNT)
    allSameSize := blockSystemBlocks_allSameSize }
  refine ⟨BS, ⟨?_, ?_, ?_⟩, nontrivial_block_size hNT⟩
  · exact blockSystemBlocks_invariant B (g₁ n k m) (g₁_mem_H n k m)
  · exact blockSystemBlocks_invariant B (g₂ n k m) (g₂_mem_H n k m)
  · exact blockSystemBlocks_invariant B (g₃ n k m) (g₃_mem_H n k m)

/-- When n + k + m ≥ 1, all H-blocks on Omega are trivial.
    Uses Lemma 11.5: no non-trivial block system exists. -/
theorem H_blocks_trivial (h : n + k + m ≥ 1) :
    ∀ B : Set (Omega n k m), IsBlock (H n k m) B → IsTrivialBlock B := by
  intro B hB; by_contra hNT
  obtain ⟨BS, hInv, hBSnt⟩ := block_to_system h hB hNT
  exact lemma11_5_no_nontrivial_blocks h BS hInv hBSnt

/-- **Lemma 11**: If n + k + m ≥ 1, H acts primitively on Ω.
    Combines Lemma 5 (transitivity), Lemma 10 (criterion), Lemma 11.5 (no blocks). -/
theorem lemma11_H_isPrimitive (h : n + k + m ≥ 1) :
    IsPreprimitive (H n k m) (Omega n k m) := by
  haveI : IsPretransitive (H n k m) (Omega n k m) := H_transitive n k m
  rw [lemma10_primitivity_criterion (H n k m)]; exact H_blocks_trivial h

/-- Alternative: H-blocks trivial → H primitive -/
theorem H_primitive_of_trivial_blocks (_h : n + k + m ≥ 1) :
    (∀ B : Set (Omega n k m), IsBlock (H n k m) B → IsTrivialBlock B) →
    IsPreprimitive (H n k m) (Omega n k m) := by
  intro hTriv; haveI : IsPretransitive (H n k m) (Omega n k m) := H_transitive n k m
  rw [lemma10_primitivity_criterion (H n k m)]; exact hTriv

/-- Maximal stabilizers: For primitive H, point stabilizers are maximal -/
theorem H_stabilizers_maximal (h : n + k + m ≥ 1) (x : Omega n k m) :
    IsCoatom (stabilizer (H n k m) x) := by
  haveI : IsPretransitive (H n k m) (Omega n k m) := H_transitive n k m
  exact (primitivity_iff_maximal_stabilizer (H n k m) x).mp (lemma11_H_isPrimitive h)

/-- No proper intermediate subgroups between stabilizers and H -/
theorem H_no_intermediate_subgroups (h : n + k + m ≥ 1) (x : Omega n k m)
    (K : Subgroup (H n k m)) :
    stabilizer (H n k m) x ≤ K → K = stabilizer (H n k m) x ∨ K = ⊤ := by
  intro hLe; have hMax := H_stabilizers_maximal h x
  by_cases hK : K = ⊤
  · exact Or.inr hK
  · left; exact (hMax.le_iff_eq hK).mp hLe

end LemmaFeld.GroupTheory.AF.Primitivity
