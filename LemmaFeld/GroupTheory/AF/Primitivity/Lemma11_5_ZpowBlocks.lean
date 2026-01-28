/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_4_Helpers
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_OrbitContinuation

/-!
# Lemma 11.5: Zpow Block Preservation for Generators

Specialized lemmas for proving that g₁^j, g₂^j, g₃^j preserve block membership
for j : ℤ. These are thin wrappers around the generic `zpow_image_mem_blocks`
from `Lemma11_4_Helpers.lean`.

## Main Results

* `g₁_zpow_preserves_blocks`: g₁^j '' B ∈ BS.blocks
* `g₂_zpow_preserves_blocks`: g₂^j '' B ∈ BS.blocks
* `g₃_zpow_preserves_blocks`: g₃^j '' B ∈ BS.blocks

These are used in Case 2 of Lemma 11.5 where we have B' = g₁^j '' B from
the orbit membership argument, and need to establish B' ∈ BS.blocks.
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

-- ============================================
-- SECTION 1: SPECIALIZED ZPOW FOR GENERATORS
-- ============================================

/-- g₁^j preserves block membership -/
theorem g₁_zpow_preserves_blocks (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS)
    (B : Set (Omega n k m)) (hB : B ∈ BS.blocks) (j : ℤ) :
    (g₁ n k m ^ j) '' B ∈ BS.blocks := by
  have hBSInv := g₁_block_system_invariant BS hInv
  have hFin : BS.blocks.Finite := Set.toFinite _
  exact zpow_image_mem_blocks hBSInv hFin hB j

/-- g₂^j preserves block membership -/
theorem g₂_zpow_preserves_blocks (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS)
    (B : Set (Omega n k m)) (hB : B ∈ BS.blocks) (j : ℤ) :
    (g₂ n k m ^ j) '' B ∈ BS.blocks := by
  have hBSInv : BlockSystemInvariant (g₂ n k m) BS.blocks := fun b hb => hInv.2.1 b hb
  have hFin : BS.blocks.Finite := Set.toFinite _
  exact zpow_image_mem_blocks hBSInv hFin hB j

/-- g₃^j preserves block membership -/
theorem g₃_zpow_preserves_blocks (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS)
    (B : Set (Omega n k m)) (hB : B ∈ BS.blocks) (j : ℤ) :
    (g₃ n k m ^ j) '' B ∈ BS.blocks := by
  have hBSInv : BlockSystemInvariant (g₃ n k m) BS.blocks := fun b hb => hInv.2.2 b hb
  have hFin : BS.blocks.Finite := Set.toFinite _
  exact zpow_image_mem_blocks hBSInv hFin hB j
