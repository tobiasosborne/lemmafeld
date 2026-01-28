/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_2
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_3
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_4
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_FixedPoints
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_CycleSupport
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_Cases
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_SupportCover
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_Case2
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_Defs
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_SymmetricDefs
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_CaseB
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_CaseC

/-!
# Lemma 11.5: No Non-trivial Blocks

If n + k + m ≥ 1, then H admits no non-trivial block system on Ω.
See `examples/lemmas/lemma11_5_no_nontrivial_blocks.md` for the full proof outline.
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

/-- **Lemma 11.5**: If n + k + m ≥ 1, H admits no non-trivial block system on Ω. -/
theorem lemma11_5_no_nontrivial_blocks (h : n + k + m ≥ 1) :
    ∀ BS : BlockSystemOn n k m, IsHInvariant BS → ¬IsNontrivial BS := by
  intro BS hInv hNT; obtain ⟨hInv₁, hInv₂, hInv₃⟩ := hInv; obtain ⟨hDisj, hCover⟩ := BS.isPartition
  by_cases hn : n ≥ 1
  · -- Case: n ≥ 1. Let B be the block containing a₁
    -- Since BS.blocks covers Ω, there exists a block B containing a₁
    have ha₁_in_univ : a₁ n k m hn ∈ (Set.univ : Set (Omega n k m)) := Set.mem_univ _
    rw [← hCover] at ha₁_in_univ
    obtain ⟨B, hB_mem, ha₁_in_B⟩ := Set.mem_sUnion.mp ha₁_in_univ
    -- For any block in an H-invariant system, generator images are either equal or disjoint
    have hDichotomy₁ := perm_image_preserves_or_disjoint (g₁ n k m) B BS.blocks hDisj hB_mem
      (hInv₁ B hB_mem)
    have hDichotomy₂ := perm_image_preserves_or_disjoint (g₂ n k m) B BS.blocks hDisj hB_mem
      (hInv₂ B hB_mem)
    have hDichotomy₃ := perm_image_preserves_or_disjoint (g₃ n k m) B BS.blocks hDisj hB_mem
      (hInv₃ B hB_mem)
    -- Case 1: g₁(B) = B
    rcases hDichotomy₁ with hg₁_pres | hg₁_disj
    · -- Case 1: g₁ preserves B
      -- By Lemma 11.3, supp(g₁) ⊆ B
      have hSupp₁ : (↑(g₁ n k m).support : Set _) ⊆ B := by
        have hMeet : containsA₁ B hn := ha₁_in_B
        exact lemma11_3_tail_in_block hn B hMeet hg₁_pres
      -- Sub-case: g₂(B) = B vs g₂(B) ≠ B
      rcases hDichotomy₂ with hg₂_pres | hg₂_disj
      · -- Case 1a: g₂ also preserves B
        -- Element 0 ∈ supp(g₁) ⊆ B
        have h0_in_B : (⟨0, by omega⟩ : Omega n k m) ∈ B := hSupp₁ elem0_in_support_g₁
        -- Since 0 ∈ supp(g₂), and g₂(B) = B, by Lemma 11.2, supp(g₂) ⊆ B
        have hSupp₂ : (↑(g₂ n k m).support : Set _) ⊆ B := by
          have hMeet : (↑(g₂ n k m).support ∩ B).Nonempty :=
            ⟨⟨0, by omega⟩, elem0_in_support_g₂, h0_in_B⟩
          have hCyc := g₂_isCycle n k m
          exact (cycle_support_subset_or_disjoint hCyc hg₂_pres).resolve_right
            (fun hDisj' => Set.not_nonempty_iff_eq_empty.mpr
              (Set.disjoint_iff_inter_eq_empty.mp hDisj') hMeet)
        -- Sub-sub-case: g₃(B) = B vs g₃(B) ≠ B
        rcases hDichotomy₃ with hg₃_pres | hg₃_disj
        · -- Case 1a-i: g₃ also preserves B
          -- By Lemma 11.2, supp(g₃) ⊆ B (since element 1 ∈ supp(g₂) ⊆ B is also in supp(g₃))
          have hSupp₃ : (↑(g₃ n k m).support : Set _) ⊆ B := by
            -- Element 1 is in supp(g₂) ⊆ B, and also in supp(g₃)
            have h1_in_B : (⟨1, by omega⟩ : Omega n k m) ∈ B := hSupp₂ elem1_in_support_g₂
            have hMeet : (↑(g₃ n k m).support ∩ B).Nonempty :=
              ⟨⟨1, by omega⟩, elem1_in_support_g₃, h1_in_B⟩
            have hCyc := g₃_isCycle n k m
            exact (cycle_support_subset_or_disjoint hCyc hg₃_pres).resolve_right
              (fun hDisj' => Set.not_nonempty_iff_eq_empty.mpr
                (Set.disjoint_iff_inter_eq_empty.mp hDisj') hMeet)
          -- Now B contains all three supports, so B = Ω
          have hB_eq_univ := case1a_i_supports_cover_univ B hSupp₁ hSupp₂ hSupp₃
          -- This means |B| = |Ω| = 6 + n + k + m, contradicting non-triviality
          have hBS_eq : BS.blockSize = 6 + n + k + m := by
            have hCard := BS.allSameSize B hB_mem
            rw [hB_eq_univ] at hCard
            simp only [Set.ncard_univ, Omega, Nat.card_eq_fintype_card, Fintype.card_fin] at hCard
            exact hCard.symm
          -- Non-triviality requires blockSize < 6 + n + k + m
          exact Nat.lt_irrefl _ (hBS_eq ▸ hNT.2)
        · -- Case 1a-ii: g₃ does not preserve B (disjoint)
          -- Element 0 ∈ supp(g₁) ⊆ B, and g₃ fixes 0 (not in supp(g₃))
          exact case1a_ii_impossible B h0_in_B hg₃_disj
      · -- Case 1b: g₂ does not preserve B (disjoint)
        exact case1b_impossible hn B hSupp₁ hg₂_disj
    · -- Case 2: g₁ does not preserve B (disjoint)
      -- By fixed-point argument, g₂ and g₃ must preserve B
      have hDisj₂ : ¬PreservesSet (g₂ n k m) B → Disjoint (g₂ n k m '' B) B := by
        intro hNot; exact hDichotomy₂.resolve_left hNot
      have hDisj₃ : ¬PreservesSet (g₃ n k m) B → Disjoint (g₃ n k m '' B) B := by
        intro hNot; exact hDichotomy₃.resolve_left hNot
      obtain ⟨hg₂_pres, hg₃_pres⟩ := case2_forces_stabilization hn B ha₁_in_B hDisj₂ hDisj₃
      have hSize_lower : 1 < BS.blockSize := hNT.1
      have hB_size := BS.allSameSize B hB_mem
      rw [← hB_size] at hSize_lower
      -- Invoke case2_impossible (structural argument)
      exact case2_impossible hn B BS ⟨hInv₁, hInv₂, hInv₃⟩ hB_mem hg₁_disj ha₁_in_B hg₂_pres hg₃_pres hSize_lower
  · -- Case: n = 0, so k ≥ 1 or m ≥ 1. By symmetry, similar argument applies.
    push_neg at hn
    have hn0 : n = 0 := Nat.lt_one_iff.mp hn
    have hkm : k + m ≥ 1 := by omega
    by_cases hk : k ≥ 1
    · -- Case k ≥ 1: Use b₁ and g₂ (symmetric to n ≥ 1 case)
      have hb₁_in_univ : b₁ n k m hk ∈ (Set.univ : Set (Omega n k m)) := Set.mem_univ _
      rw [← hCover] at hb₁_in_univ
      obtain ⟨B, hB_mem, hb₁_in_B⟩ := Set.mem_sUnion.mp hb₁_in_univ
      have hDich₁ := perm_image_preserves_or_disjoint (g₁ n k m) B BS.blocks hDisj hB_mem (hInv₁ B hB_mem)
      have hDich₂ := perm_image_preserves_or_disjoint (g₂ n k m) B BS.blocks hDisj hB_mem (hInv₂ B hB_mem)
      have hDich₃ := perm_image_preserves_or_disjoint (g₃ n k m) B BS.blocks hDisj hB_mem (hInv₃ B hB_mem)
      rcases hDich₂ with hg₂_pres | hg₂_disj
      · -- Case 1: g₂(B) = B, so supp(g₂) ⊆ B
        have hSupp₂ := lemma11_3_tail_B_in_block hk B hb₁_in_B hg₂_pres
        rcases hDich₁ with hg₁_pres | hg₁_disj
        · -- Case 1a: g₁ also preserves B
          have h1_in_B : (⟨1, by omega⟩ : Omega n k m) ∈ B := hSupp₂ elem1_in_support_g₂
          have hSupp₁ : (↑(g₁ n k m).support : Set _) ⊆ B := by
            have hCyc := g₁_isCycle n k m (by omega); have hMeet : (↑(g₁ n k m).support ∩ B).Nonempty :=
              ⟨⟨0, by omega⟩, elem0_in_support_g₁, hSupp₂ elem0_in_support_g₂⟩
            exact (cycle_support_subset_or_disjoint hCyc hg₁_pres).resolve_right
              (fun hD => Set.not_nonempty_iff_eq_empty.mpr (Set.disjoint_iff_inter_eq_empty.mp hD) hMeet)
          rcases hDich₃ with hg₃_pres | hg₃_disj
          · -- Case 1a-i: All supports in B, so B = Ω
            have hSupp₃ : (↑(g₃ n k m).support : Set _) ⊆ B := by
              have hCyc := g₃_isCycle n k m; have hMeet : (↑(g₃ n k m).support ∩ B).Nonempty :=
                ⟨⟨1, by omega⟩, elem1_in_support_g₃, h1_in_B⟩
              exact (cycle_support_subset_or_disjoint hCyc hg₃_pres).resolve_right
                (fun hD => Set.not_nonempty_iff_eq_empty.mpr (Set.disjoint_iff_inter_eq_empty.mp hD) hMeet)
            have hB_eq := case1a_i_supports_cover_univ B hSupp₁ hSupp₂ hSupp₃
            have hBS_eq : BS.blockSize = 6 + n + k + m := by
              have hCard := BS.allSameSize B hB_mem; rw [hB_eq] at hCard
              simp only [Set.ncard_univ, Omega, Nat.card_eq_fintype_card, Fintype.card_fin] at hCard
              exact hCard.symm
            exact Nat.lt_irrefl _ (hBS_eq ▸ hNT.2)
          · -- Case 1a-ii: g₃(B) ≠ B contradicts via fixed point on element 3
            exact case1b_impossible_g₃ B hSupp₂ hg₃_disj
        · -- Case 1b: g₁(B) ≠ B contradicts via fixed point (elem 4 fixed by g₁, in supp(g₂))
          exact case1b_impossible_g₁_from_g₂ B hSupp₂ hg₁_disj
      · -- Case 2: g₂(B) ≠ B, by fixed point argument g₁, g₃ preserve B
        have hD₁ : ¬PreservesSet (g₁ n k m) B → Disjoint (g₁ n k m '' B) B := fun h => hDich₁.resolve_left h
        have hD₃ : ¬PreservesSet (g₃ n k m) B → Disjoint (g₃ n k m '' B) B := fun h => hDich₃.resolve_left h
        obtain ⟨hg₁_pres, hg₃_pres⟩ := case2_forces_stabilization_B hk B hb₁_in_B hD₁ hD₃
        have hSize := hNT.1; have hB_size := BS.allSameSize B hB_mem; rw [← hB_size] at hSize
        -- Block dichotomy for powers of g₂
        have hBlock : ∀ j : ℕ, (g₂ n k m ^ j) '' B = B ∨ Disjoint ((g₂ n k m ^ j) '' B) B :=
          fun j => perm_pow_image_preserves_or_disjoint (g₂ n k m) B BS.blocks hDisj hB_mem (hInv₂) j
        exact case2_impossible_B hk B BS ⟨hInv₁, hInv₂, hInv₃⟩ hB_mem hg₂_disj hb₁_in_B hg₁_pres hg₃_pres hBlock hSize
    · -- Case m ≥ 1: Use c₁ and g₃ (symmetric to k ≥ 1 case)
      push_neg at hk; have hm : m ≥ 1 := by omega
      have hc₁_in_univ : c₁ n k m hm ∈ (Set.univ : Set (Omega n k m)) := Set.mem_univ _
      rw [← hCover] at hc₁_in_univ
      obtain ⟨B, hB_mem, hc₁_in_B⟩ := Set.mem_sUnion.mp hc₁_in_univ
      have hDich₁ := perm_image_preserves_or_disjoint (g₁ n k m) B BS.blocks hDisj hB_mem (hInv₁ B hB_mem)
      have hDich₂ := perm_image_preserves_or_disjoint (g₂ n k m) B BS.blocks hDisj hB_mem (hInv₂ B hB_mem)
      have hDich₃ := perm_image_preserves_or_disjoint (g₃ n k m) B BS.blocks hDisj hB_mem (hInv₃ B hB_mem)
      rcases hDich₃ with hg₃_pres | hg₃_disj
      · -- Case 1: g₃(B) = B, so supp(g₃) ⊆ B
        have hSupp₃ := lemma11_3_tail_C_in_block hm B hc₁_in_B hg₃_pres
        rcases hDich₂ with hg₂_pres | hg₂_disj
        · -- Case 1a: g₂ also preserves B
          have h1_in_B : (⟨1, by omega⟩ : Omega n k m) ∈ B := hSupp₃ elem1_in_support_g₃
          have hSupp₂ : (↑(g₂ n k m).support : Set _) ⊆ B := by
            have hCyc := g₂_isCycle n k m; have hMeet : (↑(g₂ n k m).support ∩ B).Nonempty :=
              ⟨⟨1, by omega⟩, elem1_in_support_g₂, h1_in_B⟩
            exact (cycle_support_subset_or_disjoint hCyc hg₂_pres).resolve_right
              (fun hD => Set.not_nonempty_iff_eq_empty.mpr (Set.disjoint_iff_inter_eq_empty.mp hD) hMeet)
          rcases hDich₁ with hg₁_pres | hg₁_disj
          · -- Case 1a-i: All supports in B, so B = Ω
            have hSupp₁ : (↑(g₁ n k m).support : Set _) ⊆ B := by
              have hCyc := g₁_isCycle n k m (by omega); have hMeet : (↑(g₁ n k m).support ∩ B).Nonempty :=
                ⟨⟨0, by omega⟩, elem0_in_support_g₁, hSupp₂ elem0_in_support_g₂⟩
              exact (cycle_support_subset_or_disjoint hCyc hg₁_pres).resolve_right
                (fun hD => Set.not_nonempty_iff_eq_empty.mpr (Set.disjoint_iff_inter_eq_empty.mp hD) hMeet)
            have hB_eq := case1a_i_supports_cover_univ B hSupp₁ hSupp₂ hSupp₃
            have hBS_eq : BS.blockSize = 6 + n + k + m := by
              have hCard := BS.allSameSize B hB_mem; rw [hB_eq] at hCard
              simp only [Set.ncard_univ, Omega, Nat.card_eq_fintype_card, Fintype.card_fin] at hCard
              exact hCard.symm
            exact Nat.lt_irrefl _ (hBS_eq ▸ hNT.2)
          · -- Case 1a-ii: g₁(B) ≠ B contradicts via fixed point
            exact case1b_impossible_g₁ B hSupp₃ hg₁_disj
        · -- Case 1b: g₂(B) ≠ B contradicts via fixed point (elem 5 fixed by g₂, in supp(g₃))
          exact case1b_impossible_g₂_from_g₃ B hSupp₃ hg₂_disj
      · -- Case 2: g₃(B) ≠ B, by fixed point argument g₁, g₂ preserve B
        have hD₁ : ¬PreservesSet (g₁ n k m) B → Disjoint (g₁ n k m '' B) B := fun h => hDich₁.resolve_left h
        have hD₂ : ¬PreservesSet (g₂ n k m) B → Disjoint (g₂ n k m '' B) B := fun h => hDich₂.resolve_left h
        obtain ⟨hg₁_pres, hg₂_pres⟩ := case2_forces_stabilization_C hm B hc₁_in_B hD₁ hD₂
        have hSize := hNT.1; have hB_size := BS.allSameSize B hB_mem; rw [← hB_size] at hSize
        -- Block dichotomy for powers of g₃
        have hBlock : ∀ j : ℕ, (g₃ n k m ^ j) '' B = B ∨ Disjoint ((g₃ n k m ^ j) '' B) B :=
          fun j => perm_pow_image_preserves_or_disjoint (g₃ n k m) B BS.blocks hDisj hB_mem (hInv₃) j
        exact case2_impossible_C hm B BS ⟨hInv₁, hInv₂, hInv₃⟩ hB_mem hg₃_disj hc₁_in_B hg₁_pres hg₂_pres hBlock hSize