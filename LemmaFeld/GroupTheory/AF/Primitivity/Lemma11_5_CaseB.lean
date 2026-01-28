/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_SymmetricDefs
import LemmaFeld.GroupTheory.AF.Transitivity.Lemma05ListProps
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_ZpowBlocks
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_OrbitHelpers_Core
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_OrbitHelpers

/-!
# Lemma 11.5: Case 2 Impossibility for B (k ≥ 1)

Proves that if B contains b₁ (first tail B element) and g₂ does not preserve B,
then we get a contradiction.

## Main Results

* `case2_impossible_B`: The k ≥ 1 case leads to contradiction
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

theorem case2_impossible_B (hk : k ≥ 1) (B : Set (Omega n k m))
    (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS) (hB_in_BS : B ∈ BS.blocks)
    (hg₂Disj : Disjoint (g₂ n k m '' B) B)
    (hb₁_in_B : b₁ n k m hk ∈ B)
    (hg₁_pres : PreservesSet (g₁ n k m) B) (hg₃_pres : PreservesSet (g₃ n k m) B)
    (hBlock : ∀ j : ℕ, (g₂ n k m ^ j) '' B = B ∨ Disjoint ((g₂ n k m ^ j) '' B) B)
    (hNT_lower : 1 < B.ncard) : False := by
  have hB_subset_supp_g₂ : B ⊆ ↑(g₂ n k m).support := by
    intro x hxB
    by_contra hx_not_supp
    have hFix : g₂ n k m x = x := Equiv.Perm.notMem_support.mp hx_not_supp
    have hx_in_img : x ∈ g₂ n k m '' B := ⟨x, hxB, hFix⟩
    exact Set.disjoint_iff.mp hg₂Disj ⟨hx_in_img, hxB⟩

  have hB_disj_supp_g₁ : Disjoint (↑(g₁ n k m).support) B := by
    have hCyc : (g₁ n k m).IsCycle := g₁_isCycle n k m (by omega)
    rcases cycle_support_subset_or_disjoint hCyc hg₁_pres with hSub | hDisj
    · exfalso
      have h5_in_B : (⟨5, by omega⟩ : Omega n k m) ∈ B := hSub elem5_in_support_g₁
      have h5_not : (⟨5, by omega⟩ : Omega n k m) ∉ (g₂ n k m).support := elem5_not_in_support_g₂
      exact h5_not (hB_subset_supp_g₂ h5_in_B)
    · exact hDisj

  have hB_disj_supp_g₃ : Disjoint (↑(g₃ n k m).support) B := by
    have hCyc : (g₃ n k m).IsCycle := g₃_isCycle n k m
    rcases cycle_support_subset_or_disjoint hCyc hg₃_pres with hSub | hDisj
    · exfalso
      have h2_in_B : (⟨2, by omega⟩ : Omega n k m) ∈ B := hSub elem2_in_support_g₃
      have h2_not : (⟨2, by omega⟩ : Omega n k m) ∉ (g₂ n k m).support := elem2_not_in_support_g₂
      exact h2_not (hB_subset_supp_g₂ h2_in_B)
    · exact hDisj

  have hB_subset_tailB : ∀ x ∈ B, isTailB x :=
    case2_B_subset_tailB B hB_subset_supp_g₂ hB_disj_supp_g₁ hB_disj_supp_g₃

  by_cases hk1 : k = 1
  · -- k=1
    have hB_ncard_le_k : B.ncard ≤ k := by
      have hTailB_finite : Set.Finite {x : Omega n k m | isTailB x} := Set.toFinite _
      have hB_subset_tailB_set : B ⊆ {x : Omega n k m | isTailB x} := fun x hx => hB_subset_tailB x hx
      calc B.ncard ≤ {x : Omega n k m | isTailB x}.ncard := Set.ncard_le_ncard hB_subset_tailB_set hTailB_finite
        _ = k := by
          have h_eq : {x : Omega n k m | isTailB x} = Set.range (fun i : Fin k => (⟨6 + n + i.val, by omega⟩ : Omega n k m)) := by
            ext x; simp [Set.mem_setOf_eq, Set.mem_range, isTailB]; constructor <;> intro h
            · use ⟨x.val - 6 - n, by have := x.isLt; omega⟩; ext; simp; omega
            · obtain ⟨i, hi⟩ := h; rw [← hi]; constructor <;> simp <;> omega
          rw [h_eq, Set.ncard_range_of_injective]
          · simp
          · intro i j h; ext; simp at h; exact h
    omega
  · -- k >= 2: Use orbit argument
    have hk2 : k ≥ 2 := by omega
    -- Step 1: b₁ ∈ supp(g₂), g₂ is a cycle, so ∃ j mapping b₁ to 0
    have hb₁_in_supp : b₁ n k m hk ∈ (g₂ n k m).support := b₁_mem_support_g₂ hk
    have h0_in_supp : (⟨0, by omega⟩ : Omega n k m) ∈ (g₂ n k m).support := elem0_in_support_g₂
    have hCyc : (g₂ n k m).IsCycle := g₂_isCycle n k m
    rw [mem_support] at hb₁_in_supp h0_in_supp
    obtain ⟨j, hj⟩ := hCyc.exists_zpow_eq hb₁_in_supp h0_in_supp
    -- Step 2: Define B' = g₂^j '' B, containing 0
    let B' := (g₂ n k m ^ j) '' B
    have h0_in_B' : (⟨0, by omega⟩ : Omega n k m) ∈ B' := ⟨b₁ n k m hk, hb₁_in_B, hj⟩
    have hB'_card : B'.ncard = B.ncard := Set.ncard_image_of_injective _ (g₂ n k m ^ j).injective
    have hB'_card_gt_1 : 1 < B'.ncard := by rw [hB'_card]; exact hNT_lower
    -- Step 3: B' ⊆ supp(g₂)
    have hB'_subset_supp : B' ⊆ (g₂ n k m).support := by
      intro x hx; obtain ⟨y, hyB, hyx⟩ := hx
      have hy_in_supp : y ∈ (g₂ n k m).support := hB_subset_supp_g₂ hyB
      simp only [Finset.mem_coe] at hy_in_supp ⊢
      rw [← hyx]
      exact Equiv.Perm.zpow_apply_mem_support.mpr hy_in_supp
    -- Step 4: g₁(0) = 5 ∉ supp(g₂), so g₁(0) ∉ B'
    have hg₁_0_not_in_B' : g₁ n k m ⟨0, by omega⟩ ∉ B' := by
      rw [g₁_elem0_eq_elem5]; intro h_contra
      exact elem5_not_in_support_g₂ (hB'_subset_supp h_contra)
    -- Step 5: g₁(B') ≠ B' (since 0 ∈ B' but g₁(0) ∉ B')
    have hg₁_B'_ne : g₁ n k m '' B' ≠ B' := by
      intro h_eq
      have : g₁ n k m ⟨0, by omega⟩ ∈ g₁ n k m '' B' := Set.mem_image_of_mem _ h0_in_B'
      rw [h_eq] at this; exact hg₁_0_not_in_B' this
    -- Step 6: Find y ∈ B', y ≠ 0
    have hB'_has_other : ∃ y ∈ B', y ≠ (⟨0, by omega⟩ : Omega n k m) := by
      by_contra h; push_neg at h
      have hSub : B' ⊆ {⟨0, by omega⟩} := fun y hy => Set.mem_singleton_iff.mpr (h y hy)
      have hLe : B'.ncard ≤ 1 := Set.ncard_le_ncard hSub (Set.finite_singleton _) |>.trans
        (by simp [Set.ncard_singleton])
      omega
    obtain ⟨y, hy_in_B', hy_ne_0⟩ := hB'_has_other
    have hy_in_supp : y ∈ (g₂ n k m).support := hB'_subset_supp hy_in_B'
    -- Step 7: Case analysis on y
    -- y ∈ supp(g₂) = {0, 1, 3, 4} ∪ tailB, y ≠ 0
    -- If y ∈ {1, 4} ∪ tailB, g₁ fixes y
    by_cases hy_eq_1 : y = ⟨1, by omega⟩
    · -- y = 1: g₁ fixes 1
      have hg₁_fixes_y : g₁ n k m y = y := by rw [hy_eq_1]; exact g₁_fixes_elem1
      have hy_in_g₁B' : y ∈ g₁ n k m '' B' := by rw [← hg₁_fixes_y]; exact Set.mem_image_of_mem _ hy_in_B'
      have hB'_in_BS : B' ∈ BS.blocks := g₂_zpow_preserves_blocks BS hInv B hB_in_BS j
      have hg₁B'_in_BS : g₁ n k m '' B' ∈ BS.blocks := hInv.1 B' hB'_in_BS
      have hDisj : Disjoint B' (g₁ n k m '' B') := BS.isPartition.1 hB'_in_BS hg₁B'_in_BS hg₁_B'_ne.symm
      exact Set.disjoint_iff.mp hDisj ⟨hy_in_B', hy_in_g₁B'⟩
    · by_cases hy_eq_4 : y = ⟨4, by omega⟩
      · -- y = 4: g₁ fixes 4
        have hg₁_fixes_y : g₁ n k m y = y := by rw [hy_eq_4]; exact g₁_fixes_elem4
        have hy_in_g₁B' : y ∈ g₁ n k m '' B' := by rw [← hg₁_fixes_y]; exact Set.mem_image_of_mem _ hy_in_B'
        have hB'_in_BS : B' ∈ BS.blocks := g₂_zpow_preserves_blocks BS hInv B hB_in_BS j
        have hg₁B'_in_BS : g₁ n k m '' B' ∈ BS.blocks := hInv.1 B' hB'_in_BS
        have hDisj : Disjoint B' (g₁ n k m '' B') := BS.isPartition.1 hB'_in_BS hg₁B'_in_BS hg₁_B'_ne.symm
        exact Set.disjoint_iff.mp hDisj ⟨hy_in_B', hy_in_g₁B'⟩
      · -- y ≠ 0, 1, 4, so y = 3 or y ∈ tailB
        by_cases hy_tailB : isTailB y
        · -- y ∈ tailB: g₁ fixes tailB
          have hg₁_fixes_y : g₁ n k m y = y := g₁_fixes_tailB y hy_tailB
          have hy_in_g₁B' : y ∈ g₁ n k m '' B' := by rw [← hg₁_fixes_y]; exact Set.mem_image_of_mem _ hy_in_B'
          have hB'_in_BS : B' ∈ BS.blocks := g₂_zpow_preserves_blocks BS hInv B hB_in_BS j
          have hg₁B'_in_BS : g₁ n k m '' B' ∈ BS.blocks := hInv.1 B' hB'_in_BS
          have hDisj : Disjoint B' (g₁ n k m '' B') := BS.isPartition.1 hB'_in_BS hg₁B'_in_BS hg₁_B'_ne.symm
          exact Set.disjoint_iff.mp hDisj ⟨hy_in_B', hy_in_g₁B'⟩
        · -- y must be 3 (only remaining element in supp(g₂))
          -- y ∈ supp(g₂), y ≠ 0, 1, 4, y ∉ tailB → y = 3
          -- This case means B' ⊇ {0, 3}
          -- Sub-case analysis on |B'|
          by_cases hB'_card_eq_2 : B'.ncard = 2
          · -- B' = {0, 3}: Use g₂² block dichotomy argument (k ≥ 2)
            -- First establish y = 3 (since y ∈ supp(g₂), y ≠ 0, 1, 4, y ∉ tailB)
            have hy_eq_3 : y = ⟨3, by omega⟩ := by
              have hy_in_supp' : y ∈ (g₂ n k m).support := hB'_subset_supp hy_in_B'
              have h_y_cases : y.val = 0 ∨ y.val = 1 ∨ y.val = 3 ∨ y.val = 4 ∨ isTailB y := by
                simp only [g₂, Equiv.Perm.mem_support, ne_eq] at hy_in_supp'
                by_contra h_not; push_neg at h_not
                have hy_fixed : g₂ n k m y = y := by
                  apply List.formPerm_apply_of_notMem; intro hmem
                  simp only [List.mem_append, g₂CoreList, tailBList, List.mem_cons,
                    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at hmem
                  rcases hmem with hCore | hTail
                  · rcases hCore with h | h | h | h <;> (simp only [Fin.ext_iff] at h; omega)
                  · obtain ⟨i, _, hi⟩ := hTail
                    have : isTailB y := by simp only [isTailB, ← hi, Fin.val_mk]; omega
                    exact h_not.2.2.2.2 this
                exact hy_in_supp' hy_fixed
              rcases h_y_cases with h0 | h1 | h3 | h4 | hB
              · exact absurd (Fin.ext h0) hy_ne_0
              · exact absurd (Fin.ext h1) hy_eq_1
              · exact Fin.ext h3
              · exact absurd (Fin.ext h4) hy_eq_4
              · exact absurd hB hy_tailB
            -- Now {0, 3} ⊆ B' and B' = {0, 3}
            have h03_subset : ({⟨0, by omega⟩, ⟨3, by omega⟩} : Set (Omega n k m)) ⊆ B' := by
              intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
              rcases hz with rfl | rfl
              · exact h0_in_B'
              · rw [← hy_eq_3]; exact hy_in_B'
            have h03_card : ({⟨0, by omega⟩, ⟨3, by omega⟩} : Set (Omega n k m)).ncard = 2 := by
              rw [Set.ncard_pair]; exact fun h => by simp only [Fin.ext_iff] at h; omega
            have hB'_eq_03 : B' = {⟨0, by omega⟩, ⟨3, by omega⟩} := by
              apply (Set.eq_of_subset_of_ncard_le h03_subset _ (Set.toFinite _)).symm
              rw [hB'_card_eq_2, h03_card]
            -- Use set_0_3_not_g₂_closed: ∃ x ∈ {0, 3}, g₂²(x) ∉ {0, 3}
            obtain ⟨x, hx_in, hx_out⟩ := set_0_3_not_g₂_closed hk2
            -- Step 1: B' ∈ BS.blocks
            have hB'_in_BS : B' ∈ BS.blocks := g₂_zpow_preserves_blocks BS hInv B hB_in_BS j
            -- Step 2: g₂²(B') ∈ BS.blocks
            have hg₂sq_B'_in_BS : (g₂ n k m ^ (2 : ℕ)) '' B' ∈ BS.blocks := by
              have hg₂B'_in : (g₂ n k m) '' B' ∈ BS.blocks := hInv.2.1 _ hB'_in_BS
              have hg₂g₂B'_in : (g₂ n k m) '' ((g₂ n k m) '' B') ∈ BS.blocks := hInv.2.1 _ hg₂B'_in
              convert hg₂g₂B'_in using 1
              ext w; simp only [Set.mem_image, pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
              constructor
              · rintro ⟨z, hz, rfl⟩; exact ⟨g₂ n k m z, ⟨z, hz, rfl⟩, rfl⟩
              · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩; exact ⟨w, hw, rfl⟩
            -- Step 3: g₂²(B') ≠ B'
            have hg₂sq_B'_ne : (g₂ n k m ^ (2 : ℕ)) '' B' ≠ B' := by
              intro h_eq
              have hx_in_B' : x ∈ B' := by rw [hB'_eq_03]; exact hx_in
              have hg₂sq_x_in : (g₂ n k m ^ (2 : ℕ)) x ∈ (g₂ n k m ^ (2 : ℕ)) '' B' :=
                Set.mem_image_of_mem _ hx_in_B'
              rw [h_eq] at hg₂sq_x_in
              have hx_out' : (g₂ n k m ^ (2 : ℕ)) x ∉ B' := by rw [hB'_eq_03]; exact hx_out
              exact hx_out' hg₂sq_x_in
            -- Step 4: g₂²(B') ∩ B' ≠ ∅ (g₂²(3) = 0 ∈ B')
            have h_not_disjoint : ¬Disjoint ((g₂ n k m ^ (2 : ℕ)) '' B') B' := by
              rw [Set.not_disjoint_iff]
              use ⟨0, by omega⟩
              constructor
              · -- 0 ∈ g₂²(B') because g₂²(3) = 0 and 3 ∈ B'
                rw [hB'_eq_03]
                have h3_in : (⟨3, by omega⟩ : Omega n k m) ∈ ({⟨0, by omega⟩, ⟨3, by omega⟩} : Set _) :=
                  Set.mem_insert_of_mem _ rfl
                use ⟨3, by omega⟩, h3_in
                exact g₂_pow2_elem3_eq_elem0
              · -- 0 ∈ B' = {0, 3}
                rw [hB'_eq_03]; exact Set.mem_insert _ _
            -- Step 5: Contradiction
            have hDichotomy := BS.isPartition.1 hg₂sq_B'_in_BS hB'_in_BS hg₂sq_B'_ne
            exact h_not_disjoint hDichotomy
          · -- |B'| > 2: Find z ∈ B' \ {0, 3}, which must be g₁-fixed
            have hB'_card_gt_2 : B'.ncard > 2 := by omega
            have h03_subset : ({⟨0, by omega⟩, ⟨3, by omega⟩} : Set (Omega n k m)) ⊆ B' := by
              intro z hz; simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
              rcases hz with rfl | rfl
              · exact h0_in_B'
              · -- y = 3 is the only remaining case, and y ∈ B'
                -- We need to show 3 ∈ B' using the fact that y must equal 3
                -- Since y ≠ 0, 1, 4, ¬tailB, and y ∈ supp(g₂), y must be 3
                have hy_in_supp' : y ∈ (g₂ n k m).support := hB'_subset_supp hy_in_B'
                have h_y_cases : y.val = 0 ∨ y.val = 1 ∨ y.val = 3 ∨ y.val = 4 ∨ isTailB y := by
                  simp only [g₂, Equiv.Perm.mem_support, ne_eq] at hy_in_supp'
                  by_contra h_not
                  push_neg at h_not
                  have hy_fixed : g₂ n k m y = y := by
                    apply List.formPerm_apply_of_notMem
                    intro hmem
                    simp only [List.mem_append, g₂CoreList, tailBList, List.mem_cons,
                      List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at hmem
                    rcases hmem with hCore | hTail
                    · rcases hCore with h | h | h | h <;> (simp only [Fin.ext_iff] at h; omega)
                    · obtain ⟨i, _, hi⟩ := hTail
                      have : isTailB y := by simp only [isTailB, ← hi, Fin.val_mk]; omega
                      exact h_not.2.2.2.2 this
                  exact hy_in_supp' hy_fixed
                rcases h_y_cases with h0 | h1 | h3 | h4 | hB
                · have : y = ⟨0, by omega⟩ := Fin.ext h0; exact absurd this hy_ne_0
                · have : y = ⟨1, by omega⟩ := Fin.ext h1; exact absurd this hy_eq_1
                · have hy_eq_3 : y = ⟨3, by omega⟩ := Fin.ext h3
                  rw [← hy_eq_3]; exact hy_in_B'
                · have : y = ⟨4, by omega⟩ := Fin.ext h4; exact absurd this hy_eq_4
                · exact absurd hB hy_tailB
            have hDiff_nonempty : (B' \ {⟨0, by omega⟩, ⟨3, by omega⟩}).Nonempty := by
              by_contra h; rw [Set.not_nonempty_iff_eq_empty, Set.diff_eq_empty] at h
              have := Set.ncard_le_ncard h (Set.toFinite _)
              have h03_card : ({⟨0, by omega⟩, ⟨3, by omega⟩} : Set (Omega n k m)).ncard = 2 := by
                rw [Set.ncard_pair]; exact fun h => by simp only [Fin.ext_iff] at h; omega
              rw [h03_card] at this; omega
            obtain ⟨z, hz_diff⟩ := hDiff_nonempty
            simp only [Set.mem_diff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hz_diff
            obtain ⟨hz_in_B', hz_ne_0, hz_ne_3⟩ := hz_diff
            -- z ∈ supp(g₂), z ≠ 0, 3, so z ∈ {1, 4} ∪ tailB, all g₁-fixed
            have hz_in_supp : z ∈ (g₂ n k m).support := hB'_subset_supp hz_in_B'
            have hg₁_fixes_z : g₁ n k m z = z := by
              have hz_cases : z.val = 0 ∨ z.val = 1 ∨ z.val = 3 ∨ z.val = 4 ∨ isTailB z := by
                simp only [g₂, Equiv.Perm.mem_support, ne_eq] at hz_in_supp
                by_contra h_not; push_neg at h_not
                have hz_fixed : g₂ n k m z = z := by
                  apply List.formPerm_apply_of_notMem
                  intro hmem
                  simp only [List.mem_append, g₂CoreList, tailBList, List.mem_cons,
                    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at hmem
                  rcases hmem with hCore | hTail
                  · rcases hCore with h | h | h | h <;> (simp only [Fin.ext_iff] at h; omega)
                  · obtain ⟨i, _, hi⟩ := hTail
                    have : isTailB z := by simp only [isTailB, ← hi, Fin.val_mk]; omega
                    exact h_not.2.2.2.2 this
                exact hz_in_supp hz_fixed
              rcases hz_cases with h0 | h1 | h3 | h4 | hB
              · have : z = ⟨0, by omega⟩ := Fin.ext h0; exact absurd this hz_ne_0
              · have hz_eq : z = ⟨1, by omega⟩ := Fin.ext h1; rw [hz_eq]; exact g₁_fixes_elem1
              · have : z = ⟨3, by omega⟩ := Fin.ext h3; exact absurd this hz_ne_3
              · have hz_eq : z = ⟨4, by omega⟩ := Fin.ext h4; rw [hz_eq]; exact g₁_fixes_elem4
              · exact g₁_fixes_tailB z hB
            have hz_in_g₁B' : z ∈ g₁ n k m '' B' := by rw [← hg₁_fixes_z]; exact Set.mem_image_of_mem _ hz_in_B'
            have hB'_in_BS : B' ∈ BS.blocks := g₂_zpow_preserves_blocks BS hInv B hB_in_BS j
            have hg₁B'_in_BS : g₁ n k m '' B' ∈ BS.blocks := hInv.1 B' hB'_in_BS
            have hDisj : Disjoint B' (g₁ n k m '' B') := BS.isPartition.1 hB'_in_BS hg₁B'_in_BS hg₁_B'_ne.symm
            exact Set.disjoint_iff.mp hDisj ⟨hz_in_B', hz_in_g₁B'⟩
