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
import LemmaFeld.GroupTheory.AF.SignAnalysis.Lemma14

/-!
# Lemma 11.5: Case 2 Impossibility for C (m ≥ 1)

Proves that if B contains c₁ (first tail C element) and g₃ does not preserve B,
then we get a contradiction.

## Main Results

* `case2_impossible_C`: The m ≥ 1 case leads to contradiction
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

theorem case2_impossible_C (hm : m ≥ 1) (B : Set (Omega n k m))
    (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS) (hB_in_BS : B ∈ BS.blocks)
    (hg₃Disj : Disjoint (g₃ n k m '' B) B)
    (hc₁_in_B : c₁ n k m hm ∈ B)
    (hg₁_pres : PreservesSet (g₁ n k m) B) (hg₂_pres : PreservesSet (g₂ n k m) B)
    (hBlock : ∀ j : ℕ, (g₃ n k m ^ j) '' B = B ∨ Disjoint ((g₃ n k m ^ j) '' B) B)
    (hNT_lower : 1 < B.ncard) : False := by
  have hB_subset_supp_g₃ : B ⊆ ↑(g₃ n k m).support := by
    intro x hxB
    by_contra hx_not_supp
    have hFix : g₃ n k m x = x := Equiv.Perm.notMem_support.mp hx_not_supp
    have hx_in_img : x ∈ g₃ n k m '' B := ⟨x, hxB, hFix⟩
    exact Set.disjoint_iff.mp hg₃Disj ⟨hx_in_img, hxB⟩

  have hB_disj_supp_g₁ : Disjoint (↑(g₁ n k m).support) B := by
    have hCyc : (g₁ n k m).IsCycle := g₁_isCycle n k m (by omega)
    rcases cycle_support_subset_or_disjoint hCyc hg₁_pres with hSub | hDisj
    · exfalso
      have h0_in_B : (⟨0, by omega⟩ : Omega n k m) ∈ B := hSub elem0_in_support_g₁
      have h0_not : (⟨0, by omega⟩ : Omega n k m) ∉ (g₃ n k m).support := elem0_not_in_support_g₃
      exact h0_not (hB_subset_supp_g₃ h0_in_B)
    · exact hDisj

  have hB_disj_supp_g₂ : Disjoint (↑(g₂ n k m).support) B := by
    have hCyc : (g₂ n k m).IsCycle := g₂_isCycle n k m
    rcases cycle_support_subset_or_disjoint hCyc hg₂_pres with hSub | hDisj
    · exfalso
      have h3_in_B : (⟨3, by omega⟩ : Omega n k m) ∈ B := hSub elem3_in_support_g₂'
      have h3_not : (⟨3, by omega⟩ : Omega n k m) ∉ (g₃ n k m).support := elem3_not_in_support_g₃
      exact h3_not (hB_subset_supp_g₃ h3_in_B)
    · exact hDisj

  have hB_subset_tailC : ∀ x ∈ B, isTailC x :=
    case2_C_subset_tailC B hB_subset_supp_g₃ hB_disj_supp_g₁ hB_disj_supp_g₂

  by_cases hm1 : m = 1
  · have hB_ncard_le_m : B.ncard ≤ m := by
      have hTailC_finite : Set.Finite {x : Omega n k m | isTailC x} := Set.toFinite _
      have hB_subset_tailC_set : B ⊆ {x : Omega n k m | isTailC x} := fun x hx => hB_subset_tailC x hx
      calc B.ncard ≤ {x : Omega n k m | isTailC x}.ncard := Set.ncard_le_ncard hB_subset_tailC_set hTailC_finite
        _ = m := by
          have h_eq : {x : Omega n k m | isTailC x} = Set.range (fun i : Fin m => (⟨6 + n + k + i.val, by omega⟩ : Omega n k m)) := by
            ext x; simp [Set.mem_setOf_eq, Set.mem_range, isTailC]; constructor <;> intro h
            · use ⟨x.val - 6 - n - k, by have := x.isLt; omega⟩; ext; simp; omega
            · obtain ⟨i, hi⟩ := h; rw [← hi]; simp
          rw [h_eq, Set.ncard_range_of_injective]
          · simp
          · intro i j hij; simp only [Fin.ext_iff] at hij ⊢; omega
    omega
  · -- m >= 2
    have hm2 : m ≥ 2 := by omega
    -- Step 1: Find j such that g₃^j(c₁) = 4
    have hc₁_in_supp : c₁ n k m hm ∈ (g₃ n k m).support := c₁_mem_support_g₃ hm
    have h4_in_supp : (⟨4, by omega⟩ : Omega n k m) ∈ (g₃ n k m).support := elem4_in_support_g₃
    have hCyc : (g₃ n k m).IsCycle := g₃_isCycle n k m
    rw [mem_support] at hc₁_in_supp h4_in_supp
    obtain ⟨j, hj⟩ := hCyc.exists_zpow_eq hc₁_in_supp h4_in_supp
    -- Step 2: Define B' and establish basic properties
    let B' := (g₃ n k m ^ j) '' B
    have h4_in_B' : (⟨4, by omega⟩ : Omega n k m) ∈ B' := ⟨c₁ n k m hm, hc₁_in_B, hj⟩
    have hB'_card : B'.ncard = B.ncard := Set.ncard_image_of_injective _ (g₃ n k m ^ j).injective
    have hB'_card_gt_1 : 1 < B'.ncard := by rw [hB'_card]; exact hNT_lower
    have hB'_subset_supp : B' ⊆ (g₃ n k m).support := by
      intro x hx; obtain ⟨y, hyB, hyx⟩ := hx
      have hy_in_supp : y ∈ (g₃ n k m).support := hB_subset_supp_g₃ hyB
      simp only [Finset.mem_coe] at hy_in_supp ⊢
      rw [← hyx]; exact Equiv.Perm.zpow_apply_mem_support.mpr hy_in_supp
    have hB'_in_BS : B' ∈ BS.blocks := g₃_zpow_preserves_blocks BS hInv B hB_in_BS j
    -- Step 3: Show g₂(B') ≠ B'
    have hg₂_4_not_in_B' : g₂ n k m ⟨4, by omega⟩ ∉ B' := by
      rw [OrbitCore.g₂_elem4_eq_elem0']; intro h_contra
      exact elem0_not_in_support_g₃ (hB'_subset_supp h_contra)
    have hg₂_B'_ne : g₂ n k m '' B' ≠ B' := by
      intro h_eq
      have : g₂ n k m ⟨4, by omega⟩ ∈ g₂ n k m '' B' := Set.mem_image_of_mem _ h4_in_B'
      rw [h_eq] at this; exact hg₂_4_not_in_B' this
    -- Step 4: Case analysis - find g₂-fixed element or handle B' = {1, 4}
    by_cases hB'_small : ∃ z ∈ B', z ≠ (⟨1, by omega⟩ : Omega n k m) ∧ z ≠ (⟨4, by omega⟩ : Omega n k m)
    · -- Case 4a: ∃ z ∈ B' with z ∉ {1, 4}
      obtain ⟨z, hz_in_B', hz_ne_1, hz_ne_4⟩ := hB'_small
      -- z ∈ supp(g₃) \ {1, 4} = {2, 5} ∪ tailC, all g₂-fixed
      have hz_in_supp : z ∈ (g₃ n k m).support := hB'_subset_supp hz_in_B'
      have hg₂_fixes_z : g₂ n k m z = z := by
        have hz_cases : z.val = 1 ∨ z.val = 2 ∨ z.val = 4 ∨ z.val = 5 ∨ isTailC z := by
          simp only [g₃, Equiv.Perm.mem_support, ne_eq] at hz_in_supp
          by_contra h_not; push_neg at h_not
          have hz_fixed : g₃ n k m z = z := by
            apply List.formPerm_apply_of_notMem
            intro hmem
            simp only [List.mem_append, g₃CoreList, tailCList, List.mem_cons,
              List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at hmem
            rcases hmem with hCore | hTail
            · rcases hCore with h | h | h | h <;> (simp only [Fin.ext_iff] at h; omega)
            · obtain ⟨i, _, hi⟩ := hTail
              have : isTailC z := by simp only [isTailC, ← hi, Fin.val_mk]; omega
              exact h_not.2.2.2.2 this
          exact hz_in_supp hz_fixed
        rcases hz_cases with h1 | h2 | h4 | h5 | hC
        · exact absurd (Fin.ext h1) hz_ne_1
        · have hz_eq : z = ⟨2, by omega⟩ := Fin.ext h2; rw [hz_eq]; exact g₂_fixes_elem2
        · exact absurd (Fin.ext h4) hz_ne_4
        · have hz_eq : z = ⟨5, by omega⟩ := Fin.ext h5; rw [hz_eq]; exact g₂_fixes_elem5
        · exact g₂_fixes_tailC z hC
      have hz_in_g₂B' : z ∈ g₂ n k m '' B' := by rw [← hg₂_fixes_z]; exact Set.mem_image_of_mem _ hz_in_B'
      have hg₂B'_in_BS : g₂ n k m '' B' ∈ BS.blocks := hInv.2.1 B' hB'_in_BS
      have hDisj : Disjoint B' (g₂ n k m '' B') := BS.isPartition.1 hB'_in_BS hg₂B'_in_BS hg₂_B'_ne.symm
      exact Set.disjoint_iff.mp hDisj ⟨hz_in_B', hz_in_g₂B'⟩
    · -- Case 4b: B' ⊆ {1, 4}, so B' = {1, 4}
      push_neg at hB'_small
      -- hB'_small : ∀ z ∈ B', z ≠ 1 → z = 4  (implication form)
      have h1_in_B' : (⟨1, by omega⟩ : Omega n k m) ∈ B' := by
        have hB'_has_other : ∃ y ∈ B', y ≠ (⟨4, by omega⟩ : Omega n k m) := by
          by_contra h; push_neg at h
          have hSub : B' ⊆ {⟨4, by omega⟩} := fun y hy => Set.mem_singleton_iff.mpr (h y hy)
          have hLe : B'.ncard ≤ 1 := Set.ncard_le_ncard hSub (Set.finite_singleton _) |>.trans
            (by simp [Set.ncard_singleton])
          omega
        obtain ⟨y, hy_in, hy_ne_4⟩ := hB'_has_other
        by_cases hy_eq_1 : y = ⟨1, by omega⟩
        · rw [← hy_eq_1]; exact hy_in
        · exact absurd (hB'_small y hy_in hy_eq_1) hy_ne_4
      have hB'_eq_14 : B' = {⟨1, by omega⟩, ⟨4, by omega⟩} := by
        ext z; constructor
        · intro hz
          by_cases h1 : z = ⟨1, by omega⟩
          · simp [h1]
          · simp [hB'_small z hz h1]
        · intro hz; simp at hz; rcases hz with rfl | rfl <;> assumption
      -- Sub-step 4b.2: use hBlock to derive contradiction
      -- Case split on m = 2 vs m ≥ 3
      by_cases hm_eq_2 : m = 2
      · -- Case m = 2: g₃²(c₁) = 2, but 2 ∉ tailC, contradicting B ⊆ tailC
        have hg₃_pow2_c₁ : (g₃ n k m ^ (2 : ℕ)) (c₁ n k m hm) = ⟨2, by omega⟩ := by
          simp only [c₁]; exact OrbitCore.g₃_pow2_c₁_eq_elem2 hm_eq_2
        have h2_not_tailC : ¬isTailC (⟨2, by omega⟩ : Omega n k m) := by
          simp only [isTailC]; omega
        -- g₃²(c₁) ∈ g₃²(B) since c₁ ∈ B
        have hc₁_in_g₃pow2B : (g₃ n k m ^ (2 : ℕ)) (c₁ n k m hm) ∈ ⇑(g₃ n k m ^ (2 : ℕ)) '' B :=
          Set.mem_image_of_mem _ hc₁_in_B
        -- By hBlock 2: either g₃²(B) = B or Disjoint
        rcases hBlock 2 with hEq | hDisj
        · -- If g₃²(B) = B, then 2 ∈ B
          rw [hEq] at hc₁_in_g₃pow2B
          have h2_in_B : (⟨2, by omega⟩ : Omega n k m) ∈ B := by
            rw [← hg₃_pow2_c₁]; exact hc₁_in_g₃pow2B
          exact h2_not_tailC (hB_subset_tailC _ h2_in_B)
        · -- If Disjoint: B = {c₁, c₂} but g₃(c₁) = c₂ ∈ B, contradicting hg₃Disj
          -- Since m = 2, tailC = {c₁, c₂} and |B| = 2, B ⊆ tailC implies B = {c₁, c₂}
          have hc₂ : (⟨7 + n + k, by omega⟩ : Omega n k m) ∈ B := by
            have hTailC_eq : {x : Omega n k m | isTailC x} = {c₁ n k m hm, ⟨7 + n + k, by omega⟩} := by
              ext x; simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
              constructor
              · intro hx; simp only [isTailC, c₁] at hx ⊢
                rcases Nat.lt_succ_iff_lt_or_eq.mp (by omega : x.val < 6 + n + k + 2) with h | h
                · left; ext; simp only [Fin.val_mk]; omega
                · right; ext; simp only [Fin.val_mk]; omega
              · intro hx; rcases hx with rfl | rfl
                · simp only [isTailC, c₁, hm_eq_2]; omega
                · simp only [isTailC, hm_eq_2]; constructor <;> omega
            have hB_sub : B ⊆ {c₁ n k m hm, ⟨7 + n + k, by omega⟩} := by
              intro x hx; rw [← hTailC_eq]; exact hB_subset_tailC x hx
            have hc₁_ne_c₂ : c₁ n k m hm ≠ (⟨7 + n + k, by omega⟩ : Omega n k m) := by
              simp only [c₁, ne_eq, Fin.ext_iff, Fin.val_mk]; omega
            have hCard2 : ({c₁ n k m hm, ⟨7 + n + k, by omega⟩} : Set (Omega n k m)).ncard = 2 := by
              rw [Set.ncard_pair hc₁_ne_c₂]
            have hB_eq : B = {c₁ n k m hm, ⟨7 + n + k, by omega⟩} := by
              apply Set.eq_of_subset_of_ncard_le hB_sub
              rw [hCard2]; exact hNT_lower
            rw [hB_eq]; simp
          -- g₃(c₁) = c₂, so c₂ ∈ g₃(B)
          have hg₃_c₁ : g₃ n k m (c₁ n k m hm) = ⟨7 + n + k, by omega⟩ := by
            simp only [c₁]
            have h := @OrbitCore.g₃_c₁_eq_c₂ n k m (by omega : m ≥ 2)
            convert h using 2 <;> omega
          have hc₂_in_g₃B : (⟨7 + n + k, by omega⟩ : Omega n k m) ∈ g₃ n k m '' B := by
            rw [← hg₃_c₁]; exact Set.mem_image_of_mem _ hc₁_in_B
          -- But c₂ ∈ B, contradicting Disjoint g₃(B) B
          exact Set.disjoint_iff.mp hg₃Disj ⟨hc₂_in_g₃B, hc₂⟩
      · -- Case m ≥ 3
        have hm3 : m ≥ 3 := by omega
        -- g₃(c₁) = c₂
        have hg₃_c₁ : g₃ n k m (c₁ n k m hm) = ⟨6 + n + k + 1, by omega⟩ := by
          simp only [c₁]
          exact @OrbitCore.g₃_c₁_eq_c₂ n k m (by omega : m ≥ 2)
        -- Case split: is c₂ in B?
        by_cases hc₂_in_B : (⟨6 + n + k + 1, by omega⟩ : Omega n k m) ∈ B
        · -- c₂ ∈ B: contradiction with hg₃Disj
          have hc₂_in_g₃B : (⟨6 + n + k + 1, by omega⟩ : Omega n k m) ∈ g₃ n k m '' B := by
            rw [← hg₃_c₁]; exact Set.mem_image_of_mem _ hc₁_in_B
          exact Set.disjoint_iff.mp hg₃Disj ⟨hc₂_in_g₃B, hc₂_in_B⟩
        · -- c₂ ∉ B: use hBlock 2 to get contradiction
          -- g₃²(c₁) = c₃, which is a tailC element
          have hg₃_pow2_c₁ : (g₃ n k m ^ (2 : ℕ)) (c₁ n k m hm) = ⟨6 + n + k + 2, by omega⟩ := by
            simp only [c₁]; exact OrbitCore.g₃_pow2_c₁_eq_c₃ hm3
          have hc₃_in_g₃pow2B : (⟨6 + n + k + 2, by omega⟩ : Omega n k m) ∈ ⇑(g₃ n k m ^ (2 : ℕ)) '' B := by
            rw [← hg₃_pow2_c₁]; exact Set.mem_image_of_mem _ hc₁_in_B
          -- By hBlock 2: either g₃²(B) = B or Disjoint
          rcases hBlock 2 with hEq | hDisj2
          · -- Equality case: g₃²(B) = B implies c₃ ∈ B
            -- Then B = {c₁, c₃} and g₃²(B) = {c₃, g₃²(c₃)}
            -- But g₃²(c₃) ∉ {c₁, c₃} since g₃ cycle length 4+m, 2∤4+m, 4∤4+m
            have hc₃_in_B : (⟨6 + n + k + 2, by omega⟩ : Omega n k m) ∈ B := by
              rw [← hEq]; exact hc₃_in_g₃pow2B
            -- c₃ is a tailC element
            have hc₃_tailC : isTailC (⟨6 + n + k + 2, by omega⟩ : Omega n k m) := by
              simp only [isTailC]; omega
            -- Since |B| = 2, c₁ ∈ B, c₃ ∈ B, c₁ ≠ c₃, we have B = {c₁, c₃}
            have hc₁_ne_c₃ : c₁ n k m hm ≠ (⟨6 + n + k + 2, by omega⟩ : Omega n k m) := by
              simp only [c₁, ne_eq, Fin.ext_iff, Fin.val_mk]; omega
            have hB_sub : B ⊆ {c₁ n k m hm, ⟨6 + n + k + 2, by omega⟩} := by
              intro x hx
              have hx_tailC := hB_subset_tailC x hx
              -- x is tailC, and |B| = 2 with c₁, c₃ ∈ B
              -- Since c₂ ∉ B and x ∈ B, if x ≠ c₁ and x ≠ c₃, B would have > 2 elements
              by_contra hx_not
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hx_not
              -- B contains c₁, c₃, x with x ≠ c₁, x ≠ c₃
              have h3 : ({c₁ n k m hm, ⟨6 + n + k + 2, by omega⟩, x} : Set (Omega n k m)).ncard ≥ 3 := by
                rw [Set.ncard_insert_of_not_mem, Set.ncard_insert_of_not_mem, Set.ncard_singleton]
                · simp only [Set.mem_singleton_iff]; exact Ne.symm hx_not.2
                · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
                  exact ⟨hc₁_ne_c₃, Ne.symm hx_not.1⟩
              have hTriple_sub_B : {c₁ n k m hm, ⟨6 + n + k + 2, by omega⟩, x} ⊆ B := by
                intro y hy
                simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
                rcases hy with rfl | rfl | rfl <;> assumption
              have hB_ge_3 : B.ncard ≥ 3 := by
                calc B.ncard ≥ ({c₁ n k m hm, ⟨6 + n + k + 2, by omega⟩, x} : Set (Omega n k m)).ncard :=
                       Set.ncard_le_ncard hTriple_sub_B (Set.toFinite _)
                     _ ≥ 3 := h3
              -- B'.ncard = 2 since B' = {1, 4}
              have hB'_card_eq_2 : B'.ncard = 2 := by
                rw [hB'_eq_14]
                have h1_ne_4 : (⟨1, by omega⟩ : Omega n k m) ≠ ⟨4, by omega⟩ := by
                  simp only [ne_eq, Fin.ext_iff, Fin.val_mk]; omega
                rw [Set.ncard_pair h1_ne_4]
              -- B.ncard = 2
              have hB_card_eq_2 : B.ncard = 2 := by rw [← hB'_card, hB'_card_eq_2]
              omega
            have hB_eq : B = {c₁ n k m hm, ⟨6 + n + k + 2, by omega⟩} := by
              apply Set.eq_of_subset_of_ncard_le hB_sub
              rw [Set.ncard_pair hc₁_ne_c₃]; exact hNT_lower
            -- Now g₃²(B) = {g₃²(c₁), g₃²(c₃)} = {c₃, g₃²(c₃)}
            -- For g₃²(B) = B, need g₃²(c₃) ∈ {c₁, c₃}
            -- But g₃ is a cycle of length 4+m, and 2,4 don't divide 4+m for m≥1
            -- So g₃²(c₃) ≠ c₃ and g₃⁴(c₁) ≠ c₁
            -- g₃²(c₃) = c₁ would mean g₃⁴(c₁) = c₁, contradiction
            have hOrd : orderOf (g₃ n k m) = (g₃ n k m).support.card := hCyc.orderOf
            have hCycLen : (g₃ n k m).support.card = 4 + m := LemmaFeld.GroupTheory.AF.SignAnalysis.g₃_support_card n k m
            have h4m_gt_4 : 4 + m > 4 := by omega
            have h4m_gt_2 : 4 + m > 2 := by omega
            -- g₃²(c₃) ≠ c₃: would require g₃² = 1, but orderOf g₃ = 4+m > 2
            have hg₃2_c₃_ne_c₃ : (g₃ n k m ^ (2 : ℕ)) (⟨6 + n + k + 2, by omega⟩ : Omega n k m) ≠
                ⟨6 + n + k + 2, by omega⟩ := by
              intro heq
              have hc₃_in_supp : (⟨6 + n + k + 2, by omega⟩ : Omega n k m) ∈ (g₃ n k m).support :=
                hB_subset_supp_g₃ hc₃_in_B
              -- g₃²(c₃) = c₃ with c₃ in support implies g₃² = 1 (by IsCycle.pow_eq_one_iff)
              have hpow2_eq_one : g₃ n k m ^ (2 : ℕ) = 1 := by
                rw [hCyc.pow_eq_one_iff]
                exact ⟨⟨6 + n + k + 2, by omega⟩, Equiv.Perm.mem_support.mp hc₃_in_supp, heq⟩
              -- g₃² = 1 implies orderOf g₃ | 2
              have hdvd : orderOf (g₃ n k m) ∣ 2 := orderOf_dvd_of_pow_eq_one hpow2_eq_one
              rw [hOrd, hCycLen] at hdvd
              have hle := Nat.le_of_dvd (by norm_num : (2 : ℕ) > 0) hdvd
              omega
            -- g₃²(c₃) ≠ c₁: would require g₃⁴(c₁) = c₁, but orderOf g₃ = 4+m doesn't divide 4
            have hg₃2_c₃_ne_c₁ : (g₃ n k m ^ (2 : ℕ)) (⟨6 + n + k + 2, by omega⟩ : Omega n k m) ≠
                c₁ n k m hm := by
              intro heq
              -- g₃²(c₃) = c₁ means g₃²(g₃²(c₁)) = c₁, i.e., g₃⁴(c₁) = c₁
              have hg₃4_c₁ : (g₃ n k m ^ (4 : ℕ)) (c₁ n k m hm) = c₁ n k m hm := by
                have h4eq : (4 : ℕ) = 2 + 2 := by norm_num
                calc (g₃ n k m ^ (4 : ℕ)) (c₁ n k m hm)
                    = (g₃ n k m ^ (2 + 2)) (c₁ n k m hm) := by rw [h4eq]
                    _ = (g₃ n k m ^ 2 * g₃ n k m ^ 2) (c₁ n k m hm) := by rw [pow_add]
                    _ = (g₃ n k m ^ (2 : ℕ)) ((g₃ n k m ^ (2 : ℕ)) (c₁ n k m hm)) := by
                        simp only [Equiv.Perm.coe_mul, Function.comp_apply]
                    _ = (g₃ n k m ^ (2 : ℕ)) (⟨6 + n + k + 2, by omega⟩) := by rw [hg₃_pow2_c₁]
                    _ = c₁ n k m hm := heq
              have hc₁_in_supp : c₁ n k m hm ∈ (g₃ n k m).support := hB_subset_supp_g₃ hc₁_in_B
              -- g₃⁴(c₁) = c₁ with c₁ in support implies g₃⁴ = 1 (by IsCycle.pow_eq_one_iff)
              have hpow4_eq_one : g₃ n k m ^ (4 : ℕ) = 1 := by
                rw [hCyc.pow_eq_one_iff]
                exact ⟨c₁ n k m hm, Equiv.Perm.mem_support.mp hc₁_in_supp, hg₃4_c₁⟩
              have hdvd : orderOf (g₃ n k m) ∣ 4 := orderOf_dvd_of_pow_eq_one hpow4_eq_one
              rw [hOrd, hCycLen] at hdvd
              have hle := Nat.le_of_dvd (by norm_num : (4 : ℕ) > 0) hdvd
              omega
            -- Now: g₃²(B) = {c₃, g₃²(c₃)} but g₃²(c₃) ∉ {c₁, c₃} = B
            have hg₃2_c₃_not_in_B : (g₃ n k m ^ (2 : ℕ)) (⟨6 + n + k + 2, by omega⟩ : Omega n k m) ∉ B := by
              rw [hB_eq]; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
              push_neg; exact ⟨hg₃2_c₃_ne_c₁, hg₃2_c₃_ne_c₃⟩
            -- But g₃²(c₃) ∈ g₃²(B) = B by hEq
            have hg₃2_c₃_in_g₃2B : (g₃ n k m ^ (2 : ℕ)) (⟨6 + n + k + 2, by omega⟩ : Omega n k m) ∈
                ⇑(g₃ n k m ^ (2 : ℕ)) '' B := Set.mem_image_of_mem _ hc₃_in_B
            rw [hEq] at hg₃2_c₃_in_g₃2B
            exact hg₃2_c₃_not_in_B hg₃2_c₃_in_g₃2B
          · -- Disjoint case: show c₃ ∈ B via cycle computation, contradicting disjointness
            -- Step 1: g₃²(4) = 1 (using g₃(4) = 5, g₃(5) = 1)
            have hg₃_pow2_4_eq_1 : (g₃ n k m ^ (2 : ℕ)) (⟨4, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ := by
              simp only [pow_two, Equiv.Perm.coe_mul, Function.comp_apply]
              rw [g₃_elem4_eq_elem5, g₃_elem5_eq_elem1]
            -- Step 2: g₃^j(c₃) = 1 using g₃^j(c₁) = 4 and g₃²(c₁) = c₃
            have hg₃_j_c₃_eq_1 : (g₃ n k m ^ j) (⟨6 + n + k + 2, by omega⟩ : Omega n k m) = ⟨1, by omega⟩ := by
              -- g₃^j(c₃) = g₃^j(g₃²(c₁)) = g₃^{j+2}(c₁) = g₃^{2+j}(c₁) = g₃²(g₃^j(c₁)) = g₃²(4) = 1
              have h1 : (g₃ n k m ^ j) (⟨6 + n + k + 2, by omega⟩ : Omega n k m) =
                  (g₃ n k m ^ j) ((g₃ n k m ^ (2 : ℕ)) (c₁ n k m hm)) := by rw [hg₃_pow2_c₁]
              have h2 : (g₃ n k m ^ j) ((g₃ n k m ^ (2 : ℕ)) (c₁ n k m hm)) =
                  ((g₃ n k m ^ j) * (g₃ n k m ^ (2 : ℕ))) (c₁ n k m hm) := rfl
              have h3 : ((g₃ n k m ^ j) * (g₃ n k m ^ (2 : ℕ))) =
                  ((g₃ n k m ^ (2 : ℕ)) * (g₃ n k m ^ j)) := by
                rw [← zpow_natCast (g₃ n k m) 2, zpow_mul_comm]
              have h4 : ((g₃ n k m ^ (2 : ℕ)) * (g₃ n k m ^ j)) (c₁ n k m hm) =
                  (g₃ n k m ^ (2 : ℕ)) ((g₃ n k m ^ j) (c₁ n k m hm)) := rfl
              rw [h1, h2, h3, h4, hj, hg₃_pow2_4_eq_1]
            -- Step 3: c₃ ∈ B (since 1 ∈ B' = g₃^j(B) and g₃^j(c₃) = 1)
            have hc₃_in_B : (⟨6 + n + k + 2, by omega⟩ : Omega n k m) ∈ B := by
              -- 1 ∈ B' = g₃^j(B), and g₃^j(c₃) = 1, so c₃ = (g₃^j)⁻¹(1) ∈ B
              have h1_in_image : ⟨1, by omega⟩ ∈ (g₃ n k m ^ j) '' B := h1_in_B'
              obtain ⟨y, hy_in_B, hy_eq⟩ := h1_in_image
              -- y ∈ B and g₃^j(y) = 1
              -- But g₃^j(c₃) = 1, so y = c₃ by injectivity
              have hInj : Function.Injective (g₃ n k m ^ j) := (g₃ n k m ^ j).injective
              have hy_eq_c₃ : y = ⟨6 + n + k + 2, by omega⟩ := hInj (hy_eq.trans hg₃_j_c₃_eq_1.symm)
              rw [← hy_eq_c₃]; exact hy_in_B
            -- Step 4: Contradiction - c₃ ∈ g₃²(B) ∩ B but they're disjoint
            exact Set.disjoint_iff.mp hDisj2 ⟨hc₃_in_g₃pow2B, hc₃_in_B⟩
