/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_4
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_Defs
import LemmaFeld.GroupTheory.AF.Primitivity.Lemma11_5_CycleSupport

/-!
# Lemma 11.5: Orbit Continuation Argument

The orbit of g₂(B₁) under g₁ partitions supp(g₁). Since a₁ ∈ supp(g₁), a₁ must be
in some block of this orbit. This block is either B (contradiction) or different from B
(contradiction via partition disjointness).
-/

open Equiv Equiv.Perm Set MulAction
open scoped Pointwise

variable {n k m : ℕ}

/-- Convert IsHInvariant to BlockSystemInvariant for g₁ -/
theorem g₁_block_system_invariant (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS) :
    BlockSystemInvariant (g₁ n k m) BS.blocks := by
  intro b hb
  exact hInv.1 b hb

/-- The orbit of a block meeting supp(g₁) covers supp(g₁) -/
theorem orbit_covers_support (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS)
    (B₀ : Set (Omega n k m)) (hB₀ : B₀ ∈ BS.blocks)
    (hMeet : (B₀ ∩ ↑(g₁ n k m).support).Nonempty) :
    ↑(g₁ n k m).support ⊆ ⋃ C ∈ blockOrbit (g₁ n k m) B₀, C := by
  have hCyc : (g₁ n k m).IsCycle := g₁_isCycle n k m (by omega)
  have hBSInv := g₁_block_system_invariant BS hInv
  have hDisj := BS.isPartition.1
  have hpart := orbit_blocks_partition_support hCyc hBSInv hB₀ hMeet hDisj
  intro x hx
  rw [hpart] at hx
  simp only [mem_iUnion, mem_inter_iff] at hx
  obtain ⟨C, hC, hxC, _⟩ := hx
  exact mem_biUnion hC hxC

/-- Element in orbit block implies block membership via partition -/
theorem element_in_orbit_block_or_different (BS : BlockSystemOn n k m) (hInv : IsHInvariant BS)
    (B₀ : Set (Omega n k m)) (hB₀ : B₀ ∈ BS.blocks)
    (hMeet : (B₀ ∩ ↑(g₁ n k m).support).Nonempty)
    (x : Omega n k m) (hx_supp : x ∈ (g₁ n k m).support)
    (B : Set (Omega n k m)) (hB : B ∈ BS.blocks) (hx_B : x ∈ B) :
    ∃ C ∈ blockOrbit (g₁ n k m) B₀, x ∈ C ∧ (C = B ∨ C ≠ B ∧ x ∈ B ∩ C) := by
  have hcover := orbit_covers_support BS hInv B₀ hB₀ hMeet
  have hx_in_union : x ∈ ⋃ C ∈ blockOrbit (g₁ n k m) B₀, C := hcover hx_supp
  simp only [mem_iUnion] at hx_in_union
  obtain ⟨C, hC, hx_C⟩ := hx_in_union
  refine ⟨C, hC, hx_C, ?_⟩
  by_cases heq : C = B
  · left; exact heq
  · right; exact ⟨heq, hx_B, hx_C⟩

/-- g₁ maps 3 to 2 -/
theorem g₁_elem3_eq_elem2 : g₁ n k m (⟨3, by omega⟩ : Omega n k m) = ⟨2, by omega⟩ := by
  unfold g₁
  have hNodup := g₁_list_nodup n k m
  have h_len := g₁_cycle_length n k m
  have h_2_lt : 2 < (g₁CoreList n k m ++ tailAList n k m).length := by rw [h_len]; omega
  have h_idx : (g₁CoreList n k m ++ tailAList n k m)[2]'h_2_lt =
      (⟨3, by omega⟩ : Omega n k m) := by simp [g₁CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 2 h_2_lt]
  simp only [h_len]
  have h_mod : (2 + 1) % (4 + n) = 3 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  have h_core_len : (g₁CoreList n k m).length = 4 := by simp [g₁CoreList]
  rw [List.getElem_append_left (by rw [h_core_len]; omega : 3 < (g₁CoreList n k m).length)]
  simp [g₁CoreList]

/-- Element 2 is in supp(g₁) - re-exported from FixedPoints -/
theorem elem2_in_support_g₁' : (⟨2, by omega⟩ : Omega n k m) ∈ (g₁ n k m).support := by
  have hNodup := g₁_list_nodup n k m
  have hNotSingleton : ∀ x, g₁CoreList n k m ++ tailAList n k m ≠ [x] := by
    intro x h; have : (g₁CoreList n k m ++ tailAList n k m).length = 1 := by rw [h]; simp
    have := g₁_cycle_length n k m; omega
  rw [g₁, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₁CoreList, List.mem_cons]; tauto

/-- Core elements 0, 2, 3, 5 are not in tailA -/
theorem elem0_not_tailA : ¬isTailA (⟨0, by omega⟩ : Omega n k m) := by simp [isTailA]
theorem elem2_not_tailA : ¬isTailA (⟨2, by omega⟩ : Omega n k m) := by simp [isTailA]
theorem elem3_not_tailA : ¬isTailA (⟨3, by omega⟩ : Omega n k m) := by simp [isTailA]
theorem elem5_not_tailA : ¬isTailA (⟨5, by omega⟩ : Omega n k m) := by simp [isTailA]

/-- g₁ maps 5 to 3 -/
theorem g₁_elem5_eq_elem3 : g₁ n k m (⟨5, by omega⟩ : Omega n k m) = ⟨3, by omega⟩ := by
  unfold g₁
  have hNodup := g₁_list_nodup n k m
  have h_len := g₁_cycle_length n k m
  have h_1_lt : 1 < (g₁CoreList n k m ++ tailAList n k m).length := by rw [h_len]; omega
  have h_idx : (g₁CoreList n k m ++ tailAList n k m)[1]'h_1_lt =
      (⟨5, by omega⟩ : Omega n k m) := by simp [g₁CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 1 h_1_lt]
  simp only [h_len]
  have h_mod : (1 + 1) % (4 + n) = 2 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  have h_core_len : (g₁CoreList n k m).length = 4 := by simp [g₁CoreList]
  rw [List.getElem_append_left (by rw [h_core_len]; omega : 2 < (g₁CoreList n k m).length)]
  simp [g₁CoreList]

/-- g₁ maps 0 to 5 -/
theorem g₁_elem0_eq_elem5 : g₁ n k m (⟨0, by omega⟩ : Omega n k m) = ⟨5, by omega⟩ := by
  unfold g₁
  have hNodup := g₁_list_nodup n k m
  have h_len := g₁_cycle_length n k m
  have h_0_lt : 0 < (g₁CoreList n k m ++ tailAList n k m).length := by rw [h_len]; omega
  have h_idx : (g₁CoreList n k m ++ tailAList n k m)[0]'h_0_lt =
      (⟨0, by omega⟩ : Omega n k m) := by simp [g₁CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 0 h_0_lt]
  simp only [h_len]
  have h_mod : (0 + 1) % (4 + n) = 1 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  have h_core_len : (g₁CoreList n k m).length = 4 := by simp [g₁CoreList]
  rw [List.getElem_append_left (by rw [h_core_len]; omega : 1 < (g₁CoreList n k m).length)]
  simp [g₁CoreList]

/-- g₁⁻¹ maps 3 to 5 (since g₁(5) = 3) -/
theorem g₁_inv_elem3_eq_elem5 : (g₁ n k m)⁻¹ (⟨3, by omega⟩ : Omega n k m) = ⟨5, by omega⟩ := by
  have h : g₁ n k m (⟨5, by omega⟩ : Omega n k m) = ⟨3, by omega⟩ := g₁_elem5_eq_elem3
  simp [← h]

/-- g₁⁻² maps 3 to 0 (since g₁⁻¹(3) = 5 and g₁⁻¹(5) = 0) -/
theorem g₁_inv_sq_elem3_eq_elem0 :
    (g₁ n k m)⁻¹ ((g₁ n k m)⁻¹ (⟨3, by omega⟩ : Omega n k m)) = ⟨0, by omega⟩ := by
  rw [g₁_inv_elem3_eq_elem5]
  have h : g₁ n k m (⟨0, by omega⟩ : Omega n k m) = ⟨5, by omega⟩ := g₁_elem0_eq_elem5
  simp [← h]

/-- g₁⁻¹ maps 5 to 0 (since g₁(0) = 5) -/
theorem g₁_inv_elem5_eq_elem0 : (g₁ n k m)⁻¹ (⟨5, by omega⟩ : Omega n k m) = ⟨0, by omega⟩ := by
  have h : g₁ n k m (⟨0, by omega⟩ : Omega n k m) = ⟨5, by omega⟩ := g₁_elem0_eq_elem5
  simp [← h]

/-- g₁² maps 5 to 2 (since g₁(5) = 3 and g₁(3) = 2) -/
theorem g₁_sq_elem5_eq_elem2 :
    g₁ n k m (g₁ n k m (⟨5, by omega⟩ : Omega n k m)) = ⟨2, by omega⟩ := by
  rw [g₁_elem5_eq_elem3, g₁_elem3_eq_elem2]

/-- g₁ maps 2 to the first tailA element (index 6) when n ≥ 1 -/
theorem g₁_elem2_eq_elem6 (hn : n ≥ 1) :
    g₁ n k m (⟨2, by omega⟩ : Omega n k m) = ⟨6, by omega⟩ := by
  unfold g₁
  have hNodup := g₁_list_nodup n k m
  have h_len := g₁_cycle_length n k m
  have h_3_lt : 3 < (g₁CoreList n k m ++ tailAList n k m).length := by rw [h_len]; omega
  have h_idx : (g₁CoreList n k m ++ tailAList n k m)[3]'h_3_lt =
      (⟨2, by omega⟩ : Omega n k m) := by simp [g₁CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 3 h_3_lt]
  simp only [h_len]
  have h_mod : (3 + 1) % (4 + n) = 4 := Nat.mod_eq_of_lt (by omega)
  simp only [h_mod]
  have h_core_len : (g₁CoreList n k m).length = 4 := by simp [g₁CoreList]
  rw [List.getElem_append_right (by rw [h_core_len] : (g₁CoreList n k m).length ≤ 4)]
  simp only [h_core_len, tailAList, List.getElem_map, List.getElem_finRange, Fin.ext_iff,
    Nat.sub_self]
  simp only [Fin.coe_cast, Fin.val_mk, add_zero]

/-- Element 6 is the first tailA element when n ≥ 1 -/
theorem elem6_is_tailA (hn : n ≥ 1) : isTailA (⟨6, by omega⟩ : Omega n k m) := by
  simp only [isTailA]; omega

/-- g₁²(3) = 6 (composition: g₁(3) = 2, g₁(2) = 6 when n ≥ 1) -/
theorem g₁_sq_elem3_eq_elem6 (hn : n ≥ 1) :
    g₁ n k m (g₁ n k m (⟨3, by omega⟩ : Omega n k m)) = ⟨6, by omega⟩ := by
  rw [g₁_elem3_eq_elem2, g₁_elem2_eq_elem6 hn]

/-- If B is in the orbit of g₂(B₁) and B ⊆ tailA, then B cannot be g₂(B₁) -/
theorem orbit_first_block_has_core (B₀ : Set (Omega n k m))
    (h3_in : (⟨3, by omega⟩ : Omega n k m) ∈ B₀)
    (B : Set (Omega n k m)) (hB_tailA : ∀ x ∈ B, isTailA x)
    (hB_eq : B = B₀) : False := by
  have h3_in_B : (⟨3, by omega⟩ : Omega n k m) ∈ B := hB_eq ▸ h3_in
  exact elem3_not_tailA (hB_tailA _ h3_in_B)

/-- If B is in the orbit of g₂(B₁) and B ⊆ tailA, then B cannot be g₁(g₂(B₁)) -/
theorem orbit_second_block_has_core (B₀ : Set (Omega n k m))
    (h3_in : (⟨3, by omega⟩ : Omega n k m) ∈ B₀)
    (B : Set (Omega n k m)) (hB_tailA : ∀ x ∈ B, isTailA x)
    (hB_eq : B = g₁ n k m '' B₀) : False := by
  have h2_in_g₁B₀ : (⟨2, by omega⟩ : Omega n k m) ∈ g₁ n k m '' B₀ := by
    refine ⟨⟨3, by omega⟩, h3_in, g₁_elem3_eq_elem2⟩
  have h2_in_B : (⟨2, by omega⟩ : Omega n k m) ∈ B := hB_eq ▸ h2_in_g₁B₀
  exact elem2_not_tailA (hB_tailA _ h2_in_B)

/-- If 5 ∈ B₀ and B = g₁²(B₀) and B ⊆ tailA, then False (since g₁²(5) = 2) -/
theorem orbit_third_block_has_core (B₀ : Set (Omega n k m))
    (h5_in : (⟨5, by omega⟩ : Omega n k m) ∈ B₀)
    (B : Set (Omega n k m)) (hB_tailA : ∀ x ∈ B, isTailA x)
    (hB_eq : B = g₁ n k m '' (g₁ n k m '' B₀)) : False := by
  have h2_in : (⟨2, by omega⟩ : Omega n k m) ∈ g₁ n k m '' (g₁ n k m '' B₀) := by
    refine ⟨⟨3, by omega⟩, ⟨⟨5, by omega⟩, h5_in, g₁_elem5_eq_elem3⟩, g₁_elem3_eq_elem2⟩
  exact elem2_not_tailA (hB_tailA _ (hB_eq ▸ h2_in))

/-- g₂ maps 4 to 0 (when k = 0) -/
theorem g₂_elem4_eq_elem0 (hk : k = 0) :
    g₂ n k m (⟨4, by omega⟩ : Omega n k m) = ⟨0, by omega⟩ := by
  subst hk
  unfold g₂
  have hNodup := g₂_list_nodup n 0 m
  have h_len := g₂_cycle_length n 0 m
  have h_2_lt : 2 < (g₂CoreList n 0 m ++ tailBList n 0 m).length := by rw [h_len]; omega
  have h_idx : (g₂CoreList n 0 m ++ tailBList n 0 m)[2]'h_2_lt =
      (⟨4, by omega⟩ : Omega n 0 m) := by simp [g₂CoreList]
  rw [← h_idx, List.formPerm_apply_getElem _ hNodup 2 h_2_lt]
  simp only [h_len]
  have h_mod : (2 + 1) % (4 + 0) = 3 := by omega
  simp only [h_mod]
  have h_core_len : (g₂CoreList n 0 m).length = 4 := by simp [g₂CoreList]
  rw [List.getElem_append_left (by rw [h_core_len]; omega : 3 < (g₂CoreList n 0 m).length)]
  simp [g₂CoreList]

/-- g₁⁻¹ image of a set containing 5 has 0 (since g₁⁻¹(5) = 0) -/
theorem g₁_inv_image_has_elem0 (B₀ : Set (Omega n k m))
    (h5_in : (⟨5, by omega⟩ : Omega n k m) ∈ B₀)
    (B : Set (Omega n k m)) (hB_tailA : ∀ x ∈ B, isTailA x)
    (hB_eq : B = (g₁ n k m).symm '' B₀) : False := by
  have h0_in : (⟨0, by omega⟩ : Omega n k m) ∈ (g₁ n k m).symm '' B₀ := by
    refine ⟨⟨5, by omega⟩, h5_in, ?_⟩
    exact g₁_inv_elem5_eq_elem0
  exact elem0_not_tailA (hB_tailA _ (hB_eq ▸ h0_in))

/-- Element 1 is not in tailA -/
theorem elem1_not_tailA : ¬isTailA (⟨1, by omega⟩ : Omega n k m) := by simp [isTailA]

/-- g₁ fixes all tailC elements -/
theorem g₁_fixes_tailC (x : Omega n k m) (hx : isTailC x) : g₁ n k m x = x := by
  simp only [isTailC] at hx
  apply List.formPerm_apply_of_notMem
  intro hmem
  simp only [List.mem_append, g₁CoreList, tailAList, List.mem_cons, List.mem_map,
    List.mem_finRange, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h
  · rcases h with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
  · obtain ⟨j, _, hj⟩ := h; simp only [Fin.ext_iff] at hj; have := j.isLt; omega

/-- g₂ fixes all tailC elements -/
theorem g₂_fixes_tailC (x : Omega n k m) (hx : isTailC x) : g₂ n k m x = x := by
  simp only [isTailC] at hx
  apply List.formPerm_apply_of_notMem
  intro hmem
  simp only [List.mem_append, g₂CoreList, tailBList, List.mem_cons, List.mem_map,
    List.mem_finRange, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h
  · rcases h with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
  · obtain ⟨j, _, hj⟩ := h; simp only [Fin.ext_iff] at hj; have := j.isLt; omega

/-- g₁ fixes all tailB elements -/
theorem g₁_fixes_tailB (x : Omega n k m) (hx : isTailB x) : g₁ n k m x = x := by
  simp only [isTailB] at hx
  apply List.formPerm_apply_of_notMem
  intro hmem
  simp only [List.mem_append, g₁CoreList, tailAList, List.mem_cons, List.mem_map,
    List.mem_finRange, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h
  · rcases h with h | h | h | h <;> simp only [Fin.ext_iff] at h <;> omega
  · obtain ⟨j, _, hj⟩ := h; simp only [Fin.ext_iff] at hj; have := j.isLt; omega

/-- tailB ∩ tailA = ∅ -/
theorem tailB_disjoint_tailA (x : Omega n k m) : isTailB x → ¬isTailA x := by
  simp only [isTailB, isTailA]; omega

/-- tailC ∩ tailA = ∅ -/
theorem tailC_disjoint_tailA (x : Omega n k m) : isTailC x → ¬isTailA x := by
  simp only [isTailC, isTailA]; omega

/-- (g₁^2)⁻¹(3) = 0, using that (g^n)⁻¹ = g⁻¹^n and expanding -/
theorem g₁_pow2_inv_elem3_eq_elem0 :
    (g₁ n k m ^ (2 : ℕ))⁻¹ (⟨3, by omega⟩ : Omega n k m) = ⟨0, by omega⟩ := by
  -- (g^2)⁻¹ = g⁻¹^2 by inv_pow
  rw [← inv_pow, sq]
  -- g⁻¹ * g⁻¹ applied to 3
  simp only [Equiv.Perm.coe_mul, Function.comp_apply]
  rw [g₁_inv_elem3_eq_elem5, g₁_inv_elem5_eq_elem0]

/-- (g₁^2)⁻¹(3) = 0, stated with Int cast for zpow compatibility -/
theorem g₁_zpow2_inv_elem3_eq_elem0 :
    (g₁ n k m ^ ((2 : ℕ) : ℤ))⁻¹ (⟨3, by omega⟩ : Omega n k m) = ⟨0, by omega⟩ := by
  simp only [zpow_natCast]
  exact g₁_pow2_inv_elem3_eq_elem0
