/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core

/-!
# Lemma 11.5 Fixed Point Lemmas

Helper lemmas showing which elements are fixed by generators g₁, g₂, g₃.
These are used in the main Lemma 11.5 proof for fixed-point arguments.

## Main Results

* `fixed_outside_support`: Elements outside support are fixed
* `tailA_not_in_support_g₂`: Tail A elements not in supp(g₂)
* `tailA_not_in_support_g₃`: Tail A elements not in supp(g₃)
* `g₂_fixes_tailA`, `g₃_fixes_tailA`: g₂, g₃ fix tail A elements
* `g₂_fixes_elem2`: g₂ fixes element 2 (= "3" in 1-indexed)
* `elem2_in_support_g₁`: Element 2 is in supp(g₁)
-/

open Equiv Equiv.Perm Set

variable {n k m : ℕ}

/-- Elements outside supp(σ) are fixed by σ -/
theorem fixed_outside_support {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Perm α) (x : α) (hx : x ∉ σ.support) : σ x = x := by
  simp only [Finset.mem_coe, mem_support, ne_eq, not_not] at hx
  exact hx

/-- Tail A elements are not in the g₂ cycle list -/
theorem tailA_not_in_g₂_list (i : Fin n) :
    (⟨6 + i.val, by omega⟩ : Omega n k m) ∉ g₂CoreList n k m ++ tailBList n k m := by
  intro h
  simp only [List.mem_append, g₂CoreList, tailBList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h
    all_goals simp only [Fin.ext_iff] at h; omega
  · obtain ⟨j, _, hj⟩ := h
    simp only [Fin.ext_iff] at hj
    have := i.isLt
    omega

/-- Tail A elements are not in supp(g₂) -/
theorem tailA_not_in_support_g₂ (hn : n ≥ 1) (i : Fin n) :
    (⟨6 + i.val, by omega⟩ : Omega n k m) ∉ (g₂ n k m).support := by
  simp only [g₂, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_not_mem
  exact tailA_not_in_g₂_list i

/-- Tail A elements are not in the g₃ cycle list -/
theorem tailA_not_in_g₃_list (i : Fin n) :
    (⟨6 + i.val, by omega⟩ : Omega n k m) ∉ g₃CoreList n k m ++ tailCList n k m := by
  intro h
  simp only [List.mem_append, g₃CoreList, tailCList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h
    all_goals simp only [Fin.ext_iff] at h; omega
  · obtain ⟨j, _, hj⟩ := h
    simp only [Fin.ext_iff] at hj
    have := i.isLt
    omega

/-- Tail A elements are not in supp(g₃) -/
theorem tailA_not_in_support_g₃ (hn : n ≥ 1) (i : Fin n) :
    (⟨6 + i.val, by omega⟩ : Omega n k m) ∉ (g₃ n k m).support := by
  simp only [g₃, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_not_mem
  exact tailA_not_in_g₃_list i

/-- g₂ fixes tail A elements -/
theorem g₂_fixes_tailA (hn : n ≥ 1) (i : Fin n) :
    g₂ n k m ⟨6 + i.val, by omega⟩ = ⟨6 + i.val, by omega⟩ := by
  exact fixed_outside_support _ _ (tailA_not_in_support_g₂ hn i)

/-- Element 2 is not in the g₂ cycle list -/
theorem elem2_not_in_g₂_list :
    (⟨2, by omega⟩ : Omega n k m) ∉ g₂CoreList n k m ++ tailBList n k m := by
  intro h
  simp only [List.mem_append, g₂CoreList, tailBList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h
    all_goals simp only [Fin.ext_iff] at h; omega
  · obtain ⟨j, _, hj⟩ := h
    simp only [Fin.ext_iff] at hj
    omega

/-- Element 2 is not in supp(g₂) -/
theorem elem2_not_in_support_g₂ :
    (⟨2, by omega⟩ : Omega n k m) ∉ (g₂ n k m).support := by
  simp only [g₂, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_not_mem
  exact elem2_not_in_g₂_list

/-- g₂ fixes element 2 -/
theorem g₂_fixes_elem2 :
    g₂ n k m (⟨2, by omega⟩ : Omega n k m) = ⟨2, by omega⟩ := by
  exact fixed_outside_support _ _ elem2_not_in_support_g₂

/-- Element 2 is in supp(g₁) (since it's in g₁CoreList [0, 5, 3, 2]) -/
theorem elem2_in_support_g₁ (hn : n ≥ 1) :
    (⟨2, by omega⟩ : Omega n k m) ∈ (g₁ n k m).support := by
  have hNodup := g₁_list_nodup n k m
  have hNotSingleton : ∀ x, g₁CoreList n k m ++ tailAList n k m ≠ [x] := by
    intro x h
    have : (g₁CoreList n k m ++ tailAList n k m).length = 1 := by rw [h]; simp
    have := g₁_cycle_length n k m
    omega
  rw [g₁, List.support_formPerm_of_nodup _ hNodup hNotSingleton]
  simp only [List.mem_toFinset, List.mem_append, g₁CoreList, List.mem_cons]
  tauto

/-- g₃ fixes tail A elements -/
theorem g₃_fixes_tailA (hn : n ≥ 1) (i : Fin n) :
    g₃ n k m ⟨6 + i.val, by omega⟩ = ⟨6 + i.val, by omega⟩ := by
  exact fixed_outside_support _ _ (tailA_not_in_support_g₃ hn i)

/-- Element 5 is not in the g₂ cycle list -/
theorem elem5_not_in_g₂_list :
    (⟨5, by omega⟩ : Omega n k m) ∉ g₂CoreList n k m ++ tailBList n k m := by
  intro h
  simp only [List.mem_append, g₂CoreList, tailBList, List.mem_cons,
    List.mem_map, List.mem_finRange, List.not_mem_nil, or_false] at h
  rcases h with h | h
  · rcases h with h | h | h | h
    all_goals simp only [Fin.ext_iff] at h; omega
  · obtain ⟨j, _, hj⟩ := h
    simp only [Fin.ext_iff] at hj
    omega

/-- Element 5 is not in supp(g₂) -/
theorem elem5_not_in_support_g₂ :
    (⟨5, by omega⟩ : Omega n k m) ∉ (g₂ n k m).support := by
  simp only [g₂, Equiv.Perm.mem_support, ne_eq, not_not]
  apply List.formPerm_apply_of_not_mem
  exact elem5_not_in_g₂_list

/-- g₂ fixes element 5 -/
theorem g₂_fixes_elem5 :
    g₂ n k m (⟨5, by omega⟩ : Omega n k m) = ⟨5, by omega⟩ := by
  exact fixed_outside_support _ _ elem5_not_in_support_g₂
