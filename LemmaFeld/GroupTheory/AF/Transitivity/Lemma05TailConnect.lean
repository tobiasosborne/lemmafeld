/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Transitivity.Lemma05ListProps

/-!
# Lemma 5: Tail Vertices Connect to Core

Each tail vertex (from generators g₁, g₂, g₃) connects to the Core {0,1,2,3,4,5}.

## Main Results

* `a_tail_connected_to_core` - a-tail elements connect to Core via g₁
* `b_tail_connected_to_core` - b-tail elements connect to Core via g₂
* `c_tail_connected_to_core` - c-tail elements connect to Core via g₃
* `H_reaches_core` - Any element can be mapped to a core element
-/

namespace LemmaFeld.GroupTheory.AF.Transitivity

open Equiv Equiv.Perm

/-! ### A-tail Connection (from g₁) -/

/-- Each tail vertex in the a-tail (from g₁) connects to the Core.
    The a-tail elements are at indices 6, 7, ..., 5+n.
    g₁ cycles through [0, 5, 3, 2, 6, 7, ..., 5+n], so
    g₁^(n-i) maps 6+i to 0 (in the Core). -/
theorem a_tail_connected_to_core (n k m : ℕ) (i : Fin n) :
    ∃ h : H n k m, (h.val ⟨6 + i.val, by omega⟩ : Omega n k m).val < 6 := by
  use ⟨(g₁ n k m) ^ (n - i.val), Subgroup.pow_mem _ (g₁_mem_H n k m) _⟩
  let L := g₁CoreList n k m ++ tailAList n k m
  have hnd : L.Nodup := g₁_list_nodup n k m
  have hlen : L.length = 4 + n := g₁_cycle_length n k m
  have hidx : 4 + i.val < L.length := by simp [L, g₁CoreList, tailAList]; omega
  have helem : L[4 + i.val] = ⟨6 + i.val, by omega⟩ := g₁_list_getElem_tail n k m i
  have hidx0 : 0 < L.length := by simp [L, g₁CoreList, tailAList]
  have helem0 : L[0] = ⟨0, by omega⟩ := by simp [L, g₁CoreList]
  have hmod : (4 + i.val + (n - i.val)) % (4 + n) = 0 := by
    have hi : i.val < n := i.isLt
    have heq : 4 + i.val + (n - i.val) = 4 + n := by omega
    rw [heq, Nat.mod_self]
  unfold g₁
  conv_lhs => rw [← helem]
  rw [List.formPerm_pow_apply_getElem L hnd (n - i.val) (4 + i.val) hidx]
  simp only [hlen, hmod, helem0]
  omega

/-! ### B-tail Connection (from g₂) -/

/-- Each tail vertex in the b-tail (from g₂) connects to the Core.
    The b-tail elements are at indices 6+n, 6+n+1, ..., 5+n+k.
    g₂ cycles through [1, 3, 4, 0, 6+n, ...], so
    g₂^(k-j) maps 6+n+j to 1 (in the Core). -/
theorem b_tail_connected_to_core (n k m : ℕ) (j : Fin k) :
    ∃ h : H n k m, (h.val ⟨6 + n + j.val, by omega⟩ : Omega n k m).val < 6 := by
  use ⟨(g₂ n k m) ^ (k - j.val), Subgroup.pow_mem _ (g₂_mem_H n k m) _⟩
  let L := g₂CoreList n k m ++ tailBList n k m
  have hnd : L.Nodup := g₂_list_nodup n k m
  have hlen : L.length = 4 + k := g₂_cycle_length n k m
  have hidx : 4 + j.val < L.length := by simp [L, g₂CoreList, tailBList]; omega
  have helem : L[4 + j.val] = ⟨6 + n + j.val, by omega⟩ := g₂_list_getElem_tail n k m j
  have hidx0 : 0 < L.length := by simp [L, g₂CoreList, tailBList]
  have helem0 : L[0] = ⟨1, by omega⟩ := by simp [L, g₂CoreList]
  have hmod : (4 + j.val + (k - j.val)) % (4 + k) = 0 := by
    have hj : j.val < k := j.isLt
    have heq : 4 + j.val + (k - j.val) = 4 + k := by omega
    rw [heq, Nat.mod_self]
  unfold g₂
  conv_lhs => rw [← helem]
  rw [List.formPerm_pow_apply_getElem L hnd (k - j.val) (4 + j.val) hidx]
  simp only [hlen, hmod, helem0]
  omega

/-! ### C-tail Connection (from g₃) -/

/-- Each tail vertex in the c-tail (from g₃) connects to the Core.
    The c-tail elements are at indices 6+n+k, ..., 5+n+k+m.
    g₃ cycles through [2, 4, 5, 1, 6+n+k, ...], so
    g₃^(m-l) maps 6+n+k+l to 2 (in the Core). -/
theorem c_tail_connected_to_core (n k m : ℕ) (l : Fin m) :
    ∃ h : H n k m, (h.val ⟨6 + n + k + l.val, by omega⟩ : Omega n k m).val < 6 := by
  use ⟨(g₃ n k m) ^ (m - l.val), Subgroup.pow_mem _ (g₃_mem_H n k m) _⟩
  let L := g₃CoreList n k m ++ tailCList n k m
  have hnd : L.Nodup := g₃_list_nodup n k m
  have hlen : L.length = 4 + m := g₃_cycle_length n k m
  have hidx : 4 + l.val < L.length := by simp [L, g₃CoreList, tailCList]; omega
  have helem : L[4 + l.val] = ⟨6 + n + k + l.val, by omega⟩ := g₃_list_getElem_tail n k m l
  have hidx0 : 0 < L.length := by simp [L, g₃CoreList, tailCList]
  have helem0 : L[0] = ⟨2, by omega⟩ := by simp [L, g₃CoreList]
  have hmod : (4 + l.val + (m - l.val)) % (4 + m) = 0 := by
    have hl : l.val < m := l.isLt
    have heq : 4 + l.val + (m - l.val) = 4 + m := by omega
    rw [heq, Nat.mod_self]
  unfold g₃
  conv_lhs => rw [← helem]
  rw [List.formPerm_pow_apply_getElem L hnd (m - l.val) (4 + l.val) hidx]
  simp only [hlen, hmod, helem0]
  omega

/-! ### Any Element Reaches Core -/

/-- Any element of Omega can be mapped to a core element -/
theorem H_reaches_core (n k m : ℕ) (x : Omega n k m) :
    ∃ h : H n k m, (h.val x).val < 6 := by
  by_cases hx : x.val < 6
  · exact ⟨1, by simp [hx]⟩
  · push_neg at hx
    by_cases hn : x.val < 6 + n
    · -- x is in a-tail: x.val = 6 + i for some i < n
      have hi : x.val - 6 < n := by omega
      obtain ⟨h, hh⟩ := a_tail_connected_to_core n k m ⟨x.val - 6, hi⟩
      refine ⟨h, ?_⟩
      have hval : 6 + (x.val - 6) = x.val := Nat.add_sub_cancel' hx
      have heq : (⟨6 + (x.val - 6), by have := x.isLt; omega⟩ : Omega n k m) = x := by
        ext; exact hval
      rw [← heq]; exact hh
    · push_neg at hn
      by_cases hk : x.val < 6 + n + k
      · -- x is in b-tail: x.val = 6 + n + j for some j < k
        have hj : x.val - 6 - n < k := by omega
        obtain ⟨h, hh⟩ := b_tail_connected_to_core n k m ⟨x.val - 6 - n, hj⟩
        refine ⟨h, ?_⟩
        have hval : 6 + n + (x.val - 6 - n) = x.val := by omega
        have heq : (⟨6 + n + (x.val - 6 - n), by have := x.isLt; omega⟩ : Omega n k m) = x := by
          ext; exact hval
        rw [← heq]; exact hh
      · push_neg at hk
        -- x is in c-tail: x.val = 6 + n + k + l for some l < m
        have hl : x.val - 6 - n - k < m := by have := x.isLt; omega
        obtain ⟨h, hh⟩ := c_tail_connected_to_core n k m ⟨x.val - 6 - n - k, hl⟩
        refine ⟨h, ?_⟩
        have hval : 6 + n + k + (x.val - 6 - n - k) = x.val := by omega
        have heq : (⟨6 + n + k + (x.val - 6 - n - k), by have := x.isLt; omega⟩ : Omega n k m) = x := by
          ext; exact hval
        rw [← heq]; exact hh

end LemmaFeld.GroupTheory.AF.Transitivity
