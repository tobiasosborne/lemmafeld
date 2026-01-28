/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Core

/-!
# Lemma 5: List Element Properties

Properties about specific elements in the generator cycle lists for transitivity proofs.

## Main Results

* `g₁_list_getElem_*` - Element access for g₁ cycle list
* `g₂_list_getElem_*` - Element access for g₂ cycle list
* `g₃_list_getElem_tail` - Tail element access for g₃ cycle list
-/

namespace LemmaFeld.GroupTheory.AF.Transitivity

open Equiv Equiv.Perm

/-! ### List Length Properties -/

/-- The g₁ list has length at least 4 -/
theorem g₁_list_length_ge_4 (n k m : ℕ) :
    4 ≤ (g₁CoreList n k m ++ tailAList n k m).length := by
  simp [g₁CoreList, tailAList, List.finRange]

/-- The g₂ list has length at least 4 -/
theorem g₂_list_length_ge_4 (n k m : ℕ) :
    4 ≤ (g₂CoreList n k m ++ tailBList n k m).length := by
  simp [g₂CoreList, tailBList, List.finRange]

/-! ### g₁ List Element Access -/

/-- The g₁ list at index 0 is ⟨0, _⟩ -/
theorem g₁_list_getElem_0 (n k m : ℕ) (h : 0 < (g₁CoreList n k m ++ tailAList n k m).length) :
    (g₁CoreList n k m ++ tailAList n k m)[0] = Fin.mk 0 (by omega) := by
  simp [g₁CoreList, tailAList]

/-- The g₁ list at index 1 is ⟨5, _⟩ -/
theorem g₁_list_getElem_1 (n k m : ℕ) (h : 1 < (g₁CoreList n k m ++ tailAList n k m).length) :
    (g₁CoreList n k m ++ tailAList n k m)[1] = Fin.mk 5 (by omega) := by
  simp [g₁CoreList, tailAList]

/-- The g₁ list at index 2 is ⟨3, _⟩ -/
theorem g₁_list_getElem_2 (n k m : ℕ) (h : 2 < (g₁CoreList n k m ++ tailAList n k m).length) :
    (g₁CoreList n k m ++ tailAList n k m)[2] = Fin.mk 3 (by omega) := by
  simp [g₁CoreList, tailAList]

/-- The g₁ list at index 3 is ⟨2, _⟩ -/
theorem g₁_list_getElem_3 (n k m : ℕ) (h : 3 < (g₁CoreList n k m ++ tailAList n k m).length) :
    (g₁CoreList n k m ++ tailAList n k m)[3] = Fin.mk 2 (by omega) := by
  simp [g₁CoreList, tailAList]

/-! ### g₂ List Element Access -/

/-- The g₂ list at index 0 is ⟨1, _⟩ -/
theorem g₂_list_getElem_0 (n k m : ℕ) (h : 0 < (g₂CoreList n k m ++ tailBList n k m).length) :
    (g₂CoreList n k m ++ tailBList n k m)[0] = Fin.mk 1 (by omega) := by
  simp [g₂CoreList, tailBList]

/-- The g₂ list at index 1 is ⟨3, _⟩ -/
theorem g₂_list_getElem_1 (n k m : ℕ) (h : 1 < (g₂CoreList n k m ++ tailBList n k m).length) :
    (g₂CoreList n k m ++ tailBList n k m)[1] = Fin.mk 3 (by omega) := by
  simp [g₂CoreList, tailBList]

/-- The g₂ list at index 2 is ⟨4, _⟩ -/
theorem g₂_list_getElem_2 (n k m : ℕ) (h : 2 < (g₂CoreList n k m ++ tailBList n k m).length) :
    (g₂CoreList n k m ++ tailBList n k m)[2] = Fin.mk 4 (by omega) := by
  simp [g₂CoreList, tailBList]

/-- The g₂ list at index 3 is ⟨0, _⟩ -/
theorem g₂_list_getElem_3 (n k m : ℕ) (h : 3 < (g₂CoreList n k m ++ tailBList n k m).length) :
    (g₂CoreList n k m ++ tailBList n k m)[3] = Fin.mk 0 (by omega) := by
  simp [g₂CoreList, tailBList]

/-! ### Tail Element Access -/

/-- Element 6+i is at index 4+i in the g₁ list -/
theorem g₁_list_getElem_tail (n k m : ℕ) (i : Fin n) :
    (g₁CoreList n k m ++ tailAList n k m)[4 + i.val]'(by simp [g₁CoreList, tailAList]; omega) =
    ⟨6 + i.val, by omega⟩ := by
  have h1 : (g₁CoreList n k m).length = 4 := by simp [g₁CoreList]
  have h2 : (g₁CoreList n k m).length ≤ 4 + i.val := by omega
  rw [List.getElem_append_right h2]
  simp only [tailAList, h1, Nat.add_sub_cancel_left]
  rw [List.getElem_map]
  simp only [List.getElem_finRange, Fin.cast_val_eq_self]
  rfl

/-- Element 6+n+j is at index 4+j in the g₂ list -/
theorem g₂_list_getElem_tail (n k m : ℕ) (j : Fin k) :
    (g₂CoreList n k m ++ tailBList n k m)[4 + j.val]'(by simp [g₂CoreList, tailBList]; omega) =
    ⟨6 + n + j.val, by omega⟩ := by
  have h1 : (g₂CoreList n k m).length = 4 := by simp [g₂CoreList]
  have h2 : (g₂CoreList n k m).length ≤ 4 + j.val := by omega
  rw [List.getElem_append_right h2]
  simp only [tailBList, h1, Nat.add_sub_cancel_left]
  rw [List.getElem_map]
  simp only [List.getElem_finRange, Fin.cast_val_eq_self]
  rfl

/-- Element 6+n+k+l is at index 4+l in the g₃ list -/
theorem g₃_list_getElem_tail (n k m : ℕ) (l : Fin m) :
    (g₃CoreList n k m ++ tailCList n k m)[4 + l.val]'(by simp [g₃CoreList, tailCList]; omega) =
    ⟨6 + n + k + l.val, by omega⟩ := by
  have h1 : (g₃CoreList n k m).length = 4 := by simp [g₃CoreList]
  have h2 : (g₃CoreList n k m).length ≤ 4 + l.val := by omega
  rw [List.getElem_append_right h2]
  simp only [tailCList, h1, Nat.add_sub_cancel_left]
  rw [List.getElem_map]
  simp only [List.getElem_finRange, Fin.cast_val_eq_self]
  rfl

end LemmaFeld.GroupTheory.AF.Transitivity
