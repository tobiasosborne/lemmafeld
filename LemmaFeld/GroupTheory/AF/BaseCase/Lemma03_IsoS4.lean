/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.BaseCase.Lemma03_Explicit
import Mathlib.Data.Fintype.Card

/-! # H₆ ≃* S₄ Isomorphism via generator correspondence:
g₁ ↦ (0 3 1 2), g₂ ↦ (0 1 2 3), g₃ ↦ (0 1 3 2) -/

namespace LemmaFeld.GroupTheory.AF.BaseCase

open Equiv Equiv.Perm

set_option linter.style.nativeDecide false
set_option linter.constructorNameAsVariable false

def φ_g₁ : Perm (Fin 4) := c[0, 3, 1, 2]
def φ_g₂ : Perm (Fin 4) := c[0, 1, 2, 3]
def φ_g₃ : Perm (Fin 4) := c[0, 1, 3, 2]

inductive Gen | g1 | g2 | g3 | inv1 | inv2 | inv3 deriving DecidableEq

private def evalH6 : Gen → Perm (Fin 6)
| .g1 => g₁ 0 0 0 | .g2 => g₂ 0 0 0 | .g3 => g₃ 0 0 0
| .inv1 => (g₁ 0 0 0)⁻¹ | .inv2 => (g₂ 0 0 0)⁻¹ | .inv3 => (g₃ 0 0 0)⁻¹

private def evalS4 : Gen → Perm (Fin 4)
| .g1 => φ_g₁ | .g2 => φ_g₂ | .g3 => φ_g₃
| .inv1 => φ_g₁⁻¹ | .inv2 => φ_g₂⁻¹ | .inv3 => φ_g₃⁻¹

private def evalWordH6 : List Gen → Perm (Fin 6)
| [] => 1 | g :: gs => evalH6 g * evalWordH6 gs

private def evalWordS4 : List Gen → Perm (Fin 4)
| [] => 1 | g :: gs => evalS4 g * evalWordS4 gs

private def gens : List Gen := [.g1, .g2, .g3, .inv1, .inv2, .inv3]

private def allWords : List (List Gen) :=
  [[]] ++ gens.map (·::[]) ++
  gens.flatMap (fun a => gens.map (fun b => [a, b])) ++
  gens.flatMap (fun a => gens.flatMap (fun b => gens.map (fun d => [a, b, d])))

def correspondencePairs : List (Perm (Fin 6) × Perm (Fin 4)) :=
  (allWords.map (fun w => (evalWordH6 w, evalWordS4 w))).eraseDups

def H6_fromPairs : List (Perm (Fin 6)) := correspondencePairs.map Prod.fst
def S4_fromPairs : List (Perm (Fin 4)) := correspondencePairs.map Prod.snd

def isoFwd (h : Perm (Fin 6)) : Perm (Fin 4) :=
  S4_fromPairs.getD (H6_fromPairs.findIdx (· == h)) 1

def isoBwd (s : Perm (Fin 4)) : Perm (Fin 6) :=
  H6_fromPairs.getD (S4_fromPairs.findIdx (· == s)) 1

theorem H6_fromPairs_eq_explicit : H6_fromPairs.toFinset = H₆_explicit := by native_decide

theorem S4_fromPairs_eq_univ : S4_fromPairs.toFinset = Finset.univ := by
  apply Finset.eq_univ_of_card
  have h : S4_fromPairs.toFinset.card = 24 := by native_decide
  rw [h, Fintype.card_perm, Fintype.card_fin]; native_decide

theorem isoBwd_mem_H6_all : ∀ s ∈ S4_fromPairs, isoBwd s ∈ H₆_explicit := by native_decide

theorem isoBwd_mem_H6 (s : Perm (Fin 4)) : isoBwd s ∈ H₆_explicit := by
  have hs : s ∈ S4_fromPairs := by
    rw [← List.mem_toFinset, S4_fromPairs_eq_univ]; exact Finset.mem_univ s
  exact isoBwd_mem_H6_all s hs

theorem isoBwd_isoFwd : ∀ h ∈ H6_fromPairs, isoBwd (isoFwd h) = h := by native_decide
theorem isoFwd_isoBwd : ∀ s ∈ S4_fromPairs, isoFwd (isoBwd s) = s := by native_decide
theorem isoFwd_mul : ∀ a ∈ H6_fromPairs, ∀ b ∈ H6_fromPairs,
    isoFwd (a * b) = isoFwd a * isoFwd b := by native_decide

/-- The isomorphism H₆ ≃* S₄ exists -/
theorem H₆_iso_S4_exists : Nonempty (H₆ ≃* Perm (Fin 4)) := by
  have mem_H6_explicit : ∀ h, h ∈ H₆ ↔ h ∈ H₆_explicit := fun h => by rw [H₆_eq_explicit]; rfl
  have mem_iff : ∀ h, h ∈ H₆ ↔ h ∈ H6_fromPairs := fun h => by
    rw [mem_H6_explicit, ← H6_fromPairs_eq_explicit, List.mem_toFinset]
  have s4_all : ∀ s : Perm (Fin 4), s ∈ S4_fromPairs := fun s => by
    rw [← List.mem_toFinset, S4_fromPairs_eq_univ]; exact Finset.mem_univ s
  exact ⟨{
    toFun := fun ⟨h, _⟩ => isoFwd h
    invFun := fun s => ⟨isoBwd s, by rw [H₆_eq_explicit]; exact isoBwd_mem_H6 s⟩
    left_inv := fun ⟨h, hh⟩ => Subtype.ext (isoBwd_isoFwd h ((mem_iff h).mp hh))
    right_inv := fun s => isoFwd_isoBwd s (s4_all s)
    map_mul' := fun ⟨a, ha⟩ ⟨b, hb⟩ =>
      isoFwd_mul a ((mem_iff a).mp ha) b ((mem_iff b).mp hb)
  }⟩

end LemmaFeld.GroupTheory.AF.BaseCase
