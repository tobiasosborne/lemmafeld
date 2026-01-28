/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.GroupTheory.AF.Transitivity.Lemma05Base
import LemmaFeld.GroupTheory.AF.Transitivity.Lemma05CoreActions
import LemmaFeld.GroupTheory.AF.Transitivity.Lemma05TailConnect
import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Lemma 5: Transitivity of H on Omega

The group H = ⟨g₁, g₂, g₃⟩ acts transitively on Ω = Fin(6+n+k+m).

## Main Results

* `H_isPretransitive` - H acts transitively on Omega

## Proof Strategy

The proof proceeds by showing the support graph Γ is connected:
1. Identify edges from each generator (consecutive elements in cycles)
2. Show the Core {0,1,2,3,4,5} forms a connected subgraph
3. Show each tail vertex connects to the Core
4. Conclude Γ is connected, hence H acts transitively

## Reference

See `examples/lemmas/lemma05_transitivity.md` for the natural language proof.
-/

namespace LemmaFeld.GroupTheory.AF.Transitivity

open Equiv Equiv.Perm

/-! ### Main Transitivity Theorem -/

/-- There is only one orbit under the action of H -/
theorem H_single_orbit (n k m : ℕ) :
    ∀ x y : Omega n k m, ∃ h : H n k m, h.val x = y := by
  intro x y
  -- Get h₁ mapping x to some core element c₁
  obtain ⟨h₁, hh₁⟩ := H_reaches_core n k m x
  -- Get h₂ mapping y to some core element c₂
  obtain ⟨h₂, hh₂⟩ := H_reaches_core n k m y
  -- Get elements as Fin 6
  let c₁ : Fin 6 := ⟨(h₁.val x).val, hh₁⟩
  let c₂ : Fin 6 := ⟨(h₂.val y).val, hh₂⟩
  -- Use core_connected to get h₃ mapping c₁ to c₂
  obtain ⟨h₃, hh₃⟩ := core_connected n k m c₁ c₂
  -- Compose: h₂⁻¹ * h₃ * h₁ maps x to y
  use h₂⁻¹ * h₃ * h₁
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.coe_mul, Function.comp_apply]
  -- h₃(h₁(x)) = h₂(y) since h₃(c₁) = c₂
  have heq : h₃.val (h₁.val x) = h₂.val y := by
    have hh₃' := hh₃
    ext
    have lhs_val : (h₃.val (h₁.val x)).val = (Fin.castLE (by omega : 6 ≤ 6 + n + k + m) c₂).val := by
      have : h₃.val (Fin.castLE (by omega : 6 ≤ 6 + n + k + m) c₁) =
             Fin.castLE (by omega : 6 ≤ 6 + n + k + m) c₂ := hh₃'
      have heq1 : (Fin.castLE (by omega : 6 ≤ 6 + n + k + m) c₁ : Omega n k m) = h₁.val x := by
        ext; simp [c₁]
      rw [← heq1, this]
    have rhs_val : (h₂.val y).val = (Fin.castLE (by omega : 6 ≤ 6 + n + k + m) c₂).val := by
      simp [c₂]
    rw [lhs_val, rhs_val]
  rw [heq]
  exact Equiv.Perm.inv_apply_self (h₂.val) y

/-- The group H acts transitively on Omega.
    Proof: The support graph is connected (Core is connected and all tails
    connect to Core), hence H acts transitively. -/
theorem H_isPretransitive (n k m : ℕ) : MulAction.IsPretransitive (H n k m) (Omega n k m) := by
  constructor
  intro x y
  exact H_single_orbit n k m x y

end LemmaFeld.GroupTheory.AF.Transitivity
