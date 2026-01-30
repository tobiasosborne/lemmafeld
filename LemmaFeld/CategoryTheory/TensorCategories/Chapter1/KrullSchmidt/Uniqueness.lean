/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.Defs
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.Exchange
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.BiproductCancellation
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.UniquenessHelpers

/-!
# Krull-Schmidt: Uniqueness Proof

This file proves the uniqueness part of the Krull-Schmidt theorem:
any two indecomposable decompositions of a finite length object are equivalent
up to permutation and isomorphism.

The proof uses:
1. Base case: If d₁.n = 0, then X is zero, so d₂.n = 0 as well
2. Single component case: If d₁.n = 1, then X is indecomposable, so d₂.n = 1
3. Inductive case: By exchange lemma, d₁.components 0 ≅ d₂.components j for some j
   Then apply cancellation and induction on the remainders
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]

/-- **Krull-Schmidt Uniqueness**: Any two indecomposable decompositions of a finite
length object are equivalent up to permutation and isomorphism.
-/
theorem krullSchmidt_uniqueness {X : C} (hX : IsFiniteLengthObject X)
    (d₁ d₂ : IndecomposableDecomposition C X) : DecompositionsEquivalent C d₁ d₂ := by
  rcases Nat.eq_zero_or_pos d₁.n with hn | hn_pos
  · -- Base case: d₁.n = 0
    have hBiprod_zero : IsZero (⨁ d₁.components) := by
      have hemp : IsEmpty (Fin d₁.n) := by rw [hn]; exact Fin.isEmpty
      haveI := hemp
      constructor
      · intro Y
        exact ⟨{ default := biproduct.desc (fun i => IsEmpty.elim hemp i)
                 uniq := fun f => by ext j; exact IsEmpty.elim hemp j }⟩
      · intro Y
        exact ⟨{ default := biproduct.lift (fun i => IsEmpty.elim hemp i)
                 uniq := fun f => by ext j; exact IsEmpty.elim hemp j }⟩
    have hXzero : IsZero X := hBiprod_zero.of_iso d₁.iso
    have hd2_n_eq : d₂.n = 0 := eq_zero_of_isZero_indecomposable_decomposition
      d₂.components d₂.indecomposable X hXzero d₂.iso
    refine ⟨by omega, Equiv.refl _, ?_⟩
    intro i
    have : i.val < 0 := by rw [← hn]; exact i.isLt
    exact (Nat.not_lt_zero i.val this).elim
  · -- d₁.n > 0
    have hYfl : ∀ i, IsFiniteLengthObject (d₁.components i) :=
      fun i => isFiniteLengthObject_of_biproduct_iso d₁.components d₁.iso hX i
    have hZfl : ∀ j, IsFiniteLengthObject (d₂.components j) :=
      fun j => isFiniteLengthObject_of_biproduct_iso d₂.components d₂.iso hX j
    obtain ⟨j, ⟨f⟩⟩ := exchangeLemma hn_pos d₁.components d₂.components
      d₁.indecomposable d₂.indecomposable hYfl hZfl d₁.iso d₂.iso
    by_cases hn1 : d₁.n = 1
    · -- Single component case: d₁.n = 1
      have hd2_n : d₂.n = 1 := by
        by_contra hd2_ne1
        have hd2_pos : 0 < d₂.n := Fin.pos j
        have hd2_gt1 : 1 < d₂.n := Nat.lt_of_le_of_ne
          (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd2_pos)) (Ne.symm hd2_ne1)
        have iso_chain : d₁.components ⟨0, hn_pos⟩ ≅ ⨁ d₂.components :=
          (biproductSingletonIso' hn1 d₁.components).symm ≪≫ d₁.iso.symm ≪≫ d₂.iso
        exact not_indecomposable_of_biproduct_gt_one d₂.components hd2_gt1 d₂.indecomposable
          (indecomposable_of_iso_indecomposable (d₁.indecomposable ⟨0, hn_pos⟩) iso_chain)
      refine ⟨by omega, Equiv.refl _, ?_⟩
      intro i
      have hi0 : i.val = 0 := by omega
      have hj0 : j.val = 0 := by omega
      have heqi : i = ⟨0, hn_pos⟩ := Fin.ext hi0
      have heqj : j = ⟨0, by omega⟩ := Fin.ext hj0
      rw [heqi]
      simp only [Equiv.refl_apply]
      exact ⟨f ≪≫ eqToIso (by rw [heqj])⟩
    · -- Inductive case: d₁.n > 1
      -- The full proof requires strong induction on n + biproduct cancellation.
      -- Key steps:
      -- 1. Show d₂.n > 1 (else X is indecomposable, contradicting d₁.n > 1)
      -- 2. Use biproduct cancellation: Y₀ ⊞ rest₁ ≅ Z_j ⊞ rest₂ with Y₀ ≅ Z_j implies rest₁ ≅ rest₂
      -- 3. Apply IH on the (n-1)-component remainders
      -- 4. Combine permutations

      have hn_gt1 : 1 < d₁.n := Nat.lt_of_le_of_ne
        (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn_pos)) (Ne.symm hn1)

      have hd2_pos : 0 < d₂.n := Fin.pos j

      have hd2_gt1 : 1 < d₂.n := by
        by_contra hd2_le1
        have hd2_eq1 : d₂.n = 1 := Nat.eq_of_le_of_lt_succ
          (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd2_pos))
          (Nat.lt_succ_of_le (Nat.not_lt.mp hd2_le1))
        have iso_X_single : X ≅ d₂.components ⟨0, by omega⟩ :=
          d₂.iso ≪≫ biproductSingletonIso' hd2_eq1 d₂.components
        have hX_indec : Indecomposable X :=
          indecomposable_of_iso_indecomposable (d₂.indecomposable ⟨0, by omega⟩) iso_X_single.symm
        exact not_indecomposable_of_biproduct_gt_one d₁.components hn_gt1 d₁.indecomposable
          (indecomposable_of_iso_indecomposable hX_indec d₁.iso)

      -- Build head-tail splits for both decompositions
      let iso_d1_split : ⨁ d₁.components ≅
          d₁.components ⟨0, hn_pos⟩ ⊞ ⨁ (finTail hn_pos d₁.components) :=
        biproductHeadTailIso hn_pos d₁.components

      let d2_swapped := d₂.components ∘ (finSwapFront j).symm
      let iso_d2_swap : ⨁ d₂.components ≅ ⨁ d2_swapped := biproductSwapFrontIso d₂.components j
      have hd2_swapped_0 : d2_swapped ⟨0, hd2_pos⟩ = d₂.components j := biproductSwapFront_zero _ j
      let iso_d2_split : ⨁ d2_swapped ≅
          d2_swapped ⟨0, hd2_pos⟩ ⊞ ⨁ (finTail hd2_pos d2_swapped) :=
        biproductHeadTailIso hd2_pos d2_swapped

      let iso_full : (d₁.components ⟨0, hn_pos⟩ ⊞ ⨁ (finTail hn_pos d₁.components)) ≅
          (d2_swapped ⟨0, hd2_pos⟩ ⊞ ⨁ (finTail hd2_pos d2_swapped)) :=
        iso_d1_split.symm ≪≫ d₁.iso.symm ≪≫ d₂.iso ≪≫ iso_d2_swap ≪≫ iso_d2_split

      -- The remaining work requires:
      -- a) Prove the (1,1) component equals f (the exchange lemma iso)
      -- b) Apply Biprod.isoElim to get remainder iso
      -- c) Build IndecomposableDecomposition for remainders (n-1 components each)
      -- d) Apply strong induction hypothesis
      -- e) Combine permutations
      --
      -- This requires restructuring the proof to use Nat.strong_induction_on.
      -- Tracked in: lemmafeld-vxyi (this sorry)
      sorry

end LemmaFeld.TensorCategories.Chapter1
