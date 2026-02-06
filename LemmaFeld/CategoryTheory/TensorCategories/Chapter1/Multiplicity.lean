/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.Order.JordanHolder
import Mathlib.Order.RelSeries
import Mathlib.Order.OrderIsoNat
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.JordanHolderSubobject
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.FiniteLength
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.GrothendieckGroup

/-!
# §1.5.8: Jordan-Hölder Multiplicities for Abelian Categories

Defines multiplicities of simple factors in composition series of finite-length
objects in abelian categories, proving well-definedness via the Jordan-Hölder theorem.

## Book Reference

Etingof et al. "Tensor Categories" (AMS 2015), §1.5.8:
"[X : Xᵢ]" denotes the Jordan-Hölder multiplicity of simple Xᵢ in X.

## Main Results

- `exists_compositionSeries_subobject`: Finite length → composition series ⊥ to ⊤
- `compositionSeriesFactorObj`: The factor object (cokernel) at each step
- `multiplicityCount`: Count of factors isomorphic to a given simple object
- `multiplicityCount_eq_of_equivalent`: Well-definedness via JH equivalence
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C]

/-! ## Composition Series Existence -/

/-- For finite length objects, there exists a composition series from ⊥ to ⊤
in the subobject lattice. Uses ACC + DCC to refine an LTSeries to a CovBy series. -/
theorem exists_compositionSeries_subobject {X : C} (hfl : IsFiniteLengthObject X) :
    ∃ s : CompositionSeries (Subobject X), s.head = ⊥ ∧ s.last = ⊤ := by
  haveI : IsArtinianObject X := hfl.1
  haveI : IsNoetherianObject X := hfl.2
  by_cases h : (⊥ : Subobject X) = ⊤
  · exact ⟨RelSeries.singleton _ ⊥, rfl, by simp [RelSeries.last, RelSeries.singleton, h]⟩
  · have hlt : (⊥ : Subobject X) < ⊤ := lt_of_le_of_ne bot_le h
    let s0 : LTSeries (Subobject X) :=
      ⟨1, fun i => if i.val = 0 then ⊥ else ⊤, fun i => by
        simp [Fin.castSucc, Fin.succ, hlt]⟩
    obtain ⟨t, _, _, ht_head, ht_last⟩ :=
      LTSeries.exists_relSeries_covBy_and_head_eq_bot_and_last_eq_bot s0
    exact ⟨t, ht_head, ht_last⟩

/-! ## Factor Objects

For a composition series s, the factor at index i is the cokernel of s[i] → s[i+1].
Each factor is a simple object (since consecutive elements satisfy CovBy). -/

/-- The factor object at index i of a composition series: cokernel(s[i].ofLE s[i+1]). -/
def compositionSeriesFactorObj {X : C}
    (s : CompositionSeries (Subobject X)) (i : Fin s.length) : C :=
  cokernel ((s (Fin.castSucc i)).ofLE (s i.succ) (s.step i).lt.le)

/-- Whether the factor at index i is isomorphic to a given object Y. -/
def factorIsIso {X : C}
    (s : CompositionSeries (Subobject X)) (i : Fin s.length) (Y : C) : Prop :=
  Nonempty (compositionSeriesFactorObj s i ≅ Y)

instance {X : C} (s : CompositionSeries (Subobject X)) (i : Fin s.length) (Y : C) :
    Decidable (factorIsIso s i Y) :=
  Classical.dec _

/-! ## Multiplicity Count -/

/-- Count of factors in a composition series isomorphic to a given simple object Y.
This is the Jordan-Hölder multiplicity [X : Y]. -/
def multiplicityCount {X : C}
    (s : CompositionSeries (Subobject X)) (Y : C) [Simple Y] : ℕ :=
  (Finset.univ.filter (fun i => factorIsIso s i Y)).card

/-! ## Well-Definedness

The Jordan-Hölder theorem gives a bijection between factors of equivalent series
that preserves SubobjectIso (= cokernel isomorphism). This implies multiplicity
counts are equal across any two series with the same endpoints. -/

/-- SubobjectIso between factors implies the factor objects are isomorphic.
This connects the abstract JHL Iso with concrete cokernel isomorphism. -/
lemma factorObj_iso_of_subobjectIso {X : C}
    (s₁ s₂ : CompositionSeries (Subobject X))
    (i : Fin s₁.length) (j : Fin s₂.length)
    (h : JordanHolderLattice.Iso
      (s₁ (Fin.castSucc i), s₁ i.succ) (s₂ (Fin.castSucc j), s₂ j.succ)) :
    Nonempty (compositionSeriesFactorObj s₁ i ≅ compositionSeriesFactorObj s₂ j) := by
  -- SubobjectIso uses cokernel((A ⊓ B).ofLE B), but for consecutive series elements
  -- A ≤ B, so A ⊓ B = A and the cokernel matches compositionSeriesFactorObj.
  obtain ⟨φ⟩ := h
  have heq₁ := inf_eq_left.mpr (s₁.step i).lt.le
  have heq₂ := inf_eq_left.mpr (s₂.step j).lt.le
  exact ⟨(cokernel.mapIso _ _ (Subobject.isoOfEq _ _ heq₁) (Iso.refl _) (by
      simp [Subobject.isoOfEq_hom, Subobject.ofLE_comp_ofLE])).symm ≪≫ φ ≪≫
    cokernel.mapIso _ _ (Subobject.isoOfEq _ _ heq₂) (Iso.refl _) (by
      simp [Subobject.isoOfEq_hom, Subobject.ofLE_comp_ofLE])⟩

/-- Multiplicity count is independent of the choice of composition series.
Uses the Jordan-Hölder theorem: equivalent series have a factor-preserving bijection. -/
theorem multiplicityCount_eq_of_equivalent {X : C}
    (s₁ s₂ : CompositionSeries (Subobject X))
    (hhead : s₁.head = s₂.head) (hlast : s₁.last = s₂.last)
    (Y : C) [Simple Y] :
    multiplicityCount s₁ Y = multiplicityCount s₂ Y := by
  obtain ⟨f, hf⟩ := CompositionSeries.jordan_holder s₁ s₂ hhead hlast
  unfold multiplicityCount
  apply Finset.card_bij (fun i _ => f i)
  · -- f maps filtered s₁ into filtered s₂
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨iso₁⟩ := hi.2
    obtain ⟨φ⟩ := hf i
    have heq₁ := inf_eq_left.mpr (s₁.step i).lt.le
    have heq₂ := inf_eq_left.mpr (s₂.step (f i)).lt.le
    exact ⟨(cokernel.mapIso _ _ (Subobject.isoOfEq _ _ heq₂) (Iso.refl _) (by
        simp [Subobject.isoOfEq_hom, Subobject.ofLE_comp_ofLE])).symm ≪≫
      φ.symm ≪≫
      cokernel.mapIso _ _ (Subobject.isoOfEq _ _ heq₁) (Iso.refl _) (by
        simp [Subobject.isoOfEq_hom, Subobject.ofLE_comp_ofLE]) ≪≫ iso₁⟩
  · -- f is injective on the filter
    intro a₁ _ a₂ _ h; exact f.injective h
  · -- f is surjective onto filtered s₂
    intro j hj
    rw [Finset.mem_filter] at hj
    obtain ⟨iso₂⟩ := hj.2
    refine ⟨f.symm j, ?_, f.apply_symm_apply j⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨φ⟩ := hf (f.symm j)
    have heq₁ := inf_eq_left.mpr (s₁.step (f.symm j)).lt.le
    have heq₂ := inf_eq_left.mpr (s₂.step (f (f.symm j))).lt.le
    rw [f.apply_symm_apply] at heq₂ φ
    exact ⟨(cokernel.mapIso _ _ (Subobject.isoOfEq _ _ heq₁) (Iso.refl _) (by
        simp [Subobject.isoOfEq_hom, Subobject.ofLE_comp_ofLE])).symm ≪≫ φ ≪≫
      cokernel.mapIso _ _ (Subobject.isoOfEq _ _ heq₂) (Iso.refl _) (by
        simp [Subobject.isoOfEq_hom, Subobject.ofLE_comp_ofLE]) ≪≫ iso₂⟩

/-- The multiplicity of simple Y in finite-length X, defined via any composition series.
Well-defined by `multiplicityCount_eq_of_equivalent`. -/
def jhMultiplicity {X : C} (hfl : IsFiniteLengthObject X) (Y : C) [Simple Y] : ℕ :=
  multiplicityCount (Classical.choose (exists_compositionSeries_subobject hfl)) Y

/-- jhMultiplicity is independent of series choice. -/
theorem jhMultiplicity_eq_multiplicityCount {X : C} (hfl : IsFiniteLengthObject X)
    (s : CompositionSeries (Subobject X)) (hs : s.head = ⊥ ∧ s.last = ⊤)
    (Y : C) [Simple Y] :
    jhMultiplicity hfl Y = multiplicityCount s Y := by
  unfold jhMultiplicity
  exact multiplicityCount_eq_of_equivalent _ s
    (by rw [(Classical.choose_spec (exists_compositionSeries_subobject hfl)).1, hs.1])
    (by rw [(Classical.choose_spec (exists_compositionSeries_subobject hfl)).2, hs.2]) Y

end LemmaFeld.TensorCategories.Chapter1
