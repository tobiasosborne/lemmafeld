/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.FittingLemma
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.LocalRing

/-!
# Krull-Schmidt: Exchange Lemma

The exchange lemma is the key technical result for Krull-Schmidt uniqueness:
given two indecomposable decompositions of the same object, the first component
of one is isomorphic to some component of the other.
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]

/-- Helper: sum of π ≫ ι equals identity for biproducts. -/
private lemma biproduct_sum_π_ι {n : ℕ} (f : Fin n → C) :
    ∑ j : Fin n, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f) := by
  apply biproduct.hom_ext'
  intro k
  rw [Preadditive.comp_sum, Category.comp_id]
  conv_lhs =>
    arg 2
    ext j
    rw [← Category.assoc, biproduct.ι_π]
  simp only [dite_comp, zero_comp, Finset.sum_dite_eq, Finset.mem_univ, ↓reduceIte, eqToHom_refl,
    Category.id_comp]

/-- **Exchange Lemma**: Given two indecomposable decompositions of the same object,
the first component of one decomposition is isomorphic to some component of the other.

This is the key lemma for Krull-Schmidt uniqueness. The proof uses:
1. The endomorphism projections Y₀ → X → Zⱼ → X → Y₀ sum to the identity
2. By local ring property, one of these is an isomorphism
3. Since both Y₀ and Zⱼ are indecomposable finite-length, the map Y₀ → Zⱼ is an iso
-/
lemma exchangeLemma {X : C} {n m : ℕ} (hn : 0 < n)
    (Y : Fin n → C) (Z : Fin m → C)
    (hY : ∀ i, Indecomposable (Y i)) (hZ : ∀ j, Indecomposable (Z j))
    (hYfl : ∀ i, IsFiniteLengthObject (Y i)) (hZfl : ∀ j, IsFiniteLengthObject (Z j))
    (iso₁ : X ≅ ⨁ Y) (iso₂ : X ≅ ⨁ Z) :
    ∃ j, Nonempty (Y ⟨0, hn⟩ ≅ Z j) := by
  let Y₀ : C := Y ⟨0, hn⟩
  let f : (j : Fin m) → (Y₀ ⟶ Z j) := fun j =>
    biproduct.ι Y ⟨0, hn⟩ ≫ iso₁.inv ≫ iso₂.hom ≫ biproduct.π Z j
  let g : (j : Fin m) → (Z j ⟶ Y₀) := fun j =>
    biproduct.ι Z j ≫ iso₂.inv ≫ iso₁.hom ≫ biproduct.π Y ⟨0, hn⟩
  let p : Fin m → End Y₀ := fun j => f j ≫ g j
  have sum_eq_id : ∑ i : Fin m, p i = 1 := by
    rw [End.one_def]
    show ∑ j : Fin m, (biproduct.ι Y ⟨0, hn⟩ ≫ iso₁.inv ≫ iso₂.hom ≫ biproduct.π Z j) ≫
         (biproduct.ι Z j ≫ iso₂.inv ≫ iso₁.hom ≫ biproduct.π Y ⟨0, hn⟩) = 𝟙 Y₀
    simp only [Category.assoc]
    have step1 : ∀ j : Fin m,
      biproduct.ι Y ⟨0, hn⟩ ≫ iso₁.inv ≫ iso₂.hom ≫ biproduct.π Z j ≫
      biproduct.ι Z j ≫ iso₂.inv ≫ iso₁.hom ≫ biproduct.π Y ⟨0, hn⟩ =
      biproduct.ι Y ⟨0, hn⟩ ≫ iso₁.inv ≫ iso₂.hom ≫
      ((biproduct.π Z j ≫ biproduct.ι Z j) ≫ iso₂.inv ≫ iso₁.hom ≫ biproduct.π Y ⟨0, hn⟩) := by
      intro j; simp only [Category.assoc]
    simp_rw [step1]
    simp only [← Preadditive.comp_sum]
    have sum_factor : ∑ j : Fin m, (biproduct.π Z j ≫ biproduct.ι Z j) ≫ iso₂.inv ≫ iso₁.hom ≫
                biproduct.π Y ⟨0, hn⟩ =
                iso₂.inv ≫ iso₁.hom ≫ biproduct.π Y ⟨0, hn⟩ := by
      rw [← Preadditive.sum_comp, biproduct_sum_π_ι, Category.id_comp]
    rw [sum_factor]
    simp only [Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, biproduct.ι_π_self]
    rfl
  haveI : IsLocalRing (End Y₀) :=
    isLocalRing_end_of_indecomposable_finiteLength (hY ⟨0, hn⟩) (hYfl ⟨0, hn⟩)
  obtain ⟨j, hj⟩ := exists_isUnit_of_finsum_eq_one p sum_eq_id
  have hfg_iso : IsIso (p j) := by rwa [isUnit_iff_isIso] at hj
  haveI hfg_mono : Mono (f j ≫ g j) := inferInstance
  have hf_mono : Mono (f j) := mono_of_mono_fac (g := g j) (h := f j ≫ g j) rfl
  let q : End (Z j) := g j ≫ f j
  haveI hZj_local : IsLocalRing (End (Z j)) :=
    isLocalRing_end_of_indecomposable_finiteLength (hZ j) (hZfl j)
  have hq_or : IsNilpotent q ∨ IsUnit q := fitting_lemma q (hZ j) (hZfl j)
  have pow_key : ∀ k : ℕ, (p j)^(k + 1) = f j ≫ (q^k) ≫ g j := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.zero_add, pow_one, pow_zero, End.one_def, Category.id_comp]; rfl
    | succ l ihl =>
      rw [pow_succ (p j) (l + 1), ihl, End.mul_def, pow_succ q l, End.mul_def]
      calc p j ≫ f j ≫ (q ^ l) ≫ g j
        = (f j ≫ g j) ≫ f j ≫ (q ^ l) ≫ g j := rfl
      _ = f j ≫ g j ≫ f j ≫ (q ^ l) ≫ g j := by simp only [Category.assoc]
      _ = f j ≫ (g j ≫ f j) ≫ (q ^ l) ≫ g j := by simp only [Category.assoc]
      _ = f j ≫ q ≫ (q ^ l) ≫ g j := rfl
      _ = f j ≫ (q ≫ q ^ l) ≫ g j := by simp only [Category.assoc]
  have hq_unit : IsUnit q := by
    rcases hq_or with ⟨k, hk_eq⟩ | hunit
    · exfalso
      rcases k with _ | k'
      · simp only [pow_zero] at hk_eq
        have hid_eq_zero : 𝟙 (Z j) = 0 := by
          simp only [End.one_def] at hk_eq; exact hk_eq
        have hZj_zero : IsZero (Z j) := (Limits.IsZero.iff_id_eq_zero (Z j)).mpr hid_eq_zero
        exact (hZ j).1 hZj_zero
      · have h_pow_zero : (p j)^(k' + 2) = 0 := by
          rw [pow_key (k' + 1), hk_eq]
          simp only [Limits.zero_comp, Limits.comp_zero]
        have hpj_unit_pow : IsUnit ((p j)^(k' + 2)) := hj.pow (k' + 2)
        rw [h_pow_zero] at hpj_unit_pow
        exact not_isUnit_zero hpj_unit_pow
    · exact hunit
  have hq_iso : IsIso q := by rwa [isUnit_iff_isIso] at hq_unit
  haveI hgf_epi : Epi (g j ≫ f j) := inferInstance
  have hf_epi : Epi (f j) := epi_of_epi_fac (f := g j) (h := g j ≫ f j) rfl
  have hf_iso : IsIso (f j) := isIso_of_mono_of_epi (f j)
  exact ⟨j, ⟨asIso (f j)⟩⟩

end LemmaFeld.TensorCategories.Chapter1
