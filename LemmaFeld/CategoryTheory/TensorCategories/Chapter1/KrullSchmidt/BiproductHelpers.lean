/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Krull-Schmidt: Biproduct Helpers

Structural lemmas for biproducts:
- `concatFin`: Concatenation of indexed families
- `biproductBiprodIso`: (⨁ f) ⊞ (⨁ g) ≅ ⨁ (concatFin f g)
- `biprodMapIso`: Map iso across binary biproduct
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]

/-- Map iso to binary biproduct. -/
def biprodMapIso {W X Y Z : C} (iWY : W ≅ Y) (iXZ : X ≅ Z) : W ⊞ X ≅ Y ⊞ Z :=
  biprod.mapIso iWY iXZ

/-- Helper: concatenated family of objects. -/
def concatFin {n m : ℕ} (f : Fin n → C) (g : Fin m → C) : Fin (n + m) → C :=
  fun k => if h : k.val < n then f ⟨k.val, h⟩ else g ⟨k.val - n, by omega⟩

lemma concatFin_left {n m : ℕ} (f : Fin n → C) (g : Fin m → C) (i : Fin n) :
    concatFin f g ⟨i.val, by omega⟩ = f i := by
  simp only [concatFin, i.isLt, ↓reduceDIte, Fin.eta]

lemma concatFin_right {n m : ℕ} (f : Fin n → C) (g : Fin m → C) (j : Fin m) :
    concatFin f g ⟨n + j.val, by omega⟩ = g j := by
  simp only [concatFin]; have h : ¬ (n + j.val < n) := by omega
  simp only [h, ↓reduceDIte]; congr 1; simp only [Fin.ext_iff]; omega

lemma concatFin_right' {n m : ℕ} (f : Fin n → C) (g : Fin m → C)
    (k : Fin (n + m)) (h : ¬ k.val < n) : concatFin f g k = g ⟨k.val - n, by omega⟩ := by
  simp only [concatFin, h, ↓reduceDIte]

private lemma add_sub_cancel_of_ge' {n k : ℕ} (h : n ≤ k) : n + (k - n) = k := by omega

private lemma biproduct_ι_cast' {J : Type*} [Fintype J] (h : J → C) [HasBiproduct h]
    (j j' : J) (hj : j = j') : biproduct.ι h j = eqToHom (by rw [hj]) ≫ biproduct.ι h j' := by
  subst hj; simp

private lemma biproduct_ι_fin_eq' {J : Type*} {D : Type*} [Category D] [Preadditive D]
    (p : J → D) [HasBiproduct p] (i j : J) (hij : i = j) :
    biproduct.ι p i = eqToHom (congrArg p hij) ≫ biproduct.ι p j := by
  subst hij; simp

/-- The biproduct of two biproducts is isomorphic to the biproduct over the concatenated index.

This is the key structural lemma for concatenating decompositions.

**Construction:**
- hom: (⨁ f) ⊞ (⨁ g) → ⨁ (concatenated)
  - On left: biproduct.ι f i ↦ biproduct.ι (concat) ⟨i.val, ...⟩
  - On right: biproduct.ι g j ↦ biproduct.ι (concat) ⟨n + j.val, ...⟩
- inv: ⨁ (concatenated) → (⨁ f) ⊞ (⨁ g)
  - For k < n: biproduct.ι k ↦ biproduct.ι f ⟨k, ...⟩ ≫ biprod.inl
  - For k ≥ n: biproduct.ι k ↦ biproduct.ι g ⟨k - n, ...⟩ ≫ biprod.inr
-/
def biproductBiprodIso {n m : ℕ} (f : Fin n → C) (g : Fin m → C) :
    (⨁ f) ⊞ (⨁ g) ≅ ⨁ (concatFin f g) where
  hom := biprod.desc
    (biproduct.desc fun i => eqToHom (concatFin_left f g i).symm ≫
      biproduct.ι (concatFin f g) ⟨i.val, by omega⟩)
    (biproduct.desc fun j => eqToHom (concatFin_right f g j).symm ≫
      biproduct.ι (concatFin f g) ⟨n + j.val, by omega⟩)
  inv := biproduct.desc fun k =>
    if h : k.val < n then
      eqToHom (concatFin_left f g ⟨k.val, h⟩) ≫ biproduct.ι f ⟨k.val, h⟩ ≫ biprod.inl
    else
      eqToHom (concatFin_right' f g k h) ≫ biproduct.ι g ⟨k.val - n, by omega⟩ ≫ biprod.inr
  hom_inv_id := by
    apply biprod.hom_ext'
    · simp only [Category.comp_id]
      rw [show biprod.inl ≫ biprod.desc _ _ ≫ _ =
             (biprod.inl ≫ biprod.desc _ _) ≫ _ from (Category.assoc _ _ _).symm,
           biprod.inl_desc]
      apply biproduct.hom_ext'; intro i
      rw [biproduct.ι_desc_assoc]
      simp only [Category.assoc, biproduct.ι_desc, i.isLt, ↓reduceDIte, eqToHom_trans_assoc,
                 Fin.eta, eqToHom_refl, Category.id_comp]
    · simp only [Category.comp_id]
      rw [show biprod.inr ≫ biprod.desc _ _ ≫ _ =
             (biprod.inr ≫ biprod.desc _ _) ≫ _ from (Category.assoc _ _ _).symm,
           biprod.inr_desc]
      apply biproduct.hom_ext'; intro j
      rw [biproduct.ι_desc_assoc]
      simp only [Category.assoc, biproduct.ι_desc]
      have h : ¬ (n + j.val < n) := by omega
      simp only [h, ↓reduceDIte, eqToHom_trans_assoc]
      have fin_eq : (⟨n + j.val - n, by omega⟩ : Fin m) = j := by
        simp only [Nat.add_sub_cancel_left, Fin.eta]
      rw [biproduct_ι_fin_eq' g _ j fin_eq]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  inv_hom_id := by
    apply biproduct.hom_ext'; intro k
    simp only [biproduct.ι_desc_assoc, Category.comp_id]
    split_ifs with hk
    · simp only [Category.assoc, biprod.inl_desc, biproduct.ι_desc,
                 eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Fin.eta]
    · simp only [Category.assoc, biprod.inr_desc, biproduct.ι_desc]
      have fin_eq : (⟨n + (k.val - n), by omega⟩ : Fin (n + m)) = k :=
        Fin.ext (add_sub_cancel_of_ge' (Nat.not_lt.mp hk))
      rw [eqToHom_trans_assoc, biproduct_ι_cast' _ _ _ fin_eq]
      simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

end LemmaFeld.TensorCategories.Chapter1
