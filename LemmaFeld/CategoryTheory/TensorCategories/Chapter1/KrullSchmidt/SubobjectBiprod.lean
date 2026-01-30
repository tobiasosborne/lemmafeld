/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Subobject.Basic
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.Auxiliary

/-!
# Krull-Schmidt: Subobject Infrastructure for Biproducts

This file provides the subobject-level infrastructure needed for the
well-founded recursion in the Krull-Schmidt existence proof.

Key results:
- When X ≅ Y ⊕ Z, Y and Z embed as proper subobjects of X (if both nonzero)
- Transfer of finite length to subobjects
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]

/-- The subobject of X given by Y when X ≅ Y ⊕ Z. -/
def subobjectOfBiprodFst {X Y Z : C} (i : X ≅ Y ⊞ Z) : Subobject X :=
  Subobject.mk (biprod.inl ≫ i.inv)

/-- The subobject of X given by Z when X ≅ Y ⊕ Z. -/
def subobjectOfBiprodSnd {X Y Z : C} (i : X ≅ Y ⊞ Z) : Subobject X :=
  Subobject.mk (biprod.inr ≫ i.inv)

/-- If biprod.inl : Y → Y ⊕ Z is an iso, then Z is zero. -/
lemma isZero_of_isIso_biprod_inl {Y Z : C} (h : IsIso (biprod.inl : Y ⟶ Y ⊞ Z)) : IsZero Z := by
  haveI := h
  rw [IsZero.iff_id_eq_zero]
  have heq : inv (biprod.inl : Y ⟶ Y ⊞ Z) = (biprod.fst : Y ⊞ Z ⟶ Y) := by
    apply (cancel_epi (biprod.inl : Y ⟶ Y ⊞ Z)).mp
    simp
  have hzero : (biprod.inr : Z ⟶ Y ⊞ Z) ≫ inv (biprod.inl : Y ⟶ Y ⊞ Z) = 0 := by
    rw [heq, biprod.inr_fst]
  have step1 : (biprod.inr : Z ⟶ Y ⊞ Z) ≫ biprod.snd =
               biprod.inr ≫ (inv (biprod.inl : Y ⟶ Y ⊞ Z) ≫ biprod.inl) ≫ biprod.snd := by
    congr 1
    rw [IsIso.inv_hom_id, Category.id_comp]
  have step2 : biprod.inr ≫ (inv (biprod.inl : Y ⟶ Y ⊞ Z) ≫ biprod.inl) ≫ biprod.snd =
               (biprod.inr ≫ inv (biprod.inl : Y ⟶ Y ⊞ Z)) ≫
               ((biprod.inl : Y ⟶ Y ⊞ Z) ≫ biprod.snd) := by
    simp only [Category.assoc]
  have step3 : (biprod.inr ≫ inv (biprod.inl : Y ⟶ Y ⊞ Z)) ≫
               ((biprod.inl : Y ⟶ Y ⊞ Z) ≫ biprod.snd) = 0 := by
    rw [hzero, biprod.inl_snd, zero_comp]
  rw [← biprod.inr_snd, step1, step2, step3]

/-- If biprod.inr : Z → Y ⊕ Z is an iso, then Y is zero. -/
lemma isZero_of_isIso_biprod_inr {Y Z : C} (h : IsIso (biprod.inr : Z ⟶ Y ⊞ Z)) : IsZero Y := by
  haveI := h
  rw [IsZero.iff_id_eq_zero]
  have heq : inv (biprod.inr : Z ⟶ Y ⊞ Z) = (biprod.snd : Y ⊞ Z ⟶ Z) := by
    apply (cancel_epi (biprod.inr : Z ⟶ Y ⊞ Z)).mp
    simp
  have hzero : (biprod.inl : Y ⟶ Y ⊞ Z) ≫ inv (biprod.inr : Z ⟶ Y ⊞ Z) = 0 := by
    rw [heq, biprod.inl_snd]
  have step1 : (biprod.inl : Y ⟶ Y ⊞ Z) ≫ biprod.fst =
               biprod.inl ≫ (inv (biprod.inr : Z ⟶ Y ⊞ Z) ≫ biprod.inr) ≫ biprod.fst := by
    congr 1
    rw [IsIso.inv_hom_id, Category.id_comp]
  have step2 : biprod.inl ≫ (inv (biprod.inr : Z ⟶ Y ⊞ Z) ≫ biprod.inr) ≫ biprod.fst =
               (biprod.inl ≫ inv (biprod.inr : Z ⟶ Y ⊞ Z)) ≫
               ((biprod.inr : Z ⟶ Y ⊞ Z) ≫ biprod.fst) := by
    simp only [Category.assoc]
  have step3 : (biprod.inl ≫ inv (biprod.inr : Z ⟶ Y ⊞ Z)) ≫
               ((biprod.inr : Z ⟶ Y ⊞ Z) ≫ biprod.fst) = 0 := by
    rw [hzero, biprod.inr_fst, zero_comp]
  rw [← biprod.inl_fst, step1, step2, step3]

/-- When X ≅ Y ⊕ Z with Z nonzero, the subobject from Y is proper (< ⊤). -/
lemma subobjectOfBiprodFst_lt_top {X Y Z : C} (i : X ≅ Y ⊞ Z) (hZ : ¬IsZero Z) :
    subobjectOfBiprodFst i < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h
  have hiso : IsIso (biprod.inl ≫ i.inv) :=
    (Subobject.isIso_iff_mk_eq_top (biprod.inl ≫ i.inv)).mpr h
  haveI : IsIso i.inv := inferInstance
  have hinl : IsIso (biprod.inl : Y ⟶ Y ⊞ Z) := by
    have : biprod.inl = (biprod.inl ≫ i.inv) ≫ i.hom := by simp
    rw [this]; infer_instance
  exact hZ (isZero_of_isIso_biprod_inl hinl)

/-- When X ≅ Y ⊕ Z with Y nonzero, the subobject from Z is proper (< ⊤). -/
lemma subobjectOfBiprodSnd_lt_top {X Y Z : C} (i : X ≅ Y ⊞ Z) (hY : ¬IsZero Y) :
    subobjectOfBiprodSnd i < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h
  have hiso : IsIso (biprod.inr ≫ i.inv) :=
    (Subobject.isIso_iff_mk_eq_top (biprod.inr ≫ i.inv)).mpr h
  haveI : IsIso i.inv := inferInstance
  have hinr : IsIso (biprod.inr : Z ⟶ Y ⊞ Z) := by
    have : biprod.inr = (biprod.inr ≫ i.inv) ≫ i.hom := by simp
    rw [this]; infer_instance
  exact hY (isZero_of_isIso_biprod_inr hinr)

/-- The underlying object of the first biproduct subobject is isomorphic to Y. -/
def subobjectOfBiprodFst_underlyingIso {X Y Z : C} (i : X ≅ Y ⊞ Z) :
    Subobject.underlying.obj (subobjectOfBiprodFst i) ≅ Y :=
  Subobject.underlyingIso _

/-- The underlying object of the second biproduct subobject is isomorphic to Z. -/
def subobjectOfBiprodSnd_underlyingIso {X Y Z : C} (i : X ≅ Y ⊞ Z) :
    Subobject.underlying.obj (subobjectOfBiprodSnd i) ≅ Z :=
  Subobject.underlyingIso _

/-- The underlying object of a subobject of a finite length object has finite length. -/
lemma isFiniteLengthObject_subobject {X : C} (hX : IsFiniteLengthObject X)
    (S : Subobject X) : IsFiniteLengthObject (Subobject.underlying.obj S) := by
  have hA := hX.artinian
  have hN := hX.noetherian
  constructor
  · exact isArtinianObject_of_mono S.arrow
  · exact isNoetherianObject_of_mono S.arrow

/-- When S : Subobject X and underlying.obj S ≅ Y ⊕ Z, create the subobject for Y. -/
def subobjectOfBiprodFst_via {X : C} (S : Subobject X) {Y Z : C}
    (iU : Subobject.underlying.obj S ≅ Y ⊞ Z) : Subobject X :=
  Subobject.mk (biprod.inl ≫ iU.inv ≫ S.arrow)

/-- When S : Subobject X and underlying.obj S ≅ Y ⊕ Z, create the subobject for Z. -/
def subobjectOfBiprodSnd_via {X : C} (S : Subobject X) {Y Z : C}
    (iU : Subobject.underlying.obj S ≅ Y ⊞ Z) : Subobject X :=
  Subobject.mk (biprod.inr ≫ iU.inv ≫ S.arrow)

/-- The first biproduct subobject is strictly less than S when Z is nonzero. -/
lemma subobjectOfBiprodFst_via_lt {X : C} (S : Subobject X) {Y Z : C}
    (iU : Subobject.underlying.obj S ≅ Y ⊞ Z) (hZ : ¬IsZero Z) :
    subobjectOfBiprodFst_via S iU < S := by
  rw [lt_iff_le_and_ne]
  constructor
  · unfold subobjectOfBiprodFst_via
    exact Subobject.mk_le_of_comm (biprod.inl ≫ iU.inv) (by simp [Category.assoc])
  · intro heq
    unfold subobjectOfBiprodFst_via at heq
    let φ := Subobject.isoOfEq _ _ heq
    let ψ := Subobject.underlyingIso (biprod.inl ≫ iU.inv ≫ S.arrow)
    let θ : Y ≅ Subobject.underlying.obj S := ψ.symm ≪≫ φ
    have hθ : θ.hom ≫ S.arrow = (biprod.inl ≫ iU.inv) ≫ S.arrow := by
      have key : ψ.inv ≫ (Subobject.mk (biprod.inl ≫ iU.inv ≫ S.arrow)).arrow =
                 biprod.inl ≫ iU.inv ≫ S.arrow := Subobject.underlyingIso_arrow _
      have hφ : φ.hom ≫ S.arrow = (Subobject.mk (biprod.inl ≫ iU.inv ≫ S.arrow)).arrow := by
        simp only [φ, Subobject.isoOfEq, Subobject.ofLE_arrow]
      simp only [θ, Iso.trans_hom, Iso.symm_hom, Category.assoc, hφ, key]
    have hθ_val : θ.hom = biprod.inl ≫ iU.inv := (cancel_mono S.arrow).mp hθ
    have hiso : IsIso (biprod.inl ≫ iU.inv) := by rw [← hθ_val]; infer_instance
    haveI : IsIso (biprod.inl : Y ⟶ Y ⊞ Z) := by
      have h1 : biprod.inl = (biprod.inl ≫ iU.inv) ≫ iU.hom := by simp
      rw [h1]; infer_instance
    exact hZ (isZero_of_isIso_biprod_inl this)

/-- The second biproduct subobject is strictly less than S when Y is nonzero. -/
lemma subobjectOfBiprodSnd_via_lt {X : C} (S : Subobject X) {Y Z : C}
    (iU : Subobject.underlying.obj S ≅ Y ⊞ Z) (hY : ¬IsZero Y) :
    subobjectOfBiprodSnd_via S iU < S := by
  rw [lt_iff_le_and_ne]
  constructor
  · unfold subobjectOfBiprodSnd_via
    exact Subobject.mk_le_of_comm (biprod.inr ≫ iU.inv) (by simp [Category.assoc])
  · intro heq
    unfold subobjectOfBiprodSnd_via at heq
    let φ := Subobject.isoOfEq _ _ heq
    let ψ := Subobject.underlyingIso (biprod.inr ≫ iU.inv ≫ S.arrow)
    let θ : Z ≅ Subobject.underlying.obj S := ψ.symm ≪≫ φ
    have hθ : θ.hom ≫ S.arrow = (biprod.inr ≫ iU.inv) ≫ S.arrow := by
      have key : ψ.inv ≫ (Subobject.mk (biprod.inr ≫ iU.inv ≫ S.arrow)).arrow =
                 biprod.inr ≫ iU.inv ≫ S.arrow := Subobject.underlyingIso_arrow _
      have hφ : φ.hom ≫ S.arrow = (Subobject.mk (biprod.inr ≫ iU.inv ≫ S.arrow)).arrow := by
        simp only [φ, Subobject.isoOfEq, Subobject.ofLE_arrow]
      simp only [θ, Iso.trans_hom, Iso.symm_hom, Category.assoc, hφ, key]
    have hθ_val : θ.hom = biprod.inr ≫ iU.inv := (cancel_mono S.arrow).mp hθ
    have hiso : IsIso (biprod.inr ≫ iU.inv) := by rw [← hθ_val]; infer_instance
    haveI : IsIso (biprod.inr : Z ⟶ Y ⊞ Z) := by
      have h1 : biprod.inr = (biprod.inr ≫ iU.inv) ≫ iU.hom := by simp
      rw [h1]; infer_instance
    exact hY (isZero_of_isIso_biprod_inr this)

/-- The underlying object of subobjectOfBiprodFst_via is isomorphic to Y. -/
def subobjectOfBiprodFst_via_underlyingIso {X : C} (S : Subobject X) {Y Z : C}
    (iU : Subobject.underlying.obj S ≅ Y ⊞ Z) :
    Subobject.underlying.obj (subobjectOfBiprodFst_via S iU) ≅ Y :=
  Subobject.underlyingIso _

/-- The underlying object of subobjectOfBiprodSnd_via is isomorphic to Z. -/
def subobjectOfBiprodSnd_via_underlyingIso {X : C} (S : Subobject X) {Y Z : C}
    (iU : Subobject.underlying.obj S ≅ Y ⊞ Z) :
    Subobject.underlying.obj (subobjectOfBiprodSnd_via S iU) ≅ Z :=
  Subobject.underlyingIso _

end LemmaFeld.TensorCategories.Chapter1
