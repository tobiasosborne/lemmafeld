/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Abelian.Basic
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.FiniteLength

/-!
# Krull-Schmidt: Auxiliary Lemmas

Basic lemmas for the Krull-Schmidt theorem:
- Finite length preservation under isomorphisms and biproducts
- Properties of empty and singleton biproducts
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]

/-- Finite length is preserved under isomorphism (to the target). -/
lemma isFiniteLengthObject_of_iso {X Y : C} (i : X ≅ Y) (hX : IsFiniteLengthObject X) :
    IsFiniteLengthObject Y := by
  have hA := hX.artinian
  have hN := hX.noetherian
  constructor
  · exact isArtinianObject_of_mono i.inv
  · exact isNoetherianObject_of_mono i.inv

/-- Finite length is preserved under isomorphism (source direction). -/
lemma isFiniteLengthObject_of_iso' {X Y : C} (i : X ≅ Y) (hY : IsFiniteLengthObject Y) :
    IsFiniteLengthObject X :=
  isFiniteLengthObject_of_iso i.symm hY

/-- A binary biproduct component has finite length if the biproduct does. -/
lemma isFiniteLengthObject_biprod_fst {X Y : C} (h : IsFiniteLengthObject (X ⊞ Y)) :
    IsFiniteLengthObject X := by
  haveI : IsArtinianObject (X ⊞ Y) := h.artinian
  haveI : IsNoetherianObject (X ⊞ Y) := h.noetherian
  constructor
  · exact isArtinianObject_of_mono (biprod.inl : X ⟶ X ⊞ Y)
  · exact isNoetherianObject_of_mono (biprod.inl : X ⟶ X ⊞ Y)

/-- A binary biproduct component has finite length if the biproduct does. -/
lemma isFiniteLengthObject_biprod_snd {X Y : C} (h : IsFiniteLengthObject (X ⊞ Y)) :
    IsFiniteLengthObject Y := by
  haveI : IsArtinianObject (X ⊞ Y) := h.artinian
  haveI : IsNoetherianObject (X ⊞ Y) := h.noetherian
  constructor
  · exact isArtinianObject_of_mono (biprod.inr : Y ⟶ X ⊞ Y)
  · exact isNoetherianObject_of_mono (biprod.inr : Y ⟶ X ⊞ Y)

/-- The empty biproduct is the zero object. -/
lemma biproduct_empty_isZero : IsZero (⨁ (Fin.elim0 : Fin 0 → C)) := by
  refine ⟨fun Y => ⟨⟨⟨biproduct.desc (fun b => b.elim0)⟩, fun f => ?_⟩⟩,
          fun Y => ⟨⟨⟨biproduct.lift (fun b => b.elim0)⟩, fun f => ?_⟩⟩⟩
  · ext ⟨j, hj⟩
    exact (Nat.not_lt_zero j hj).elim
  · ext ⟨j, hj⟩
    exact (Nat.not_lt_zero j hj).elim

/-- The singleton biproduct is isomorphic to its element. -/
def biproductSingletonIso (X : C) : ⨁ (fun _ : Fin 1 => X) ≅ X where
  hom := biproduct.desc (fun _ => 𝟙 X)
  inv := biproduct.lift (fun _ => 𝟙 X)
  hom_inv_id := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc, Category.id_comp]
    have hi' : i = 0 := Nat.lt_one_iff.mp hi
    have hj' : j = 0 := Nat.lt_one_iff.mp hj
    subst hi' hj'
    simp
  inv_hom_id := by simp [biproduct.lift_desc]

end LemmaFeld.TensorCategories.Chapter1
