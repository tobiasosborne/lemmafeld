/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.Defs
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.Auxiliary
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.BiproductHelpers

/-!
# Krull-Schmidt: Uniqueness Helper Lemmas

Various lemmas used in the uniqueness proof:
- Zero propagation through biproducts
- Finite length propagation through biproducts
- Indecomposability propagation through isomorphisms
- A biproduct of >1 indecomposables is decomposable
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]

/-- A biproduct summand of a zero object is zero. -/
lemma isZero_component_of_isZero_biproduct {n : ℕ} (f : Fin n → C)
    (hZ : IsZero (⨁ f)) (i : Fin n) : IsZero (f i) := by
  rw [IsZero.iff_id_eq_zero]
  have h1 : biproduct.ι f i ≫ biproduct.π f i = 𝟙 (f i) := biproduct.ι_π_self f i
  have h2 : biproduct.ι f i ≫ biproduct.π f i = 0 := by
    have hι := hZ.eq_zero_of_tgt (biproduct.ι f i)
    rw [hι, Limits.zero_comp]
  rw [← h1, h2]

/-- If X is zero and X ≅ ⨁ f with all f i indecomposable, then n = 0. -/
lemma eq_zero_of_isZero_indecomposable_decomposition {n : ℕ} (f : Fin n → C)
    (hf : ∀ i, Indecomposable (f i)) (Y : C) (hY : IsZero Y)
    (e : Y ≅ ⨁ f) : n = 0 := by
  by_contra h
  push_neg at h
  have hn : 0 < n := Nat.pos_of_ne_zero h
  have hZbiprod : IsZero (⨁ f) := hY.of_iso e.symm
  have hZf0 : IsZero (f ⟨0, hn⟩) := isZero_component_of_isZero_biproduct f hZbiprod ⟨0, hn⟩
  exact (hf ⟨0, hn⟩).1 hZf0

/-- Finite length transfer through biproduct iso. -/
lemma isFiniteLengthObject_of_biproduct_iso {n : ℕ} {X : C} (f : Fin n → C)
    (e : X ≅ ⨁ f) (hX : IsFiniteLengthObject X) (i : Fin n) : IsFiniteLengthObject (f i) := by
  have hBiprod : IsFiniteLengthObject (⨁ f) := isFiniteLengthObject_of_iso e hX
  haveI : IsArtinianObject (⨁ f) := hBiprod.artinian
  haveI : IsNoetherianObject (⨁ f) := hBiprod.noetherian
  constructor
  · exact isArtinianObject_of_mono (biproduct.ι f i)
  · exact isNoetherianObject_of_mono (biproduct.ι f i)

/-- Indecomposability transfers through isomorphisms. -/
lemma indecomposable_of_iso_indecomposable {X Y : C} (hX : Indecomposable X) (e : X ≅ Y) :
    Indecomposable Y := by
  constructor
  · intro hYz
    exact hX.1 (hYz.of_iso e)
  · intro A B eAB
    have eXAB : X ≅ A ⊞ B := e ≪≫ eAB
    exact hX.2 A B eXAB

/-- When n = 1, the biproduct over Fin n is isomorphic to the single component. -/
def biproductSingletonIso' {n : ℕ} (hn : n = 1) (f : Fin n → C) :
    ⨁ f ≅ f ⟨0, by omega⟩ where
  hom := biproduct.π f ⟨0, by omega⟩
  inv := biproduct.ι f ⟨0, by omega⟩
  hom_inv_id := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Category.assoc, biproduct.ι_π_assoc, Category.id_comp]
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0 hj0
    simp [biproduct.ι_π_self]
  inv_hom_id := biproduct.ι_π_self f ⟨0, by omega⟩

/-- Helper: if a biproduct has a nonzero component, the biproduct is nonzero. -/
private lemma not_isZero_biproduct_of_component {J : Type*} [Fintype J] (g : J → C)
    [HasBiproduct g] (j : J) (h : ¬IsZero (g j)) : ¬IsZero (⨁ g) := by
  intro hZ
  apply h
  rw [Limits.IsZero.iff_id_eq_zero]
  have hι : biproduct.ι g j = 0 := hZ.eq_of_tgt _ _
  calc 𝟙 (g j) = biproduct.ι g j ≫ biproduct.π g j := (biproduct.ι_π_self g j).symm
    _ = 0 ≫ biproduct.π g j := by rw [hι]
    _ = 0 := zero_comp

/-- For n > 1, concatFin of singleton head and (n-1)-element tail equals f (reindexed). -/
private lemma concatFin_eq_reindex {n : ℕ} (hn : 1 ≤ n) (f : Fin n → C) :
    concatFin (fun _ : Fin 1 => f ⟨0, by omega⟩)
              (fun i : Fin (n - 1) => f ⟨i.val + 1, by omega⟩) =
    (fun k : Fin (1 + (n - 1)) => f ⟨k.val, by omega⟩) := by
  ext k
  simp only [concatFin]
  by_cases hk : k.val < 1
  · simp only [hk, ↓reduceDIte]
    have hk0 : k.val = 0 := by omega
    congr 1; ext; simp [hk0]
  · simp only [hk, ↓reduceDIte]
    have hk_ge : k.val ≥ 1 := by omega
    congr 1; ext
    exact Nat.sub_add_cancel hk_ge

/-- A biproduct of indecomposables with more than one component is decomposable. -/
lemma not_indecomposable_of_biproduct_gt_one {n : ℕ} (f : Fin n → C) (hn : 1 < n)
    (hf : ∀ i, Indecomposable (f i)) : ¬Indecomposable (⨁ f) := by
  intro ⟨hnonzero, hdecomp⟩
  have h0 : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
  have h1 : 1 < n := hn
  have hf0_nz : ¬IsZero (f ⟨0, h0⟩) := (hf ⟨0, h0⟩).1
  have hf1_nz : ¬IsZero (f ⟨1, h1⟩) := (hf ⟨1, h1⟩).1
  let head : Fin 1 → C := fun _ => f ⟨0, h0⟩
  let tail : Fin (n - 1) → C := fun i => f ⟨i.val + 1, by omega⟩
  have hn_eq : 1 + (n - 1) = n := by omega
  have hconcat : concatFin head tail = (fun k : Fin (1 + (n - 1)) => f ⟨k.val, by omega⟩) :=
    concatFin_eq_reindex (by omega : 1 ≤ n) f
  have hn1 : 1 + (n - 1) = n := hn_eq
  let e : Fin n ≃ Fin (1 + (n - 1)) := {
    toFun := fun i => ⟨i.val, by omega⟩
    invFun := fun k => ⟨k.val, by omega⟩
    left_inv := fun i => by ext; simp
    right_inv := fun k => by ext; simp
  }
  let g := fun k : Fin (1 + (n - 1)) => f ⟨k.val, by omega⟩
  have iso_reindex : ⨁ f ≅ ⨁ g :=
    biproduct.whiskerEquiv e (fun i => eqToIso (by simp only [g, e]; rfl))
  have iso_concat : ⨁ g ≅ ⨁ (concatFin head tail) :=
    biproduct.whiskerEquiv (Equiv.refl _) (fun k => eqToIso (by
      simp only [Equiv.refl_apply]
      exact congrFun hconcat k))
  let split_iso : ⨁ f ≅ (⨁ head) ⊞ (⨁ tail) :=
    iso_reindex ≪≫ iso_concat ≪≫ (biproductBiprodIso head tail).symm
  have h_decomp := hdecomp (⨁ head) (⨁ tail) split_iso
  have h_head_nz : ¬IsZero (⨁ head) := by
    have : ⨁ head ≅ f ⟨0, h0⟩ := biproductSingletonIso (f ⟨0, h0⟩)
    intro hZ
    exact hf0_nz (hZ.of_iso this.symm)
  have h_tail_nz : ¬IsZero (⨁ tail) := by
    have h1' : (1 : ℕ) < n := h1
    have hn1 : 0 < n - 1 := by omega
    have htail0 : tail ⟨0, hn1⟩ = f ⟨1, h1⟩ := by simp [tail]
    rw [← htail0] at hf1_nz
    exact not_isZero_biproduct_of_component tail ⟨0, hn1⟩ hf1_nz
  rcases h_decomp with hZ_head | hZ_tail
  · exact h_head_nz hZ_head
  · exact h_tail_nz hZ_tail

end LemmaFeld.TensorCategories.Chapter1
