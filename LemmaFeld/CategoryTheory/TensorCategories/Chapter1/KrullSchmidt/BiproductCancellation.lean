/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.BiproductHelpers

/-!
# Krull-Schmidt: Biproduct Cancellation Infrastructure

These lemmas enable the "cancel matching component" step in KS uniqueness:
Given `Y₀ ⊞ rest_Y ≅ Z_j ⊞ rest_Z` with `Y₀ ≅ Z_j`, conclude `rest_Y ≅ rest_Z`.

Key constructions:
- `finSwapFront`: Equivalence that swaps index j to position 0
- `biproductSwapFrontIso`: Reindex biproduct via swap
- `finTail`, `biproductHeadTailIso`: Head-tail decomposition of biproducts
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]

/-- Swap j to position 0 in Fin n. Uses Equiv.swap. -/
def finSwapFront {n : ℕ} (j : Fin n) : Fin n ≃ Fin n :=
  Equiv.swap j ⟨0, j.pos⟩

@[simp]
lemma finSwapFront_apply_self {n : ℕ} (j : Fin n) :
    finSwapFront j j = ⟨0, j.pos⟩ := Equiv.swap_apply_left j ⟨0, j.pos⟩

@[simp]
lemma finSwapFront_apply_zero {n : ℕ} (j : Fin n) :
    finSwapFront j ⟨0, j.pos⟩ = j := Equiv.swap_apply_right j ⟨0, j.pos⟩

lemma finSwapFront_symm {n : ℕ} (j : Fin n) : (finSwapFront j).symm = finSwapFront j := by
  unfold finSwapFront
  ext k
  simp only [Equiv.symm_swap]

/-- Biproduct reindexed by swapping j to front. -/
def biproductSwapFrontIso {n : ℕ} (f : Fin n → C) (j : Fin n) :
    ⨁ f ≅ ⨁ (f ∘ (finSwapFront j).symm) := by
  have hw : ∀ k, (f ∘ (finSwapFront j).symm) ((finSwapFront j) k) ≅ f k := fun k => by
    simp only [Function.comp_apply, Equiv.symm_apply_apply]; exact Iso.refl _
  exact biproduct.whiskerEquiv (finSwapFront j) hw

/-- After swapping j to front, component 0 is f j. -/
lemma biproductSwapFront_zero {n : ℕ} (f : Fin n → C) (j : Fin n) :
    (f ∘ (finSwapFront j).symm) ⟨0, j.pos⟩ = f j := by
  simp only [Function.comp_apply, finSwapFront_symm, finSwapFront_apply_zero]

/-- Tail of a family, for head-tail splitting. -/
def finTail {n : ℕ} (hn : 0 < n) (f : Fin n → C) : Fin (n - 1) → C :=
  fun i => f ⟨i.val + 1, by omega⟩

/-- Head-tail split for biproducts: ⨁ f ≅ f 0 ⊞ ⨁ (tail f) for n > 0. -/
def biproductHeadTailIso {n : ℕ} (hn : 0 < n) (f : Fin n → C) :
    ⨁ f ≅ f ⟨0, hn⟩ ⊞ ⨁ (finTail hn f) := by
  let head : Fin 1 → C := fun _ => f ⟨0, hn⟩
  let tail : Fin (n - 1) → C := finTail hn f
  have hn_eq : 1 + (n - 1) = n := by omega
  let e : Fin n ≃ Fin (1 + (n - 1)) := {
    toFun := fun i => ⟨i.val, by omega⟩
    invFun := fun k => ⟨k.val, by omega⟩
    left_inv := fun i => by ext; simp
    right_inv := fun k => by ext; simp
  }
  have heq : ∀ k : Fin (1 + (n - 1)), concatFin head tail k = f ⟨k.val, by omega⟩ := fun k => by
    simp only [concatFin, head, tail, finTail]
    by_cases hk : k.val < 1
    · simp only [hk, ↓reduceDIte]; congr 1; ext
      exact (Nat.lt_one_iff.mp hk).symm
    · simp only [hk, ↓reduceDIte]; congr 1; ext
      have hk_ge : k.val ≥ 1 := Nat.not_lt.mp hk
      exact Nat.sub_add_cancel hk_ge
  have hw : ∀ i, f (e.symm (e i)) ≅ f i := fun i => eqToIso (by simp only [Equiv.symm_apply_apply])
  let iso_reindex : ⨁ f ≅ ⨁ (f ∘ e.symm) := biproduct.whiskerEquiv e hw
  have hw2 : ∀ k, (f ∘ e.symm) k ≅ f ⟨k.val, by omega⟩ := fun k =>
    eqToIso (by simp only [Function.comp_apply, e]; rfl)
  let iso_cast : ⨁ (f ∘ e.symm) ≅ ⨁ (fun k : Fin (1 + (n - 1)) => f ⟨k.val, by omega⟩) :=
    biproduct.mapIso hw2
  let iso_concat : ⨁ (fun k : Fin (1 + (n - 1)) => f ⟨k.val, by omega⟩) ≅ ⨁ (concatFin head tail) :=
    biproduct.mapIso (fun k => eqToIso (heq k).symm)
  let iso_split : ⨁ (concatFin head tail) ≅ (⨁ head) ⊞ (⨁ tail) :=
    (biproductBiprodIso head tail).symm
  let iso_head : ⨁ head ≅ f ⟨0, hn⟩ := by
    refine ⟨biproduct.desc (fun _ => 𝟙 _), biproduct.lift (fun _ => 𝟙 _), ?_, ?_⟩
    · ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc, Category.id_comp]
      have hi' : i = 0 := Nat.lt_one_iff.mp hi
      have hj' : j = 0 := Nat.lt_one_iff.mp hj
      subst hi' hj'
      simp only [biproduct.ι_π_self, head]
    · simp [biproduct.lift_desc]
  exact iso_reindex ≪≫ iso_cast ≪≫ iso_concat ≪≫ iso_split ≪≫ biprod.mapIso iso_head (Iso.refl _)

/-- finSwapFront is self-inverse (swap is involutive). -/
@[simp]
lemma finSwapFront_apply_apply {n : ℕ} (j k : Fin n) :
    finSwapFront j (finSwapFront j k) = k := by
  simp only [finSwapFront, Equiv.swap_apply_self]

/-! ## Simp lemmas for biproductHeadTailIso

The key insight is to use `Iso.comp_inv_eq` and `Iso.eq_inv_comp`:
- To prove `biprod.inl ≫ inv = X`, show that `X ≫ hom = biprod.inl`
- To prove `hom ≫ biprod.fst = Y`, show directly by unfolding

We first establish the "hom direction" lemmas, then derive the "inv direction" from them.
-/

/-- Index 0 injection composed with biproductHeadTailIso.hom gives biprod.inl.

**Proof sketch:** Trace through the 5-way iso composition:
1. biproduct.ι f 0 ≫ whiskerEquiv.hom → eqToHom _ ≫ biproduct.ι (f ∘ e.symm) (e 0)
2. ... ≫ mapIso (iso_cast).hom → eqToHom _ ≫ biproduct.ι _ _
3. ... ≫ mapIso (iso_concat).hom → eqToHom _ ≫ biproduct.ι (concatFin head tail) ⟨0, _⟩
4. ... ≫ biproductBiprodIso.inv → (since 0 < 1) eqToHom _ ≫ biproduct.ι head 0 ≫ biprod.inl
5. ... ≫ biprod.mapIso.hom → (by inl_map) iso_head.hom ≫ biprod.inl
6. biproduct.ι head 0 ≫ iso_head.hom = 𝟙 (since iso_head.hom = biproduct.desc (fun _ => 𝟙))
7. Collapse eqToHom chain to 𝟙 ≫ biprod.inl = biprod.inl

**Blocking issue:** The nested composition structure blocks `biproduct.ι_map` rewriting
due to `eqToIso.inv` prefix terms. Need more sophisticated conv targeting or manual calc.
-/
lemma biproductHeadTailIso_ι_zero_hom {n : ℕ} (hn : 0 < n) (f : Fin n → C) :
    biproduct.ι f ⟨0, hn⟩ ≫ (biproductHeadTailIso hn f).hom = biprod.inl := by
  unfold biproductHeadTailIso
  simp only [Iso.trans_hom]
  rw [biproduct.whiskerEquiv_hom]
  simp only [biproduct.ι_desc_assoc, biproduct.mapIso_hom, Category.assoc]
  -- Goal: (eqToIso _).inv ≫ biproduct.ι _ (e 0) ≫ biproduct.map _ ≫ biproduct.map _ ≫ ...
  -- Strategy: rewrite ι ≫ map ≫ map to _ ≫ _ ≫ ι using ι_map twice (with reassoc form)
  rw [biproduct.ι_map_assoc, biproduct.ι_map_assoc]
  -- Now: (eqToIso _).inv ≫ (eqToIso _).hom ≫ ... ≫ biproduct.ι (concatFin _ _) ⟨0, _⟩ ≫ ...
  simp only [Iso.inv_hom_id_assoc]
  -- Thread through biproductBiprodIso.symm.hom
  simp only [Iso.symm_hom, biproductBiprodIso]
  -- 0 < 1, so take the left branch
  simp only [Nat.lt_one_iff]
  -- Use aesop_cat to close the remaining goal
  aesop_cat

/-- The (1,1) component of biproductHeadTailIso.hom projects to index 0. -/
@[simp]
lemma biproductHeadTailIso_hom_fst {n : ℕ} (hn : 0 < n) (f : Fin n → C) :
    (biproductHeadTailIso hn f).hom ≫ biprod.fst = biproduct.π f ⟨0, hn⟩ := by
  -- Use biproduct extensionality for morphisms FROM biproducts:
  -- Two morphisms g, h : ⨁ f ⟶ X are equal iff ι j ≫ g = ι j ≫ h for all j
  apply biproduct.hom_ext'; intro j
  by_cases hj : j = ⟨0, hn⟩
  · -- j = 0: use ι_zero_hom
    subst hj
    rw [← Category.assoc, biproductHeadTailIso_ι_zero_hom, biprod.inl_fst, biproduct.ι_π_self]
  · -- j ≠ 0: both sides are zero
    -- RHS: ι j ≫ π 0 = 0 since j ≠ 0
    rw [biproduct.ι_π_ne _ hj]
    -- For LHS: thread through the composition like in ι_zero_hom
    unfold biproductHeadTailIso
    simp only [Iso.trans_hom, Category.assoc]
    rw [biproduct.whiskerEquiv_hom]
    simp only [biproduct.ι_desc_assoc, biproduct.mapIso_hom, Category.assoc]
    rw [biproduct.ι_map_assoc, biproduct.ι_map_assoc]
    simp only [Iso.inv_hom_id_assoc]
    simp only [Iso.symm_hom, biproductBiprodIso]
    -- j.val ≥ 1 since j ≠ ⟨0, hn⟩
    have hj_nlt : ¬ j.val < 1 := by
      intro h
      exact hj (Fin.ext (Nat.lt_one_iff.mp h))
    aesop_cat

/-- Injection composed with biproductHeadTailIso.inv gives the head inclusion.
This is the key simp lemma for computing through head-tail decompositions. -/
@[simp]
lemma biproductHeadTailIso_inl_inv {n : ℕ} (hn : 0 < n) (f : Fin n → C) :
    biprod.inl ≫ (biproductHeadTailIso hn f).inv = biproduct.ι f ⟨0, hn⟩ := by
  -- Use Iso.comp_inv_eq: X ≫ inv = Y ↔ X = Y ≫ hom
  rw [Iso.comp_inv_eq]
  exact (biproductHeadTailIso_ι_zero_hom hn f).symm

end LemmaFeld.TensorCategories.Chapter1
