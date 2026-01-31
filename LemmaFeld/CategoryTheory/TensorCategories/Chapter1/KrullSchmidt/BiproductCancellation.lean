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

@[simp]
lemma finSwapFront_symm {n : ℕ} (j : Fin n) : (finSwapFront j).symm = finSwapFront j := by
  unfold finSwapFront
  ext k
  simp only [Equiv.symm_swap]

/-- finSwapFront is self-inverse (swap is involutive). -/
@[simp]
lemma finSwapFront_apply_apply {n : ℕ} (j k : Fin n) :
    finSwapFront j (finSwapFront j k) = k := by
  simp only [finSwapFront, Equiv.swap_apply_self]

/-! ## Tail Permutation Lifting

Helper for constructing the full permutation in KS uniqueness from a tail permutation.
-/

/-- Lift a tail permutation to Fin n by fixing 0. -/
def liftTailPerm {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin (n - 1))) : Equiv.Perm (Fin n) where
  toFun i := if hi : i.val = 0 then ⟨0, hn⟩ else
    have hi_lt : i.val - 1 < n - 1 :=
      Nat.sub_lt_sub_right (Nat.one_le_iff_ne_zero.mpr hi) i.isLt
    ⟨(σ ⟨i.val - 1, hi_lt⟩).val + 1, Nat.add_lt_of_lt_sub (σ ⟨i.val - 1, hi_lt⟩).isLt⟩
  invFun k := if hk : k.val = 0 then ⟨0, hn⟩ else
    have hk_lt : k.val - 1 < n - 1 :=
      Nat.sub_lt_sub_right (Nat.one_le_iff_ne_zero.mpr hk) k.isLt
    ⟨(σ.symm ⟨k.val - 1, hk_lt⟩).val + 1, Nat.add_lt_of_lt_sub (σ.symm ⟨k.val - 1, hk_lt⟩).isLt⟩
  left_inv i := by
    by_cases hi : i.val = 0
    · simp only [dif_pos hi]
      ext; exact hi.symm
    · simp only [dif_neg hi]
      have hi_lt : i.val - 1 < n - 1 := Nat.sub_lt_sub_right (Nat.one_le_iff_ne_zero.mpr hi) i.isLt
      have hi' : ¬ ((σ ⟨i.val - 1, hi_lt⟩).val + 1) = 0 := by omega
      simp only [dif_neg hi']
      -- Goal: ⟨(σ.symm ⟨(σ ⟨i.val - 1, _⟩).val + 1 - 1, _⟩).val + 1, _⟩ = i
      ext
      simp only [Nat.add_sub_cancel]
      -- Goal: (σ.symm ⟨(σ ⟨i.val - 1, _⟩).val, _⟩).val + 1 = i.val
      -- The inner Fin has same .val as (σ ⟨i.val - 1, hi_lt⟩)
      have heq : (⟨(σ ⟨i.val - 1, hi_lt⟩).val, _⟩ : Fin (n - 1)) = σ ⟨i.val - 1, hi_lt⟩ :=
        Fin.ext rfl
      rw [heq, Equiv.symm_apply_apply]
      exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)
  right_inv k := by
    by_cases hk : k.val = 0
    · simp only [dif_pos hk]
      ext; exact hk.symm
    · simp only [dif_neg hk]
      have hk_lt : k.val - 1 < n - 1 := Nat.sub_lt_sub_right (Nat.one_le_iff_ne_zero.mpr hk) k.isLt
      have hk' : ¬ ((σ.symm ⟨k.val - 1, hk_lt⟩).val + 1) = 0 := by omega
      simp only [dif_neg hk']
      ext
      simp only [Nat.add_sub_cancel]
      have heq : (⟨(σ.symm ⟨k.val - 1, hk_lt⟩).val, _⟩ : Fin (n - 1)) = σ.symm ⟨k.val - 1, hk_lt⟩ :=
        Fin.ext rfl
      rw [heq, Equiv.apply_symm_apply]
      exact Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk)

@[simp]
lemma liftTailPerm_zero {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin (n - 1))) :
    liftTailPerm hn σ ⟨0, hn⟩ = ⟨0, hn⟩ := by simp [liftTailPerm]

@[simp]
lemma liftTailPerm_succ {n : ℕ} (hn : 0 < n) (σ : Equiv.Perm (Fin (n - 1))) (i : Fin (n - 1)) :
    liftTailPerm hn σ ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ =
    ⟨(σ i).val + 1, Nat.add_lt_of_lt_sub (σ i).isLt⟩ := by
  simp only [liftTailPerm, Equiv.coe_fn_mk]
  have h : ¬(i.val + 1 = 0) := by omega
  simp only [dif_neg h, Nat.add_sub_cancel]

/-- Combine "0 ↦ j" with "tail ↦ lifted through swap" into a single permutation.

For KS uniqueness: builds the full permutation from the exchange lemma match (0 ↦ j)
and the IH-derived tail permutation. -/
def prependSwapPerm {n m : ℕ} (hn : 0 < n) (_hm : 0 < m) (hn_eq : n = m)
    (j : Fin m) (σ_tail : Equiv.Perm (Fin (n - 1))) : Equiv.Perm (Fin n) :=
  (liftTailPerm hn σ_tail).trans (finSwapFront ⟨j.val, by omega⟩)

@[simp]
lemma prependSwapPerm_zero {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hn_eq : n = m)
    (j : Fin m) (σ_tail : Equiv.Perm (Fin (n - 1))) :
    prependSwapPerm hn hm hn_eq j σ_tail ⟨0, hn⟩ = ⟨j.val, by omega⟩ := by
  simp only [prependSwapPerm, Equiv.trans_apply, liftTailPerm_zero]
  simp only [finSwapFront, Equiv.swap_apply_right]

@[simp]
lemma prependSwapPerm_succ {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hn_eq : n = m)
    (j : Fin m) (σ_tail : Equiv.Perm (Fin (n - 1))) (i : Fin (n - 1)) :
    prependSwapPerm hn hm hn_eq j σ_tail ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ =
    finSwapFront ⟨j.val, by omega⟩ ⟨(σ_tail i).val + 1, Nat.add_lt_of_lt_sub (σ_tail i).isLt⟩ := by
  simp only [prependSwapPerm, Equiv.trans_apply, liftTailPerm_succ]

/-- The equality: f k = (f ∘ (finSwapFront j).symm) ((finSwapFront j) k).
Used for the hom direction of biproductSwapFrontIso. -/
@[simp]
lemma biproductSwapFront_hom_eq {n : ℕ} (f : Fin n → C) (j k : Fin n) :
    f k = (f ∘ (finSwapFront j).symm) ((finSwapFront j) k) := by
  simp only [Function.comp_apply, finSwapFront_symm, finSwapFront_apply_apply]

/-- Biproduct reindexed by swapping j to front.

Direct construction using desc for both directions, avoiding whiskerEquiv
which creates complex proof terms that break rewriting.

Key insight:
- inv doesn't need eqToHom because g k = f (symm k) is definitional
- hom needs eqToHom because g (swap k) = f k is only propositional -/
def biproductSwapFrontIso {n : ℕ} (f : Fin n → C) (j : Fin n) :
    ⨁ f ≅ ⨁ (f ∘ (finSwapFront j).symm) where
  hom := biproduct.desc fun k =>
    eqToHom (biproductSwapFront_hom_eq f j k) ≫
    biproduct.ι (f ∘ (finSwapFront j).symm) ((finSwapFront j) k)
  inv := biproduct.desc fun k => biproduct.ι f ((finSwapFront j).symm k)
  hom_inv_id := by
    ext i k
    simp only [Category.assoc, biproduct.ι_desc_assoc, Category.id_comp]
    simp only [biproduct.ι_π]
    split_ifs with h1 h2 h3
    · -- Both true
      simp only [eqToHom_trans]
    · -- h1 true, h2 false: symm (swap k) = i but k ≠ i
      -- This is impossible since symm (swap k) = k
      exfalso
      simp only [finSwapFront_symm, finSwapFront_apply_apply] at h1
      exact h2 h1
    · -- h1 false, h2 true: symm (swap k) ≠ i but k = i
      -- This is impossible
      exfalso
      simp only [finSwapFront_symm, finSwapFront_apply_apply] at h1
      exact h1 h3
    · -- Both false
      simp only [eqToHom_comp_iff, comp_zero]
  inv_hom_id := by
    ext i k
    simp only [Function.comp_apply, Category.assoc, biproduct.ι_desc_assoc, Category.id_comp]
    simp only [biproduct.ι_π]
    split_ifs with h1 h2 h3
    · simp only [eqToHom_trans]
    · exfalso
      simp only [finSwapFront_symm, finSwapFront_apply_apply] at h1
      exact h2 h1
    · exfalso
      simp only [finSwapFront_symm, finSwapFront_apply_apply] at h1
      exact h1 h3
    · simp only [comp_zero, eqToHom_comp_iff]

/-- After swapping j to front, component 0 is f j. -/
lemma biproductSwapFront_zero {n : ℕ} (f : Fin n → C) (j : Fin n) :
    (f ∘ (finSwapFront j).symm) ⟨0, j.pos⟩ = f j := by
  simp only [Function.comp_apply, finSwapFront_symm, finSwapFront_apply_zero]

/-- Key simp lemma: projecting at index 0 after swapping j to front extracts the j-th component.
This enables computing the (1,1) block in Biprod.isoElim for KS uniqueness. -/
@[simp]
lemma biproductSwapFrontIso_hom_π_zero {n : ℕ} (f : Fin n → C) (j : Fin n) :
    (biproductSwapFrontIso f j).hom ≫ biproduct.π (f ∘ (finSwapFront j).symm) ⟨0, j.pos⟩ =
    biproduct.π f j ≫ eqToHom (biproductSwapFront_zero f j).symm := by
  -- Use biproduct extensionality: show ι k ≫ LHS = ι k ≫ RHS for all k
  apply biproduct.hom_ext'; intro k
  -- Expand hom definition and use ι_desc, ι_π
  simp only [Category.assoc, biproductSwapFrontIso, biproduct.ι_desc_assoc, biproduct.ι_π,
             biproduct.ι_π_assoc]
  -- Now split on whether k = j (and correspondingly swap k = 0)
  split_ifs with h1 h2 h3
  · -- h1: swap k = 0, h2: k = j
    -- Both sides give eqToHom chains
    simp only [eqToHom_trans]
  · -- h1: swap k = 0, but k ≠ j
    -- swap k = 0 implies k = j, contradiction
    exfalso
    apply h2
    have : finSwapFront j k = ⟨0, j.pos⟩ := h1
    rw [← finSwapFront_apply_self j] at this
    exact (Equiv.injective (finSwapFront j)) this
  · -- h1: swap k ≠ 0, but k = j
    -- k = j implies swap k = 0, contradiction
    exfalso
    apply h1
    rw [h3, finSwapFront_apply_self]
  · -- Both conditions false: swap k ≠ 0 and k ≠ j
    simp only [eqToHom_comp_iff, comp_zero, zero_comp]

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
