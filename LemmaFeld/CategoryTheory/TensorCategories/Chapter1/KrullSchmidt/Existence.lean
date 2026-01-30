/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.Defs
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.Auxiliary
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.SubobjectBiprod
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.KrullSchmidt.BiproductHelpers

/-!
# Krull-Schmidt: Existence Proof

This file proves the existence part of the Krull-Schmidt theorem:
every finite length object admits an indecomposable decomposition.

The proof uses well-founded induction on the subobject lattice.
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]

/-- Empty decomposition for the zero object. -/
def emptyDecomposition (X : C) (hX : IsZero X) : IndecomposableDecomposition C X where
  n := 0
  components := Fin.elim0
  indecomposable := fun i => i.elim0
  iso := hX.isoZero ≪≫ biproduct_empty_isZero.isoZero.symm

/-- Singleton decomposition for an indecomposable object. -/
def singletonDecomposition (X : C) (hX : Indecomposable X) : IndecomposableDecomposition C X where
  n := 1
  components := fun _ => X
  indecomposable := fun _ => hX
  iso := (biproductSingletonIso X).symm

/-- **Krull-Schmidt Existence**: Every finite length object admits an indecomposable decomposition.

The proof proceeds by well-founded induction on the subobject lattice. For a finite length object X:
- If X is zero, use the empty decomposition
- If X is indecomposable, use the singleton decomposition
- If X ≅ Y ⊞ Z with both nonzero, recursively decompose Y and Z
-/
theorem krullSchmidt_existence (X : C) (hX : IsFiniteLengthObject X) :
    Nonempty (IndecomposableDecomposition C X) := by
  haveI : IsArtinianObject X := hX.artinian
  suffices h : ∀ S : Subobject X,
      Nonempty (IndecomposableDecomposition C (Subobject.underlying.obj S)) by
    obtain ⟨d⟩ := h ⊤
    haveI : IsIso (⊤ : Subobject X).arrow := by rw [Subobject.isIso_arrow_iff_eq_top]
    let topIso : Subobject.underlying.obj (⊤ : Subobject X) ≅ X := asIso (⊤ : Subobject X).arrow
    exact ⟨{ n := d.n
             components := d.components
             indecomposable := d.indecomposable
             iso := topIso.symm ≪≫ d.iso }⟩
  intro S
  induction S using WellFoundedLT.induction with
  | ind S ih =>
    set U := Subobject.underlying.obj S with hU
    have hUfl : IsFiniteLengthObject U := isFiniteLengthObject_subobject hX S
    by_cases hZero : IsZero U
    · exact ⟨emptyDecomposition U hZero⟩
    · by_cases hIndec : Indecomposable U
      · exact ⟨singletonDecomposition U hIndec⟩
      · simp only [Indecomposable, not_and, not_forall, not_or] at hIndec
        obtain ⟨Y, Z, iU, hY, hZ⟩ := hIndec hZero
        let sY := subobjectOfBiprodFst_via S iU
        let sZ := subobjectOfBiprodSnd_via S iU
        have sY_lt : sY < S := subobjectOfBiprodFst_via_lt S iU hZ
        have sZ_lt : sZ < S := subobjectOfBiprodSnd_via_lt S iU hY
        obtain ⟨dY'⟩ := ih sY sY_lt
        obtain ⟨dZ'⟩ := ih sZ sZ_lt
        let iY : Subobject.underlying.obj sY ≅ Y := subobjectOfBiprodFst_via_underlyingIso S iU
        let iZ : Subobject.underlying.obj sZ ≅ Z := subobjectOfBiprodSnd_via_underlyingIso S iU
        let dY : IndecomposableDecomposition C Y :=
          { n := dY'.n
            components := dY'.components
            indecomposable := dY'.indecomposable
            iso := iY.symm ≪≫ dY'.iso }
        let dZ : IndecomposableDecomposition C Z :=
          { n := dZ'.n
            components := dZ'.components
            indecomposable := dZ'.indecomposable
            iso := iZ.symm ≪≫ dZ'.iso }
        refine ⟨⟨dY.n + dZ.n, fun k =>
          if h : k.val < dY.n then dY.components ⟨k.val, h⟩
          else dZ.components ⟨k.val - dY.n, by omega⟩, ?_, ?_⟩⟩
        · intro k
          simp only
          split_ifs with h
          · exact dY.indecomposable ⟨k.val, h⟩
          · exact dZ.indecomposable ⟨k.val - dY.n, by omega⟩
        · exact iU ≪≫ biprodMapIso dY.iso dZ.iso ≪≫ biproductBiprodIso dY.components dZ.components

end LemmaFeld.TensorCategories.Chapter1
