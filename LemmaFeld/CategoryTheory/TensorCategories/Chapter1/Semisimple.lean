/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.HomOrthogonal
import Mathlib.CategoryTheory.Preadditive.Schur

/-!
# Chapter 1, Section 1.5: Semisimple Objects and Categories

This file formalizes semisimple objects and categories from Etingof et al.
"Tensor Categories" §1.5, Definition 1.5.1.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.5

## §1.5 Definition 1.5.1 (Semisimple)

Book: "An object X in C is called semisimple if it is a direct sum of simple objects,
and C is called semisimple if every object of C is semisimple."

## Mathlib Status

As of mathlib4 (2025), there is no categorical `Semisimple` class for general
abelian categories. Mathlib has:
- `IsSemisimpleModule R M` in `Mathlib.RingTheory.SimpleModule.Basic` (for modules)
- `HomOrthogonal` in `Mathlib.CategoryTheory.Preadditive.HomOrthogonal` (preliminary)

This file provides the categorical definitions needed for the tensor categories project.

## Main Definitions

* `IsSemisimple X` - object X is isomorphic to a finite biproduct of simple objects
* `SemisimpleCategory C` - every object is semisimple

-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

/-! ## §1.5 Definition 1.5.1: Semisimple Objects -/

section SemisimpleObjects

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasFiniteBiproducts C]

/-- An object X is semisimple if it is isomorphic to a finite biproduct of simple objects.

Book: "An object X in C is called semisimple if it is a direct sum of simple objects" -/
def IsSemisimple (X : C) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (S : ι → C), (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S)

/-- Simple objects are semisimple (direct sum of one object). -/
theorem Simple.isSemisimple {X : C} [Simple X] : IsSemisimple X := by
  refine ⟨Unit, inferInstance, fun _ => X, fun _ => inferInstance, ⟨?_⟩⟩
  exact (biproductUniqueIso (fun _ : Unit => X)).symm

/-- Semisimplicity is preserved under isomorphism. -/
theorem IsSemisimple.of_iso {X Y : C} (h : X ≅ Y) (hX : IsSemisimple X) : IsSemisimple Y := by
  obtain ⟨ι, _, S, hS, ⟨iso⟩⟩ := hX
  exact ⟨ι, inferInstance, S, hS, ⟨h.symm.trans iso⟩⟩

end SemisimpleObjects

/-! ## §1.5 Definition 1.5.1: Semisimple Categories -/

section SemisimpleCategory

/-- A category is semisimple if every object is semisimple.

Book: "C is called semisimple if every object of C is semisimple." -/
class SemisimpleCategory (C : Type*) [Category C] [HasZeroMorphisms C]
    [HasFiniteBiproducts C] : Prop where
  /-- Every object is semisimple -/
  isSemisimple : ∀ X : C, IsSemisimple X

variable {C : Type*} [Category C] [HasZeroMorphisms C] [HasFiniteBiproducts C]

/-- In a semisimple category, every object is semisimple. -/
theorem isSemisimple_of_semisimpleCategory [SemisimpleCategory C] (X : C) : IsSemisimple X :=
  SemisimpleCategory.isSemisimple X

end SemisimpleCategory

/-! ## Connection to HomOrthogonal

Mathlib's `HomOrthogonal` provides the key uniqueness theorem for decompositions:
if a family `s : ι → C` of objects satisfies `HomOrthogonal s` (the only morphism
between distinct objects is zero), then decompositions as biproducts over `s`
have uniquely defined multiplicities.

For simple objects, `HomOrthogonal` holds by Schur's lemma: if X, Y are simple
and non-isomorphic, then Hom(X, Y) = 0.
-/

section HomOrthogonalConnection

variable {C : Type*} [Category C] [Preadditive C] [HasKernels C] [HasFiniteBiproducts C]

/-- Simple objects form a hom orthogonal family (up to isomorphism classes).

This follows from Schur's lemma: if X ≇ Y are simple, then Hom(X, Y) = 0. -/
theorem homOrthogonal_of_simple {ι : Type*} (S : ι → C) (hS : ∀ i, Simple (S i))
    (hne : ∀ i j, i ≠ j → ¬Nonempty (S i ≅ S j)) : HomOrthogonal S := by
  intro i j hij
  constructor
  intro f g
  -- Both f and g must be zero by Schur's lemma since S i ≇ S j
  have hf : f = 0 := by
    by_contra hf'
    haveI := hS i
    haveI := hS j
    have hiso : IsIso f := isIso_of_hom_simple hf'
    exact hne i j hij ⟨asIso f⟩
  have hg : g = 0 := by
    by_contra hg'
    haveI := hS i
    haveI := hS j
    have hiso : IsIso g := isIso_of_hom_simple hg'
    exact hne i j hij ⟨asIso g⟩
  rw [hf, hg]

end HomOrthogonalConnection

/-! ## Remarks on Further Development

**Zero object:** The zero object is semisimple (as the empty biproduct), but
proving this requires showing `(0 : C) ≅ ⨁ (PEmpty.elim : PEmpty → C)`.

**Biproduct closure:** The biproduct of semisimple objects is semisimple.
This requires API for relating `X ⊞ Y` to `⨁ (Sum.elim SX SY)`.

**Jordan-Hölder and Krull-Schmidt:** The book's treatment continues with
finite length objects (§1.5.3), Jordan-Hölder (§1.5.4), and Krull-Schmidt (§1.5.7).
These are not yet in mathlib for general abelian categories.

**Module semisimplicity:** For `ModuleCat R`, `IsSemisimple` here should be
equivalent to `IsSemisimpleModule R M`. This requires showing categorical
biproducts in `ModuleCat` correspond to direct sums.

**Maschke's theorem:** A key source of semisimple categories is representation
theory: `Rep k G` for finite group G with |G| invertible in k is semisimple.
-/

end LemmaFeld.TensorCategories.Chapter1
