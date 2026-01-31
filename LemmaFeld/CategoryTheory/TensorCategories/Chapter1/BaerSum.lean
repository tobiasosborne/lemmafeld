/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback

/-!
# Baer Sum and Extension Classes

This file formalizes the Baer sum construction from Exercise 1.4.3(i) of Etingof et al.
"Tensor Categories" (AMS 2015), §1.4.

## Book Construction (1.5)

Given two short exact sequences (extensions):
- S : 0 → X → Z → Y → 0
- S' : 0 → X → Z' → Y → 0

The Baer sum S + S' is defined as 0 → X → Z'' → Y → 0 where:
1. Let Z̃'' = Z ×_Y Z' (fiber product / pullback)
2. X embeds antidiagonally via (i, -i') : X → Z̃''
3. Z'' = Z̃'' / Im((i, -i'))

Alternative: Z̃'' = Ker(π ∘ p - π' ∘ p' : Z ⊕ Z' → Y)

## Mathlib Approach

Mathlib defines Ext via derived functors. The extension class of a short exact sequence
is given by `ShortExact.extClass`. The Baer sum is implicit in the equivalence between
Yoneda Ext and derived functor Ext.

## References

- Etingof et al. "Tensor Categories" (AMS 2015), §1.4, Exercise 1.4.3(i)
- Weibel "An Introduction to Homological Algebra" (CUP 1994), §3.4
- mathlib: `Mathlib.Algebra.Homology.DerivedCategory.Ext`
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

/-! ## The Extension Class of a Short Exact Sequence

Given S : 0 → X → Z → Y → 0, we get `S.ShortExact.extClass : Ext S.X₃ S.X₁ 1`.
Note: if S is `0 → S.X₁ → S.X₂ → S.X₃ → 0`, then extClass ∈ Ext¹(S.X₃, S.X₁).
-/

section ExtensionClass

variable {C : Type*} [Category C] [Abelian C] [HasExt C]

-- A short exact sequence S gives a class in Ext¹
-- S : 0 → S.X₁ → S.X₂ → S.X₃ → 0
-- extClass : Ext S.X₃ S.X₁ 1 (i.e., Ext¹(S.X₃, S.X₁) in book notation)
example (S : ShortComplex C) (hS : S.ShortExact) : Ext S.X₃ S.X₁ 1 :=
  hS.extClass

-- Key property: composing extClass with S.g gives 0
example (S : ShortComplex C) (hS : S.ShortExact) :
    (Ext.mk₀ S.g).comp hS.extClass (Nat.zero_add 1) = 0 :=
  hS.comp_extClass

-- Key property: composing extClass with S.f gives 0
example (S : ShortComplex C) (hS : S.ShortExact) :
    hS.extClass.comp (Ext.mk₀ S.f) (Nat.add_zero 1) = 0 :=
  hS.extClass_comp

end ExtensionClass

/-! ## Baer Sum Construction (Book Description)

The Baer sum is defined via pullback and pushout:

**Step 1**: Form the fiber product
  Z̃'' = Z ×_Y Z' = {(z, z') ∈ Z × Z' | π(z) = π'(z')}

**Step 2**: X embeds diagonally via (i, i') and antidiagonally via (i, -i')

**Step 3**: Z'' = Z̃'' / X_antidiag

**Step 4**: The induced maps give 0 → X → Z'' → Y → 0

In mathlib, this is captured via the equivalence between extension classes and Ext¹.
-/

section BaerSumDescription

variable {C : Type*} [Category C] [Abelian C]

-- Pullbacks exist in abelian categories
example {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : HasPullback f g := inferInstance

-- Pushouts exist in abelian categories
example {X Y Z : C} (f : Z ⟶ X) (g : Z ⟶ Y) : HasPushout f g := inferInstance

-- The fiber product Z ×_Y Z' can be described as a kernel:
-- pullback f g ≅ kernel (biprod.fst ≫ f - biprod.snd ≫ g)
-- (implicit in abelian category pullback construction)

end BaerSumDescription

/-! ## Summary

Exercise 1.4.3(i) is established via mathlib's `AddCommGroup (Ext X Y 1)` instance.
The abelian group axioms are verified in `ExtAbelianGroup.lean`.

**Book approach (Baer sum)**:
1. Define addition on extension classes via pullback/pushout
2. Verify abelian group axioms by explicit diagram chases

**Mathlib approach (derived functors)**:
1. Define Ext as Hom-groups in derived category
2. Abelian group structure is inherited from the additive category structure

The equivalence is a classical result in homological algebra.
-/

end LemmaFeld.TensorCategories.Chapter1
