/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.NatTrans
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Linear.FunctorCategory
import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Abelian.FunctorCategory
import Mathlib.CategoryTheory.Endomorphism
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Chapter 1, §1.8.15: Endomorphism Algebras of Tensor Product Functors

This file formalizes Proposition 1.8.15 from Etingof et al. "Tensor Categories".

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.8

## Main Result

**Proposition 1.8.15:** Let F₁, F₂ : C → Vec be two exact faithful functors.
Define F₁ ⊗ F₂ : C × C → Vec by (X, Y) ↦ F₁(X) ⊗ F₂(Y).
Then there is a canonical algebra isomorphism

  α_{F₁,F₂} : End(F₁) ⊗ End(F₂) ≅ End(F₁ ⊗ F₂)

given by α_{F₁,F₂}(η₁ ⊗ η₂)|_{F₁(X) ⊗ F₂(Y)} := η₁|_{F₁(X)} ⊗ η₂|_{F₂(Y)}.

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| End(F) | `CategoryTheory.End F` | Endomorphism ring of functor |
| F₁ ⊗ F₂ | `tensorProductFunctor` | Composition with monoidal tensor |
| Vec | `ModuleCat k` | Category of k-vector spaces |
| Algebra isomorphism | `AlgEquiv` | `Mathlib.Algebra.Algebra.Equiv` |

-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

/-! ## §1.8.15: Setup and Definitions -/

section FunctorTensorProduct

variable (k : Type) [CommRing k]
variable (C : Type u) [Category.{u} C]

/-- The tensor product of two functors F₁, F₂ : C ⥤ ModuleCat k.

Book: "Define a functor F₁ ⊗ F₂ : C × C → Vec given by (X, Y) ↦ F₁(X) ⊗ F₂(Y)."

This is constructed by first applying F₁ and F₂ in parallel to get a functor
into ModuleCat k × ModuleCat k, then composing with the monoidal tensor functor. -/
def tensorProductFunctor (F₁ F₂ : C ⥤ ModuleCat.{0} k) : C × C ⥤ ModuleCat.{0} k :=
  (F₁.prod F₂) ⋙ (MonoidalCategory.tensor (ModuleCat.{0} k))

/-- Notation for tensor product of functors. -/
scoped infixl:70 " ⊗ᶠ " => tensorProductFunctor _

/-! ### Action on objects and morphisms -/

/-- The tensor product functor sends (X, Y) to F₁(X) ⊗ F₂(Y). -/
@[simp]
lemma tensorProductFunctor_obj (F₁ F₂ : C ⥤ ModuleCat.{0} k) (p : C × C) :
    (tensorProductFunctor k C F₁ F₂).obj p = F₁.obj p.1 ⊗ F₂.obj p.2 := rfl

/-- The tensor product functor sends (f, g) to F₁(f) ⊗ₘ F₂(g). -/
@[simp]
lemma tensorProductFunctor_map (F₁ F₂ : C ⥤ ModuleCat.{0} k) {p q : C × C}
    (f : p ⟶ q) :
    (tensorProductFunctor k C F₁ F₂).map f = F₁.map f.1 ⊗ₘ F₂.map f.2 := rfl

end FunctorTensorProduct

/-! ## §1.8.15: The Canonical Map -/

section EndomorphismAlgebra

variable (k : Type) [CommRing k]
variable (C : Type u) [Category.{u} C] [Preadditive C] [Linear k C]

/-- For a functor F : C ⥤ ModuleCat k, End(F) is a k-algebra.

This is the endomorphism algebra of F in the functor category. -/
instance endAlgebra (F : C ⥤ ModuleCat.{0} k) : Algebra k (End F) :=
  inferInstance

/-- For endomorphisms η₁ : End(F₁) and η₂ : End(F₂), we can form their tensor product
as an endomorphism of F₁ ⊗ᶠ F₂.

Book: "α_{F₁,F₂}(η₁ ⊗ η₂)|_{F₁(X) ⊗ F₂(Y)} := η₁|_{F₁(X)} ⊗ η₂|_{F₂(Y)}"

This maps (η₁, η₂) to the natural transformation whose component at (X, Y) is
η₁_X ⊗ η₂_Y : F₁(X) ⊗ F₂(Y) → F₁(X) ⊗ F₂(Y). -/
def endPairToTensorEnd (F₁ F₂ : C ⥤ ModuleCat.{0} k) (η₁ : End F₁) (η₂ : End F₂) :
    End (tensorProductFunctor k C F₁ F₂) where
  app p := η₁.app p.1 ⊗ₘ η₂.app p.2
  naturality p q f := by
    simp only [tensorProductFunctor_map]
    -- Goal: (F₁.map f.1 ⊗ₘ F₂.map f.2) ≫ (η₁.app q.1 ⊗ₘ η₂.app q.2) =
    --       (η₁.app p.1 ⊗ₘ η₂.app p.2) ≫ (F₁.map f.1 ⊗ₘ F₂.map f.2)
    rw [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom]
    -- Now: (F₁.map f.1 ≫ η₁.app q.1) ⊗ₘ (F₂.map f.2 ≫ η₂.app q.2) =
    --      (η₁.app p.1 ≫ F₁.map f.1) ⊗ₘ (η₂.app p.2 ≫ F₂.map f.2)
    rw [η₁.naturality f.1, η₂.naturality f.2]

/-! ### Proposition 1.8.15: Properties of the Map

**Book Proposition 1.8.15:** There is a canonical algebra isomorphism
End(F₁) ⊗ End(F₂) ≅ End(F₁ ⊗ F₂).

The map α_{F₁,F₂} sends η₁ ⊗ η₂ to the natural transformation with components
η₁_X ⊗ η₂_Y at each (X, Y).
-/

omit [Preadditive C] [Linear k C] in
/-- The map respects the identity: 1 ⊗ 1 ↦ 1. -/
lemma endTensor_one (F₁ F₂ : C ⥤ ModuleCat.{0} k) :
    endPairToTensorEnd k C F₁ F₂ (NatTrans.id F₁) (NatTrans.id F₂) =
      NatTrans.id (tensorProductFunctor k C F₁ F₂) := by
  apply NatTrans.ext
  funext p
  simp only [endPairToTensorEnd, tensorProductFunctor_obj]
  change 𝟙 (F₁.obj p.1) ⊗ₘ 𝟙 (F₂.obj p.2) = 𝟙 (F₁.obj p.1 ⊗ F₂.obj p.2)
  rw [tensorHom_def, id_whiskerRight, whiskerLeft_id, Category.comp_id]

omit [Preadditive C] [Linear k C] in
/-- The map respects composition: (η₁ ∘ η₁') ⊗ (η₂ ∘ η₂') ↦ (η₁ ⊗ η₂) ∘ (η₁' ⊗ η₂'). -/
lemma endTensor_comp (F₁ F₂ : C ⥤ ModuleCat.{0} k)
    (η₁ η₁' : End F₁) (η₂ η₂' : End F₂) :
    endPairToTensorEnd k C F₁ F₂ (η₁ ≫ η₁') (η₂ ≫ η₂') =
      endPairToTensorEnd k C F₁ F₂ η₁ η₂ ≫ endPairToTensorEnd k C F₁ F₂ η₁' η₂' := by
  apply NatTrans.ext
  funext p
  simp only [endPairToTensorEnd, tensorProductFunctor_obj, NatTrans.comp_app]
  exact (tensorHom_comp_tensorHom _ _ _ _).symm

/-- **Proposition 1.8.15** (statement): For exact faithful functors F₁, F₂ : C → Vec,
there is a canonical algebra isomorphism End(F₁) ⊗ End(F₂) ≅ End(F₁ ⊗ F₂).

The map is given by the universal property of tensor products applied to
`endPairToTensorEnd`.

**Proof status:** The definition of the map and its algebraic properties (respects
identity and composition) are proved above. The full isomorphism requires:
1. Constructing the linear map via TensorProduct.lift
2. Proving bijectivity using exactness and faithfulness

This is left as Exercise 1.8.16 (tracked in issue lemmafeld-cgdr). -/
theorem prop_1_8_15 (F₁ F₂ : C ⥤ ModuleCat.{0} k)
    (hF₁ : F₁.Faithful) (hF₂ : F₂.Faithful) :
    Function.Bijective (fun (pair : End F₁ × End F₂) =>
      endPairToTensorEnd k C F₁ F₂ pair.1 pair.2) :=
  sorry  -- Full proof requires deeper analysis of exact faithful functors

end EndomorphismAlgebra

/-! ## §1.8.16: Exercise

Exercise 1.8.16 asks to prove Proposition 1.8.15.

The full proof that `endTensorEquiv` is an isomorphism requires:
1. Exactness and faithfulness of F₁, F₂ to ensure representability
2. The fact that for exact faithful functors on finite abelian categories,
   the functor is determined by its action on a projective generator
3. The tensor product structure and how it interacts with representability

This exercise is tracked in issue lemmafeld-cgdr.
-/

end LemmaFeld.TensorCategories.Chapter1
