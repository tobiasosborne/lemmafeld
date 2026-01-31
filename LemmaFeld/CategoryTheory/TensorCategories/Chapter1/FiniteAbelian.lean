/-
  LemmaFeld/CategoryTheory/TensorCategories/Chapter1/FiniteAbelian.lean

  §1.8.5-1.8.7: Finite Abelian Categories (Etingof et al.)

  This file formalizes the second half of §1.8, covering finite abelian categories.

  **Book Reference:** Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015)

  **Key Definitions:**
  - Definition 1.8.5/1.8.6: Finite abelian categories
  - Remark 1.8.7: Duality for finite categories

  **Dependencies:** LocallyFinite.lean for IsLocallyFinite class
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.LocallyFinite

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

universe w v u

/-! ## §1.8 Definition 1.8.5 & 1.8.6: Finite Abelian Categories

Book Definition 1.8.5: "A k-linear abelian category C is said to be finite if it is
equivalent to the category A-mod of finite dimensional modules over a finite
dimensional k-algebra A."

Book Definition 1.8.6 (equivalent intrinsic definition): C is finite if
(i) C has finite dimensional spaces of morphisms
(ii) every object of C has finite length
(iii) C has enough projectives
(iv) there are finitely many isomorphism classes of simple objects

Note: Conditions (i)-(ii) are exactly the locally finite condition.
-/

section FiniteCategory

variable (k : Type w) [Field k]
variable (C : Type u) [Category.{v} C] [Abelian C] [Preadditive C] [Linear k C]

/-- The setoid on simple objects given by isomorphism.
Two simple objects are related iff they are isomorphic. -/
def simpleIsoSetoid : Setoid {S : C // Simple S} where
  r := fun X Y => Nonempty (X.val ≅ Y.val)
  iseqv := ⟨fun _ => ⟨Iso.refl _⟩, fun ⟨i⟩ => ⟨i.symm⟩, fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩⟩

/-- The set of isomorphism classes of simple objects in C.
Book notation: O(C) denotes this set for locally finite categories. -/
def SimpleClasses : Type u := Quotient (simpleIsoSetoid C)

/-- A k-linear abelian category is finite if:
(i) Hom spaces are finite dimensional
(ii) every object has finite length
(iii) C has enough projectives
(iv) there are finitely many simple isomorphism classes

Book Definition 1.8.6. Equivalent to being equivalent to A-mod for
finite dimensional algebra A (Definition 1.8.5). -/
class IsFiniteAbelian [EnoughProjectives C] : Prop where
  /-- Conditions (i)-(ii): locally finite -/
  locallyFinite : IsLocallyFinite k C
  /-- Condition (iv): finitely many simples -/
  finiteSimples : Finite (SimpleClasses C)

-- Note: Condition (iii) is captured by [EnoughProjectives C]

/-- A finite abelian category is locally finite.
This is "Note" after Definition 1.8.6: "the first two conditions of Definition 1.8.6
are the requirement that C be locally finite." -/
instance [EnoughProjectives C] [IsFiniteAbelian k C] : IsLocallyFinite k C :=
  IsFiniteAbelian.locallyFinite

end FiniteCategory

/-! ## §1.8 Remark 1.8.7: Duality for Finite Categories

Book: "The dual category of a finite abelian category is finite. Namely, the dual
to the category of finite dimensional A-modules is the category of finite dimensional
A^op-modules, where A^op is the algebra A with opposite multiplication, and the
duality functor between these categories is the functor of taking the dual module."

Thus, in a finite abelian category, any object has both a projective cover and
an injective hull.

**Mathlib:** `EnoughProjectives` and `EnoughInjectives` are independent classes.
The duality statement would require showing that if C ≃ A-mod then Cᵒᵖ ≃ A^op-mod.
-/

/-! ## Summary of §1.8.5-1.8.7

| Book | Lean | Notes |
|------|------|-------|
| Def 1.8.5/6 | `IsFiniteAbelian k C` | LocallyFinite + EnoughProj + fin simples |
| O(C) | `SimpleClasses C` | Iso classes of simples |

**Gaps:**
- Duality: Finite category duality is not formalized
-/

end LemmaFeld.TensorCategories.Chapter1
