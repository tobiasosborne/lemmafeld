/-
  LemmaFeld/CategoryTheory/TensorCategories/Chapter1/LocallyFinite.lean

  §1.8: Locally Finite (Artinian) and Finite Abelian Categories (Etingof et al.)

  This file formalizes §1.8 of the tensor categories book, which defines
  locally finite and finite abelian categories.

  **Book Reference:** Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015)

  **Key Definitions:**
  - Definition 1.8.1: Locally finite k-linear abelian category
  - Remark 1.8.2: Locally finite = artinian categories
  - Definition 1.8.3: Injective and surjective functors
  - Proposition 1.8.4: Schur's lemma for locally finite categories
  - Definition 1.8.5/1.8.6: Finite abelian categories

  **Mathlib Status:**
  - Finite length objects: `IsArtinianObject`, `IsNoetherianObject` (via subobjects)
  - Finite dim Hom: `Module.Finite k (X ⟶ Y)` as hypothesis
  - Schur's lemma: `isIso_of_hom_simple` in `CategoryTheory.Simple`
  - Enough projectives: `EnoughProjectives C` in `CategoryTheory.Projective`
  - FGModuleCat has `instFiniteHom` for finite dim modules
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Noetherian
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.RingTheory.Finiteness.Defs
import Mathlib.FieldTheory.IsAlgClosed.Basic

import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.FiniteLength

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

universe w v u

/-! ## §1.8 Definition 1.8.1: Locally Finite Abelian Category

Book: "A k-linear abelian category C is said to be locally finite if the following
two conditions are satisfied:
(i) for any two objects X, Y in C the k-vector space Hom_C(X, Y) is finite dimensional;
(ii) every object in C has finite length."

The Jordan-Hölder and Krull-Schmidt theorems hold in any locally finite abelian category.
-/

section LocallyFinite

variable (k : Type w) [Field k]
variable (C : Type u) [Category.{v} C]

/-- A k-linear abelian category is locally finite if:
(i) Hom spaces are finite dimensional k-vector spaces
(ii) Every object has finite length (is both Artinian and Noetherian)

Book Definition 1.8.1.

**Note:** The finite dimensional Hom condition is stated as a Prop rather than
a Module.Finite instance to allow flexibility in how it's verified. -/
class IsLocallyFinite [Abelian C] [Preadditive C] [Linear k C] : Prop where
  /-- Condition (i): Hom spaces are finite dimensional -/
  finiteDim_hom : ∀ (X Y : C), Module.Finite k (X ⟶ Y)
  /-- Condition (ii): Every object has finite length -/
  finiteLength : ∀ (X : C), IsFiniteLengthObject X

/-- Remark 1.8.2: Locally finite abelian categories are also called artinian categories.
This is because condition (ii) implies every object is Artinian (DCC on subobjects). -/
abbrev IsArtinianCategory [Abelian C] [Preadditive C] [Linear k C] := IsLocallyFinite k C

end LocallyFinite

/-! ## §1.8 Definition 1.8.3: Injective and Surjective Functors

Book: "An additive functor F : C → D between two locally finite abelian categories is
injective if it is fully faithful (i.e., bijective on the sets of morphisms).
We say that F is surjective if any simple object of D is a subquotient of some
object F(X), where X is an object of C."

Note: This definition of surjective differs from essential surjectivity.
-/

section FunctorProperties

variable {C D : Type*} [Category C] [Category D]

/-- A functor is injective if it is fully faithful.
Book Definition 1.8.3(i).

Mathlib: `F.FullyFaithful` is a structure witnessing full + faithful.
We use `Nonempty` to get a Prop. -/
def Functor.IsInjective (F : C ⥤ D) : Prop := Nonempty F.FullyFaithful

/-- A functor is surjective if every simple object in the target is a subquotient
of some object in the image.

Book Definition 1.8.3(ii): "F is surjective if any simple object of D is a subquotient
of some object F(X), where X is an object of C."

**Simplified formulation:** Every simple in D is isomorphic to a simple subobject
of some F(X). A full formalization would require the subquotient notion.

**Note:** This is weaker than essential surjectivity. -/
def Functor.IsSurjective [HasZeroMorphisms D] (F : C ⥤ D) : Prop :=
  ∀ (Y : D), Simple Y → ∃ (X : C), ∃ (S : Subobject (F.obj X)),
    Simple (S : D) ∧ Nonempty ((S : D) ≅ Y)

end FunctorProperties

/-! ## §1.8 Proposition 1.8.4: Schur's Lemma for Locally Finite Categories

Book: "Suppose that k is algebraically closed. In any locally finite category C over k
we have Hom_C(X, Y) = 0 if X, Y are simple and non-isomorphic and
Hom_C(X, X) = k for any simple object X."

This follows from:
1. Schur's lemma: any morphism between simples is either 0 or iso
2. Hom(X, X) is a division algebra over k
3. Finite dimensional division algebras over algebraically closed fields are trivial
-/

section SchurLemma

variable {k : Type*} [Field k]
variable {C : Type*} [Category C] [Abelian C] [Preadditive C] [Linear k C]

/-- For non-isomorphic simple objects, Hom(X, Y) = 0.
Book Proposition 1.8.4 (first part).

Mathlib: This follows from `isIso_of_hom_simple` — any nonzero morphism
between simples is an iso, so if X ≇ Y then Hom(X, Y) = 0. -/
theorem hom_simple_eq_zero_of_not_iso {X Y : C} [Simple X] [Simple Y]
    (hne : ¬Nonempty (X ≅ Y)) : ∀ f : X ⟶ Y, f = 0 := by
  intro f
  by_contra hf
  -- If f ≠ 0, then f is an iso by Schur's lemma
  haveI : IsIso f := isIso_of_hom_simple hf
  exact hne ⟨asIso f⟩

/-- For a simple object X over an algebraically closed field k,
Hom(X, X) is a 1-dimensional k-vector space (hence isomorphic to k).

Book Proposition 1.8.4 (second part): "Hom_C(X, X) = k for any simple object X."

**Proof sketch:**
1. End(X) is a division algebra (Schur's lemma)
2. End(X) is finite dimensional over k (locally finite condition)
3. Finite dimensional division algebras over algebraically closed k are trivial

**Mathlib status:** The statement requires `IsAlgClosed k` and the fact that
finite dimensional division algebras over algebraically closed fields equal k.
-/
theorem end_simple_eq_one_dim [IsAlgClosed k] (X : C)
    [Simple X] [hfd : Module.Finite k (X ⟶ X)] :
    Module.finrank k (X ⟶ X) = 1 := by
  sorry  -- Requires division algebra classification

end SchurLemma

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

/-! ## Summary of §1.8

| Book | Lean | Notes |
|------|------|-------|
| Def 1.8.1 | `IsLocallyFinite k C` | Finite dim Hom + finite length |
| Remark 1.8.2 | `IsArtinianCategory` | Alias for IsLocallyFinite |
| Def 1.8.3 | `Functor.IsInjective/IsSurjective` | Fully faithful, subquotient |
| Prop 1.8.4 | `hom_simple_eq_zero_of_not_iso` | Schur's lemma consequences |
| Def 1.8.5/6 | `IsFiniteAbelian k C` | LocallyFinite + EnoughProj + fin simples |
| O(C) | `SimpleClasses C` | Iso classes of simples |

**Gaps:**
- `end_simple_eq_one_dim`: Requires fin dim division algebra = k (alg closed)
- `IsSurjective`: Needs proper subquotient formalization
- Duality: Finite category duality is not formalized
-/

end LemmaFeld.TensorCategories.Chapter1
