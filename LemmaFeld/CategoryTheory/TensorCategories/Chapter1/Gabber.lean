/-
  LemmaFeld/CategoryTheory/TensorCategories/Chapter1/Gabber.lean

  §1.8.17: Gabber's Theorem (Etingof et al.)

  **Book Reference:** Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015)

  **Proposition 1.8.17 (Gabber):** Let C be a locally finite abelian category.
  Suppose that there exists X ∈ C such that any object of C is a subquotient of
  a direct sum of finitely many copies of X. Then C has a projective generator,
  i.e., is a finite abelian category.

  **Original source:** Deligne, "Catégories tannakiennes", Proposition 2.14 [De1]

  This file defines:
  - Subquotient: Y is a subquotient of X
  - HasSubquotientGenerator: ∃ X such that every object is a subquotient of X^n
  - IsProjectiveGenerator: P is projective and a separator
  - Proposition 1.8.17: The main theorem
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.CategoryTheory.Generator.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.LocallyFinite
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.FiniteAbelian

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

universe w v u

/-! ## Subquotients

Book Definition (implicit in §1.8.3 and §1.8.17): An object Y is a subquotient of X
if there exists an object Z with a monomorphism Z ↪ X and an epimorphism Z ↠ Y.

Equivalently, Y is a quotient of a subobject of X.
-/

section Subquotient

variable {C : Type u} [Category.{v} C]

/-- Y is a subquotient of X if there exists Z with Z ↪ X (mono) and Z ↠ Y (epi).
This captures the notion "Y is a quotient of a subobject of X".

Book: Used implicitly in Definition 1.8.3 (surjective functors) and
Proposition 1.8.17 (Gabber's theorem). -/
def IsSubquotient (Y X : C) : Prop :=
  ∃ (Z : C) (i : Z ⟶ X) (p : Z ⟶ Y), Mono i ∧ Epi p

/-- Every object is a subquotient of itself. -/
theorem isSubquotient_refl (X : C) : IsSubquotient X X :=
  ⟨X, 𝟙 X, 𝟙 X, inferInstance, inferInstance⟩

/-- Subquotients of subquotients are subquotients (transitivity). -/
theorem isSubquotient_trans [Abelian C] {X Y Z : C}
    (hYX : IsSubquotient Y X) (hZY : IsSubquotient Z Y) : IsSubquotient Z X := by
  obtain ⟨W₁, i₁, p₁, hi₁, hp₁⟩ := hYX
  obtain ⟨W₂, i₂, p₂, hi₂, hp₂⟩ := hZY
  -- Use pullback to construct the composite subquotient
  -- W₂ --i₂--> Y <--p₁-- W₁ --i₁--> X
  -- Take pullback of i₂ and p₁:
  --   pb --fst--> W₂
  --    |           |
  --   snd        i₂ (mono)
  --    |           |
  --    v           v
  --   W₁ --p₁---> Y   (p₁ epi)
  haveI : Epi p₁ := hp₁
  haveI : Mono i₁ := hi₁
  haveI : Mono i₂ := hi₂
  haveI : Epi p₂ := hp₂
  -- In abelian categories:
  -- - pullback.snd is mono because i₂ (first arg) is mono
  -- - pullback.fst is epi because p₁ (second arg) is epi
  refine ⟨pullback i₂ p₁, pullback.snd (f := i₂) (g := p₁) ≫ i₁,
          pullback.fst (f := i₂) (g := p₁) ≫ p₂, ?_, ?_⟩
  · -- pullback.snd is mono (since i₂ is mono), and i₁ is mono
    -- So composite is mono
    exact mono_comp _ _
  · -- pullback.fst is epi (since p₁ is epi in abelian cat), and p₂ is epi
    -- So composite is epi
    exact epi_comp _ _

/-- Subquotients of direct sums: if Y is a subquotient of any summand, it's a
subquotient of the biproduct. -/
theorem isSubquotient_of_biproduct {ι : Type*} [Fintype ι]
    [Abelian C] [HasFiniteBiproducts C] {X : ι → C} {Y : C}
    (i : ι) (h : IsSubquotient Y (X i)) : IsSubquotient Y (⨁ X) := by
  classical
  obtain ⟨Z, m, p, hm, hp⟩ := h
  refine ⟨Z, m ≫ biproduct.ι X i, p, ?_, hp⟩
  haveI : Mono m := hm
  exact mono_comp _ _

end Subquotient

/-! ## Subquotient Generator Condition

Book Proposition 1.8.17 hypothesis: "there exists X ∈ C such that any object of C
is a subquotient of a direct sum of finitely many copies of X"
-/

section SubquotientGenerator

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The subquotient generator condition from Proposition 1.8.17:
There exists X such that every object Y is a subquotient of X^n for some n.

Book: "there exists X ∈ C such that any object of C is a subquotient of
a direct sum of finitely many copies of X"

**Note:** Requires `HasFiniteBiproducts C` to make sense of X^n as a biproduct. -/
def HasSubquotientGenerator [HasFiniteBiproducts C] : Prop :=
  ∃ (X : C), ∀ (Y : C), ∃ (n : ℕ), IsSubquotient Y (⨁ fun (_ : Fin n) => X)

/-- Extract the generator from HasSubquotientGenerator. -/
noncomputable def subquotientGenerator [HasFiniteBiproducts C]
    (h : HasSubquotientGenerator C) : C :=
  h.choose

end SubquotientGenerator

/-! ## Projective Generator

A projective generator is an object that is both projective and a generator
(separator in mathlib terminology).

Book: "C has a projective generator" means ∃ P projective such that P is a generator.
-/

section ProjectiveGenerator

variable (C : Type u) [Category.{v} C]

/-- P is a projective generator if P is projective and P is a separator.

Book: "a projective generator P" is an object such that:
1. P is projective (Definition 1.6.5)
2. Every object is a quotient of P^n (equivalently, P is a generator/separator)

Mathlib: `Projective P` + `IsSeparator P` -/
def IsProjectiveGenerator (P : C) : Prop :=
  Projective P ∧ IsSeparator P

/-- A category has a projective generator if such an object exists. -/
def HasProjectiveGenerator : Prop :=
  ∃ (P : C), IsProjectiveGenerator C P

end ProjectiveGenerator

/-! ## Proposition 1.8.17: Gabber's Theorem

The main theorem: a locally finite abelian category with a subquotient generator
has a projective generator, hence is a finite abelian category.
-/

section GabberTheorem

variable (k : Type w) [Field k]
variable (C : Type u) [Category.{v} C] [Abelian C] [Preadditive C] [Linear k C]
variable [HasFiniteBiproducts C]

/-- **Proposition 1.8.17 (Gabber)**

Let C be a locally finite abelian category. Suppose that there exists X ∈ C
such that any object of C is a subquotient of a direct sum of finitely many
copies of X. Then C has a projective generator.

**Book:** Proposition 1.8.17, attributed to O. Gabber (see Deligne [De1], Prop 2.14)

**Proof idea (from the book):**
The proof uses the fact that in a locally finite category, every object has finite
length. Combined with the subquotient condition, one can construct a projective
generator by taking an appropriate projective cover.

**Note:** The full proof is non-trivial and relies on:
1. Every simple is a subquotient of X
2. Finitely many simples (since X has finite length)
3. Construction of projective generator from projective covers of simples
-/
theorem gabber_theorem [IsLocallyFinite k C]
    (hgen : ∃ (X : C), ∀ (Y : C), ∃ (n : ℕ), IsSubquotient Y (⨁ fun (_ : Fin n) => X)) :
    HasProjectiveGenerator C := by
  sorry

/-- Corollary: Under the hypotheses of Gabber's theorem, C is a finite abelian category
(assuming enough projectives, which follows from having a projective generator). -/
theorem finite_of_subquotient_generator [IsLocallyFinite k C]
    (hgen : ∃ (X : C), ∀ (Y : C), ∃ (n : ℕ), IsSubquotient Y (⨁ fun (_ : Fin n) => X))
    [EnoughProjectives C] : IsFiniteAbelian k C := by
  sorry

end GabberTheorem

/-! ## §1.8.18: Definition - Image of Exact Functor

Book Definition 1.8.18: "Let F : C → D be an exact functor between two locally finite
abelian categories. The image of F is the full subcategory Im F ⊂ D consisting of all
objects contained as subquotients in F(X) for some X ∈ C."
-/

section FunctorImage

variable {k : Type w} [Field k]
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
variable [Abelian C] [Abelian D] [Preadditive C] [Preadditive D]
variable [Linear k C] [Linear k D]

/-- An object Y in D is in the image of F if it is a subquotient of F(X) for some X in C.

Book Definition 1.8.18: "The image of F is the full subcategory Im F ⊂ D consisting of
all objects contained as subquotients in F(X) for some X ∈ C." -/
def IsInFunctorImage (F : C ⥤ D) (Y : D) : Prop :=
  ∃ (X : C), IsSubquotient Y (F.obj X)

/-- The predicate defining the full subcategory Im F.
An object Y is in Im F iff IsInFunctorImage F Y. -/
def FunctorImageProp (F : C ⥤ D) : D → Prop := IsInFunctorImage F

/-- Every object in the image of F (as F(X)) is in the functor image. -/
theorem isInFunctorImage_of_obj (F : C ⥤ D) (X : C) : IsInFunctorImage F (F.obj X) :=
  ⟨X, isSubquotient_refl _⟩

/-- Subquotients of objects in the functor image are also in the functor image. -/
theorem isInFunctorImage_of_subquotient (F : C ⥤ D) {Y Z : D}
    (hY : IsInFunctorImage F Y) (hZY : IsSubquotient Z Y) : IsInFunctorImage F Z := by
  obtain ⟨X, hYX⟩ := hY
  exact ⟨X, isSubquotient_trans hYX hZY⟩

end FunctorImage

/-! ## §1.8.19: Proposition - Im(F) is Finite if C is Finite

Book Proposition 1.8.19: "If C in Definition 1.8.18 is finite then Im F is a finite
abelian category."

Proof idea: If C is finite, let P be a projective generator. Then any object in Im F
is a subquotient of F(P)^n. By Gabber's theorem (1.8.17), Im F is finite.
-/

section ImageFinite

variable (k : Type w) [Field k]
variable (C D : Type u) [Category.{v} C] [Category.{v} D]
variable [Abelian C] [Abelian D] [Preadditive C] [Preadditive D]
variable [Linear k C] [Linear k D]
variable [HasFiniteBiproducts C] [HasFiniteBiproducts D]

/-- **Proposition 1.8.19**

If C is a finite abelian category and F : C → D is an exact functor between locally
finite abelian categories, then Im F is a finite abelian category.

**Book:** Proposition 1.8.19

**Proof idea:**
1. Im F is locally finite (inherits from D)
2. Let P be a projective generator of C
3. Any object of Im F is a subquotient of F(P)^n
4. By Gabber's theorem (1.8.17), Im F is finite

**Note:** The full proof requires showing Im F is closed under kernels/cokernels
and inherits the locally finite structure from D.
-/
theorem image_finite_of_finite (F : C ⥤ D) [IsLocallyFinite k C] [IsLocallyFinite k D]
    [EnoughProjectives C] (hfin : IsFiniteAbelian k C) :
    ∃ (X : D), ∀ (Y : D), IsInFunctorImage F Y →
      ∃ (n : ℕ), IsSubquotient Y (⨁ fun (_ : Fin n) => X) := by
  -- The generator is F(P) where P is the projective generator of C
  sorry

end ImageFinite

/-! ## Summary of §1.8.17-1.8.19

| Book | Lean | Notes |
|------|------|-------|
| Subquotient | `IsSubquotient Y X` | Z ↪ X, Z ↠ Y |
| Subquotient cond | `HasSubquotientGenerator C` | ∃ X, ∀ Y, Y subquot of X^n |
| Proj generator | `IsProjectiveGenerator P` | Projective + Separator |
| Prop 1.8.17 | `gabber_theorem` | Gabber's theorem (sorry) |
| Def 1.8.18 | `IsInFunctorImage F Y` | Y ∈ Im F |
| Prop 1.8.19 | `image_finite_of_finite` | Im F finite if C finite (sorry) |

**Gaps:**
- Full proof of Gabber's theorem requires detailed analysis of simple objects
- Full proof of Prop 1.8.19 requires showing Im F is closed under kernels/cokernels
-/

end LemmaFeld.TensorCategories.Chapter1
