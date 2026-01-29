/-
  LemmaFeld/CategoryTheory/TensorCategories/Chapter1/ExternalTensorProduct.lean

  §1.11.1: External Tensor Product Definition (Etingof et al.)

  This file establishes the foundations for Deligne's tensor product of
  locally finite abelian categories.

  **Book Definition 1.11.1:** Deligne's tensor product C ⊠ D is an abelian k-linear
  category which is universal for the functor assigning to every k-linear abelian
  category A the category of right exact in both variables bilinear bifunctors
  C × D → A.

  **Mathlib Status:**
  - Mathlib has `CategoryTheory.MonoidalCategory.ExternalProduct` in
    `Mathlib.CategoryTheory.Monoidal.ExternalProduct.Basic` but this is for
    diagrams (functors) into a monoidal category: given F₁ : J₁ ⥤ C and F₂ : J₂ ⥤ C,
    defines F₁ ⊠ F₂ : J₁ × J₂ ⥤ C by (j₁, j₂) ↦ F₁(j₁) ⊗ F₂(j₂).
  - This is NOT the same as the Deligne tensor product of categories.
  - Mathlib does NOT have:
    1. Locally finite abelian categories
    2. Deligne tensor product C ⊠ D of categories
    3. The universal property for right exact bifunctors

  **This file provides:**
  - Structure for locally finite abelian categories (prerequisites)
  - Right exactness predicates for bifunctors
  - The Deligne tensor product data structure (partial)
  - Documentation of the gap for future implementation
-/

import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Linear.Basic
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Subobject.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic

namespace LemmaFeld.TensorCategories.Chapter1

universe w v u

open CategoryTheory CategoryTheory.Limits

/-! ## §1.11 Prerequisites: Locally Finite Abelian Categories

A locally finite abelian category over k is an abelian k-linear category where:
- Every object has finite length
- Hom spaces are finite dimensional k-vector spaces
- Every object is the union of its finite length subobjects

Book reference: "Let C, D be two locally finite abelian categories over a field k."
-/

variable (k : Type w) [Field k]

/-- A category is locally finite abelian if it is:
- Abelian
- k-linear
- Has finite length objects (Artinian and Noetherian)
- Has finite dimensional Hom spaces

This captures the prerequisites for Deligne tensor products.
Book: §1.8 discusses locally finite (Artinian) and finite abelian categories.

**Note:** We use `WellFoundedLT/GT (Subobject X)` for finite length condition.
The finite dimensional Hom condition would require `Module.Finite k (X ⟶ Y)`. -/
class LocallyFiniteAbelian (C : Type u) [Category.{v} C] [Abelian C]
    [Preadditive C] [Linear k C] : Prop where
  /-- Every object is Artinian (DCC on subobjects) -/
  artinian : ∀ (X : C), WellFoundedLT (Subobject X)
  /-- Every object is Noetherian (ACC on subobjects) -/
  noetherian : ∀ (X : C), WellFoundedGT (Subobject X)

/-! ## §1.11 Definition 1.11.1: External Tensor Product

The external tensor product is a bifunctor ⊠ : C × D → C ⊠ D where C ⊠ D is
the Deligne tensor product, characterized by its universal property.

**Key properties:**
1. ⊠ is right exact in both variables
2. Universal: for any right exact F : C × D → A, there exists unique F̄ : C ⊠ D → A
   such that F̄ ∘ ⊠ = F
-/

variable {C : Type*} [Category C] [Abelian C]
variable {D : Type*} [Category D] [Abelian D]

/-- A bifunctor F : C × D → A is right exact in the first variable if for each
fixed Y ∈ D, the functor F(-, Y) : C → A preserves cokernels. -/
def IsRightExactFirst {A : Type*} [Category A] [Abelian A]
    (F : C × D ⥤ A) : Prop :=
  ∀ (Y : D), PreservesColimitsOfShape WalkingParallelPair
    (Functor.flip (Functor.curry.obj F) |>.obj Y)

/-- A bifunctor F : C × D → A is right exact in the second variable if for each
fixed X ∈ C, the functor F(X, -) : D → A preserves cokernels. -/
def IsRightExactSecond {A : Type*} [Category A] [Abelian A]
    (F : C × D ⥤ A) : Prop :=
  ∀ (X : C), PreservesColimitsOfShape WalkingParallelPair
    (Functor.curry.obj F |>.obj X)

/-- A bifunctor is right exact (in both variables) if it is right exact in each
variable separately. Book: "right exact in both variables bilinear bifunctors". -/
def IsRightExactBifunctor {A : Type*} [Category A] [Abelian A]
    (F : C × D ⥤ A) : Prop :=
  IsRightExactFirst F ∧ IsRightExactSecond F

/-- A bifunctor is exact (in both variables) if it is exact in each variable
separately. This is stronger than right exactness.
Book Proposition 1.11.2(iv): "The bifunctor ⊠ is exact in both variables". -/
def IsExactBifunctor {A : Type*} [Category A] [Abelian A]
    (F : C × D ⥤ A) : Prop :=
  (∀ (Y : D), PreservesFiniteLimits
    (Functor.flip (Functor.curry.obj F) |>.obj Y)) ∧
  (∀ (Y : D), PreservesFiniteColimits
    (Functor.flip (Functor.curry.obj F) |>.obj Y)) ∧
  (∀ (X : C), PreservesFiniteLimits
    (Functor.curry.obj F |>.obj X)) ∧
  (∀ (X : C), PreservesFiniteColimits
    (Functor.curry.obj F |>.obj X))

/-! ## The Deligne Tensor Product (Statement)

The full definition of C ⊠ D requires constructing a new category with the
universal property. For coalgebra categories, this is (C ⊗ D)-comod.

Book Proposition 1.11.2(iii): "Let C, D be coalgebras and let C = C-comod and
D = D-comod. Then C ⊠ D = (C ⊗ D)-comod."
-/

variable (C D)

/-- The structure of a Deligne tensor product of two locally finite abelian
categories. This is a category E equipped with a bifunctor ⊠ : C × D → E
satisfying the universal property.

**GAP:** Full implementation requires:
1. Constructing E (the tensor product category)
2. Proving the universal property
3. For coalgebra categories, showing E ≅ (C ⊗ D)-comod -/
structure DeligneTensorProductData (E : Type*) [Category E] [Abelian E] where
  /-- The external tensor product bifunctor -/
  box : C × D ⥤ E
  /-- The bifunctor is right exact in both variables -/
  rightExact : IsRightExactBifunctor box

/-! ## Hom Space Isomorphism (Statement)

Book Proposition 1.11.2(iv): The Deligne tensor product satisfies
Hom_C(X₁, Y₁) ⊗ Hom_D(X₂, Y₂) ≅ Hom_{C⊠D}(X₁ ⊠ X₂, Y₁ ⊠ Y₂)

This is a key computational property of the external tensor product.
-/

variable {C D}
variable [Preadditive C] [Preadditive D] [Linear k C] [Linear k D]

/-- The statement that Deligne tensor product satisfies the Hom space isomorphism.
Book: Hom_C(X₁, Y₁) ⊗ Hom_D(X₂, Y₂) ≅ Hom_{C⊠D}(X₁ ⊠ X₂, Y₁ ⊠ Y₂) -/
def HomTensorIso {E : Type*} [Category E] [Abelian E] [Linear k E]
    (data : DeligneTensorProductData C D E)
    (X₁ Y₁ : C) (X₂ Y₂ : D) : Prop :=
  Nonempty (TensorProduct k (X₁ ⟶ Y₁) (X₂ ⟶ Y₂) ≃ₗ[k]
    (data.box.obj (X₁, X₂) ⟶ data.box.obj (Y₁, Y₂)))

/-! ## Functoriality of Deligne Tensor Product

If F : C → C' and G : D → D' are right exact functors between locally finite
abelian categories, then there is an induced functor F ⊠ G : C ⊠ D → C' ⊠ D'.

Book: "If F : C → C' and G : D → D' are right exact functors between locally
finite abelian categories then one defines the functor F ⊠ G : C ⊠ D → C' ⊠ D'
using the defining universal property."

**GAP:** Full implementation requires the universal property construction.
-/

/-! ## Summary of Gaps

The following components are needed for a complete formalization:

1. **Locally finite abelian categories**: Need finite dimensional Hom spaces
   (requires `Module.Finite k (X ⟶ Y)` hypothesis)

2. **Deligne tensor product construction**: For general locally finite abelian
   categories, this requires constructing C ⊠ D via coalgebras and comodules
   (Theorem 1.9.15 guarantees C ≅ comod over some coalgebra)

3. **Universal property**: The full universal property involves:
   - Existence of extension F̄ for any right exact bifunctor F
   - Uniqueness of extension
   - Right exactness of extension

4. **Hom tensor isomorphism**: Proving the tensor-Hom adjunction property

5. **Functoriality**: Defining F ⊠ G for right exact functors F and G
-/

end LemmaFeld.TensorCategories.Chapter1
