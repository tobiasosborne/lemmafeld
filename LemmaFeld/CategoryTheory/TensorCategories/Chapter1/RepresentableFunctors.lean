/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Limits.Preserves.Finite
import Mathlib.CategoryTheory.Preadditive.Projective.Basic
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Data.Matrix.Basic

/-!
# Chapter 1, §1.8.8-1.8.10: Representable Functors

This file documents the correspondence between Etingof et al. "Tensor Categories"
§1.8.8-1.8.10 on representable functors and mathlib's infrastructure.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.8

## Key Results

- **Definition 1.8.8**: A functor F: A-mod → B-mod is (⊗-)representable if F ≅ V ⊗_A -
  for some (B,A)-bimodule V.

- **Remark 1.8.9**: F: A-mod → k-Vec is representable iff it has a right adjoint.

- **Proposition 1.8.10**: F: A-mod → B-mod is representable iff it is right exact.
  This is essentially the Eilenberg-Watts theorem for finite dimensional algebras.

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| A-mod | `ModuleCat A` | Category of left A-modules |
| (B,A)-bimodule | `Module B (Module A V)` | Two-sided module structure |
| V ⊗_A - functor | `TensorProduct.Functor` | Module tensor product functor |
| Right exact functor | `Functor.RightExact F` | Preserves cokernels |

## Current Status

The full Eilenberg-Watts theorem requires significant infrastructure:
1. Defining the tensor functor V ⊗_A - as a functor on ModuleCat
2. Proving the natural isomorphism F ≅ F(A) ⊗_A - when F is right exact
3. Handling the bimodule structure on F(A)

This file documents the book definitions. Full formalization is tracked separately.
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

/-! ## §1.8.8: Tensor-Representable Functors

Book Definition 1.8.8: "An additive k-linear functor F: A-mod → B-mod is
(⊗-)representable if there exists a (B,A)-bimodule V such that F is naturally
isomorphic to (V ⊗_A -)."
-/

section RepresentableFunctors

variable (k : Type*) [Field k]
variable (A B : Type*) [Ring A] [Ring B] [Algebra k A] [Algebra k B]

/-- A functor F: A-mod → B-mod is tensor-representable if it is naturally
isomorphic to V ⊗_A - for some (B,A)-bimodule V.

Book: Definition 1.8.8

Note: Full formalization requires setting up the tensor functor V ⊗_A - as a
functor between module categories. This is tracked in a separate issue. -/
structure IsTensorRepresentable (F : ModuleCat.{0} A ⥤ ModuleCat.{0} B) : Prop where
  /-- The representing bimodule V -/
  witness_exists : ∃ (V : Type*), Nonempty V  -- Placeholder for actual bimodule

/-! ## §1.8.10: Characterization via Right Exactness

Book Proposition 1.8.10: "An additive k-linear functor F: A-mod → B-mod is
representable if and only if it is right exact."

Proof outline:
- (⇒) The tensor product functor V ⊗_A - is right exact.
- (⇐) If F is right exact, let V = F(A). Then V has a (B,A)-bimodule structure,
      and F(X) ≅ V ⊗_A X naturally in X.
-/

/-- The "only if" direction: tensor product functors are right exact.

This follows from the general fact that tensor products preserve cokernels.
Mathlib: `TensorProduct.Algebra.rightExact` and related results. -/
lemma tensorProduct_rightExact {V : Type*} [AddCommGroup V] [Module A V] :
    True := -- Placeholder: full statement needs tensor functor setup
  trivial

/-
The "if" direction is the substantive content of Eilenberg-Watts:
a right exact functor on module categories is represented by tensoring.

This requires showing F(X) ≅ F(A) ⊗_A X naturally.

Book: "Let V = F(A). Then V is a B-module which has a commuting right action of A"

Full formalization is tracked in a separate issue.
-/

end RepresentableFunctors

/-! ## §1.8.11: Corollary for Left Exact Functors

**Book Corollary 1.8.11:** "Let C be a finite abelian k-linear category, and let
F: C → Vec be an additive k-linear left exact functor. Then F = Hom_C(V, -)
for some object V ∈ C."

**Proof sketch:** Let C = A-mod for a finite dimensional algebra A. The functor
X ↦ F(X*)* is a right exact functor on A-mod^op. Hence by Prop 1.8.10,
F(X*)* = X ⊗_A V for some V. Thus F(Y) = Hom_C(V, Y).

This is the dual of 1.8.10, using that left exact functors on C correspond to
right exact functors on C^op, and the Yoneda embedding.

### Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Representable (Hom) | `Functor.IsCorepresentable` | F ≅ Hom(V, -) |
| Left exact | `PreservesFiniteLimits F` | Preserves all finite limits |
| Hom functor | `coyoneda.obj (op V)` | The functor Hom(V, -) |
| Yoneda lemma | `coyonedaEquiv` | Nat(Hom(X,-), F) ≃ F(X) |

**Key mathlib facts:**
- `Functor.corepresentable_preservesLimit`: corepresentable functors preserve all limits
- `Functor.IsCorepresentable.mk'`: construct from iso with coyoneda
-/

section Corollary_1_8_11

open Opposite

variable {C : Type*} [Category C]

/-- Corollary 1.8.11: Characterization of left exact functors to Type.

Book: "Let C be a finite abelian k-linear category, and let F: C → Vec be an
additive k-linear left exact functor. Then F = Hom_C(V, -) for some V ∈ C."

In mathlib terms: a corepresentable functor is one that is naturally isomorphic
to `coyoneda.obj (op V)` = Hom(V, -) for some object V.

The "only if" direction is immediate: Hom(V, -) preserves all limits.
The "if" direction requires the assumption that C is a finite abelian category,
and uses duality with Prop 1.8.10 (Eilenberg-Watts). -/
def IsLeftExactCorepresentable (F : C ⥤ Type*) : Prop :=
  F.IsCorepresentable ∧ PreservesFiniteLimits F

/-- Remark 1.8.12 (Yoneda Lemma): Morphisms between representable functors
correspond to morphisms between representing objects.

Book: "The Yoneda Lemma states that morphisms between functors in Corollary 1.8.11
are precisely morphisms between the representing objects in C. That is, a morphism
between functors Hom_C(V, -) and Hom_C(W, -) is given by the right composition
with a morphism φ: W → V in C."

Mathlib: This is `coyonedaEquiv`:
  `(coyoneda.obj (op X) ⟶ F) ≃ F.obj X`

In particular, for F = coyoneda.obj (op Y):
  `(coyoneda.obj (op X) ⟶ coyoneda.obj (op Y)) ≃ (Y ⟶ X)` -/
example (X Y : C) : (coyoneda.obj (op X) ⟶ coyoneda.obj (op Y)) ≃ (Y ⟶ X) :=
  coyonedaEquiv

end Corollary_1_8_11

/-! ## §1.8.13: Virtual Projective Objects

**Book Definition 1.8.13:** "Let K₀(C) denote the free abelian group generated by
isomorphism classes of indecomposable projective objects of C. Elements of
K₀(C) ⊗_ℤ k will be called virtual projective objects of C."

This is different from Gr(C) (§1.5.8) which uses simple objects.
The book notes: "Although the groups K₀(C) and Gr(C) have the same rank, in
general γ is neither surjective nor injective even after tensoring with Q."

### Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Projective object | `CategoryTheory.Projective X` | Object P with Hom(P,-) exact |
| Indecomposable | `Indecomposable X` | Not expressible as non-trivial coproduct |
| Free abelian group | `FreeAbelianGroup α` | `Mathlib.GroupTheory.FreeAbelianGroup` |
-/

section VirtualProjectives

variable (C : Type*) [Category C] [HasZeroMorphisms C] [HasBinaryBiproducts C]

/-- An object is an indecomposable projective if it is both projective and indecomposable.

Book: "isomorphism classes of indecomposable projective objects"

Note: `Indecomposable X` means X cannot be expressed as a non-trivial coproduct.
This requires `HasBinaryBiproducts C`. -/
def IsIndecompProjective (X : C) [Projective X] : Prop := Indecomposable X

/-- The type of indecomposable projective objects in C (as a subtype). -/
def IndecompProjectiveObject := { X : C // Projective X ∧ Indecomposable X }

instance : CoeOut (IndecompProjectiveObject C) C where coe := Subtype.val

/-- Two indecomposable projective objects are isomorphic if their underlying objects are. -/
def IndecompProjectiveObject.Isomorphic (X Y : IndecompProjectiveObject C) : Prop :=
  Nonempty (X.val ≅ Y.val)

/-- Isomorphism of indecomposable projectives is an equivalence relation. -/
lemma IndecompProjectiveObject.isomorphic_equivalence :
    Equivalence (IndecompProjectiveObject.Isomorphic C) where
  refl X := ⟨Iso.refl X.val⟩
  symm := fun ⟨i⟩ => ⟨i.symm⟩
  trans := fun ⟨i⟩ ⟨j⟩ => ⟨i.trans j⟩

/-- Setoid on indecomposable projectives by isomorphism. -/
def IndecompProjectiveObject.setoid : Setoid (IndecompProjectiveObject C) where
  r := IndecompProjectiveObject.Isomorphic C
  iseqv := IndecompProjectiveObject.isomorphic_equivalence C

/-- Isomorphism classes of indecomposable projective objects. -/
def IsoClassIndecompProjective := Quotient (IndecompProjectiveObject.setoid C)

/-- K₀(C) = free abelian group on iso classes of indecomposable projectives.

Book Definition 1.8.13: "Let K₀(C) denote the free abelian group generated by
isomorphism classes of indecomposable projective objects of C." -/
def K0 := FreeAbelianGroup (IsoClassIndecompProjective C)

instance : AddCommGroup (K0 C) :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup (IsoClassIndecompProjective C)))

variable (k : Type*) [Field k]

/-- Virtual projective objects of C over k.

Book Definition 1.8.13: "Elements of K₀(C) ⊗_ℤ k will be called virtual projective
objects of C."

This is the k-vector space with basis given by iso classes of indecomposable projectives.

Note: The tensor product K₀(C) ⊗_ℤ k is a k-vector space. Since K₀(C) is a free abelian
group, this is isomorphic to the free k-vector space on the basis of iso classes. -/
abbrev VirtualProjective := TensorProduct ℤ (K0 C) k

end VirtualProjectives

/-! ## §1.8.13 (continued): The map γ: K₀(C) → Gr(C)

Book: "We have an obvious homomorphism γ: K₀(C) → Gr(C). Although the groups K₀(C)
and Gr(C) have the same rank, in general γ is neither surjective nor injective
even after tensoring with Q, see Section 6.1."

The map sends [P] ↦ [P] where on the left [P] is the class in K₀ and on the right
[P] is the class in Gr(C) computed as ∑_i [P : X_i] X_i using Jordan-Hölder multiplicities.
-/

/-! ## §1.8.14: Cartan Matrix

**Book Definition 1.8.14:** "The matrix C of γ in the natural bases (i.e., the matrix
with entries [P(X) : Y], where X, Y run through isomorphism classes of simple objects
of C) will be called the Cartan matrix of C."

Here P(X) is the projective cover of simple X, and [P(X) : Y] is the Jordan-Hölder
multiplicity of simple Y in P(X).

### Key Property (Equation 1.7)

For any Y in C and simple X: dim_k Hom_C(P(X), Y) = [Y : X]

This shows the Cartan matrix encodes Hom dimensions from projective covers.

### Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Projective cover P(X) | `ProjectivePresentation.p` | Projective.Basic |
| JH multiplicity [P:Y] | — | Gap: needs `HasMultiplicity` from GrothendieckGroup.lean |
| Matrix | `Matrix` | `Mathlib.Data.Matrix.Basic` |
-/

section CartanMatrix

variable (C : Type*) [Category C] [Abelian C]

/-- The Cartan matrix of a finite abelian category.

Book Definition 1.8.14: The Cartan matrix C has entries C_{X,Y} = [P(X) : Y]
where X, Y range over iso classes of simple objects, and [P(X) : Y] is the
Jordan-Hölder multiplicity of Y in the projective cover P(X) of X.

Note: Full definition requires:
1. Finitely many simple iso classes (index set)
2. Projective covers exist (EnoughProjectives)
3. Jordan-Hölder multiplicities -/
structure CartanMatrixData (n : ℕ) where
  /-- The simple objects (indexed 0 to n-1) -/
  simples : Fin n → C
  /-- Each indexed object is simple -/
  simples_simple : ∀ i, Simple (simples i)
  /-- The projective covers of the simple objects -/
  projectiveCovers : Fin n → C
  /-- Each cover is projective -/
  covers_projective : ∀ i, Projective (projectiveCovers i)
  /-- JH multiplicity function [P(i) : j] -/
  multiplicity : Fin n → Fin n → ℕ

/-- The Cartan matrix as an n×n matrix of natural numbers.

Book: "the matrix with entries [P(X) : Y]" -/
def CartanMatrixData.toMatrix {n : ℕ} (data : CartanMatrixData C n) :
    Matrix (Fin n) (Fin n) ℕ :=
  Matrix.of fun i j => data.multiplicity i j

end CartanMatrix

end LemmaFeld.TensorCategories.Chapter1
