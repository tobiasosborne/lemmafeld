/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Algebra.BigOperators.Fin
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.FittingLemma

/-!
# Chapter 1, Theorem 1.5.7: Krull-Schmidt Theorem

This file documents the Krull-Schmidt theorem from Etingof et al. "Tensor Categories" §1.5.

## Book Statement

**Theorem 1.5.7 (Krull-Schmidt)**: Any object of finite length admits a unique (up to an
isomorphism) decomposition into a direct sum of indecomposable objects.

More precisely: if X has finite length and X ≅ ⨁ᵢ Yᵢ ≅ ⨁ⱼ Zⱼ where all Yᵢ, Zⱼ are
indecomposable, then the index sets have the same cardinality and there is a bijection
σ such that Yᵢ ≅ Z_{σ(i)}.

## Mathematical Context

The Krull-Schmidt theorem is a fundamental result for finite length objects in abelian
categories. It generalizes the decomposition of finite abelian groups as direct sums
of cyclic groups of prime power order.

**Ingredients:**
1. Indecomposable objects (Def 1.5.6): X is indecomposable if X ≅ Y ⊕ Z implies Y = 0 or Z = 0
2. Finite length (Def 1.5.3): X has a Jordan-Hölder series
3. Local endomorphism ring: For indecomposable X of finite length, End(X) is local

**Key lemma:** Fitting's Lemma (see `FittingLemma.lean`).

## Mathlib Status

### What Mathlib Has

| Concept | Mathlib | Import |
|---------|---------|--------|
| Indecomposable X | `Indecomposable X` | `Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts` |
| Simple ⟹ Indecomposable | `indecomposable_of_simple` | `Mathlib.CategoryTheory.Simple` |
| Finite biproducts | `HasFiniteBiproducts C` | `Mathlib.CategoryTheory.Limits.Shapes.Biproducts` |
| IsFiniteLength (modules) | `IsFiniteLength R M` | `Mathlib.RingTheory.FiniteLength` |

### What Mathlib Lacks (Gaps)

1. **Categorical Krull-Schmidt theorem**: No theorem stating existence and uniqueness of
   indecomposable decompositions for finite length objects in abelian categories
2. **Local endomorphism ring**: No proof that End(X) is local for indecomposable finite
   length objects

## References

- Etingof et al. "Tensor Categories" (AMS 2015), §1.5, Theorem 1.5.7
- Krause "Krull-Schmidt categories and projective covers" (Expo. Math. 2015)
- Bass "Algebraic K-theory" (1968), original proof

-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

/-! ## Definition 1.5.6: Indecomposable Objects (recap)

Mathlib's definition: `Indecomposable X := ¬IsZero X ∧ ∀ Y Z, X ≅ Y ⊞ Z → IsZero Y ∨ IsZero Z`
-/

section IndecomposableRecap

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]

-- The definition is in mathlib
#check @Indecomposable

-- Indecomposable means: nonzero and any biproduct decomposition has a zero summand
example (X : C) : Indecomposable X ↔
    (¬IsZero X ∧ ∀ Y Z : C, (X ≅ Y ⊞ Z) → IsZero Y ∨ IsZero Z) := Iff.rfl

-- Simple objects are indecomposable
example [HasKernels C] (X : C) [Simple X] : Indecomposable X := indecomposable_of_simple X

end IndecomposableRecap

/-! ## Theorem 1.5.7: Krull-Schmidt (Statement)

**Existence**: Any object of finite length is isomorphic to a finite biproduct of
indecomposable objects.

**Uniqueness**: If X ≅ ⨁ᵢ Yᵢ ≅ ⨁ⱼ Zⱼ with all Yᵢ, Zⱼ indecomposable, then the
decompositions are equivalent up to permutation and isomorphism.

We state these as propositions. The proofs require significant development
(local rings, Fitting's lemma) that is beyond current mathlib coverage.
-/

section KrullSchmidtStatement

universe u v
variable (C : Type u) [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]

/-- An indecomposable decomposition of X is a finite family of indecomposable objects
whose biproduct is isomorphic to X. -/
structure IndecomposableDecomposition (X : C) where
  /-- Number of indecomposable summands -/
  n : ℕ
  /-- The family of indecomposable objects -/
  components : Fin n → C
  /-- Each component is indecomposable -/
  indecomposable : ∀ i, Indecomposable (components i)
  /-- The biproduct is isomorphic to X -/
  iso : X ≅ ⨁ components

/-- Two indecomposable decompositions are equivalent if they have the same length
and there is a permutation such that corresponding components are isomorphic. -/
def DecompositionsEquivalent {X : C}
    (d₁ d₂ : IndecomposableDecomposition C X) : Prop :=
  ∃ (h : d₁.n = d₂.n) (σ : Equiv.Perm (Fin d₁.n)),
    ∀ i, Nonempty (d₁.components i ≅ d₂.components ⟨σ i, h ▸ (σ i).isLt⟩)

/-- **Krull-Schmidt Existence** (Theorem 1.5.7, part 1):
Any object of finite length admits an indecomposable decomposition.

This is stated as a proposition; the proof requires showing that finite length objects
can be iteratively decomposed until all summands are indecomposable. -/
def KrullSchmidt_Existence : Prop :=
  ∀ X : C, IsFiniteLengthObject X → Nonempty (IndecomposableDecomposition C X)

/-- **Krull-Schmidt Uniqueness** (Theorem 1.5.7, part 2):
Any two indecomposable decompositions of the same object are equivalent.

This requires proving that End(Y) is local for indecomposable Y of finite length,
which uses Fitting's lemma. -/
def KrullSchmidt_Uniqueness : Prop :=
  ∀ X : C, ∀ d₁ d₂ : IndecomposableDecomposition C X, DecompositionsEquivalent C d₁ d₂

/-- The full Krull-Schmidt theorem: existence and uniqueness of indecomposable
decompositions for finite length objects. -/
def KrullSchmidt_Theorem : Prop :=
  KrullSchmidt_Existence C ∧ KrullSchmidt_Uniqueness C

end KrullSchmidtStatement

/-! ## Auxiliary Lemmas for Existence Proof -/

section AuxiliaryLemmas

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]

/-- Finite length is preserved under isomorphism (to the target). -/
lemma isFiniteLengthObject_of_iso {X Y : C} (i : X ≅ Y) (hX : IsFiniteLengthObject X) :
    IsFiniteLengthObject Y := by
  have hA := hX.artinian
  have hN := hX.noetherian
  constructor
  · exact isArtinianObject_of_mono i.inv
  · exact isNoetherianObject_of_mono i.inv

/-- A binary biproduct component has finite length if the biproduct does. -/
lemma isFiniteLengthObject_biprod_fst {X Y : C} (h : IsFiniteLengthObject (X ⊞ Y)) :
    IsFiniteLengthObject X := by
  haveI : IsArtinianObject (X ⊞ Y) := h.artinian
  haveI : IsNoetherianObject (X ⊞ Y) := h.noetherian
  constructor
  · exact isArtinianObject_of_mono (biprod.inl : X ⟶ X ⊞ Y)
  · exact isNoetherianObject_of_mono (biprod.inl : X ⟶ X ⊞ Y)

/-- A binary biproduct component has finite length if the biproduct does. -/
lemma isFiniteLengthObject_biprod_snd {X Y : C} (h : IsFiniteLengthObject (X ⊞ Y)) :
    IsFiniteLengthObject Y := by
  haveI : IsArtinianObject (X ⊞ Y) := h.artinian
  haveI : IsNoetherianObject (X ⊞ Y) := h.noetherian
  constructor
  · exact isArtinianObject_of_mono (biprod.inr : Y ⟶ X ⊞ Y)
  · exact isNoetherianObject_of_mono (biprod.inr : Y ⟶ X ⊞ Y)

/-- The empty biproduct is the zero object. -/
lemma biproduct_empty_isZero : IsZero (⨁ (Fin.elim0 : Fin 0 → C)) := by
  refine ⟨fun Y => ⟨⟨⟨biproduct.desc (fun b => b.elim0)⟩, fun f => ?_⟩⟩,
          fun Y => ⟨⟨⟨biproduct.lift (fun b => b.elim0)⟩, fun f => ?_⟩⟩⟩
  · ext ⟨j, hj⟩
    exact (Nat.not_lt_zero j hj).elim
  · ext ⟨j, hj⟩
    exact (Nat.not_lt_zero j hj).elim

/-- The singleton biproduct is isomorphic to its element. -/
def biproductSingletonIso (X : C) : ⨁ (fun _ : Fin 1 => X) ≅ X where
  hom := biproduct.desc (fun _ => 𝟙 X)
  inv := biproduct.lift (fun _ => 𝟙 X)
  hom_inv_id := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Category.assoc, biproduct.lift_π, biproduct.ι_desc_assoc, Category.id_comp]
    have hi' : i = 0 := Nat.lt_one_iff.mp hi
    have hj' : j = 0 := Nat.lt_one_iff.mp hj
    subst hi' hj'
    simp
  inv_hom_id := by simp [biproduct.lift_desc]

end AuxiliaryLemmas

/-! ## Well-Founded Recursion for Krull-Schmidt

The existence proof uses well-founded recursion on the subobject lattice.
Key insight: For an Artinian object X, the subobject lattice `Subobject X` is
well-founded (with respect to `<`). When X ≅ Y ⊕ Z with both nonzero:
- Y embeds into X as a proper subobject (via biprod.inl ≫ iso.inv)
- Z embeds into X as a proper subobject (via biprod.inr ≫ iso.inv)
- These subobjects are strictly less than ⊤, enabling recursion
-/

section WellFoundedRecursion

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]

/-- The subobject of X given by Y when X ≅ Y ⊕ Z. -/
def subobjectOfBiprodFst {X Y Z : C} (i : X ≅ Y ⊞ Z) : Subobject X :=
  Subobject.mk (biprod.inl ≫ i.inv)

/-- The subobject of X given by Z when X ≅ Y ⊕ Z. -/
def subobjectOfBiprodSnd {X Y Z : C} (i : X ≅ Y ⊞ Z) : Subobject X :=
  Subobject.mk (biprod.inr ≫ i.inv)

/-- If biprod.inl : Y → Y ⊕ Z is an iso, then Z is zero.

Proof: When biprod.inl is iso, its inverse must equal biprod.fst (both are left inverses
of a monomorphism). Then biprod.inr ≫ biprod.fst = 0, so biprod.inr ≫ inv inl = 0.
This means biprod.snd factors as 0, so 𝟙_Z = biprod.inr ≫ biprod.snd = 0.
-/
lemma isZero_of_isIso_biprod_inl {Y Z : C} (h : IsIso (biprod.inl : Y ⟶ Y ⊞ Z)) : IsZero Z := by
  haveI := h
  rw [IsZero.iff_id_eq_zero]
  -- inv biprod.inl = biprod.fst since both compose with biprod.inl to give 𝟙
  have heq : inv (biprod.inl : Y ⟶ Y ⊞ Z) = (biprod.fst : Y ⊞ Z ⟶ Y) := by
    apply (cancel_epi (biprod.inl : Y ⟶ Y ⊞ Z)).mp
    simp
  -- biprod.inr ≫ inv biprod.inl = 0
  have hzero : (biprod.inr : Z ⟶ Y ⊞ Z) ≫ inv (biprod.inl : Y ⟶ Y ⊞ Z) = 0 := by
    rw [heq, biprod.inr_fst]
  -- 𝟙_Z = biprod.inr ≫ biprod.snd, and factoring shows it equals 0
  -- biprod.inr ≫ biprod.snd = biprod.inr ≫ (inv inl ≫ inl) ≫ snd = (inr ≫ inv inl) ≫ (inl ≫ snd) = 0 ≫ 0 = 0
  have step1 : (biprod.inr : Z ⟶ Y ⊞ Z) ≫ biprod.snd =
               biprod.inr ≫ (inv (biprod.inl : Y ⟶ Y ⊞ Z) ≫ biprod.inl) ≫ biprod.snd := by
    congr 1
    rw [IsIso.inv_hom_id, Category.id_comp]
  have step2 : biprod.inr ≫ (inv (biprod.inl : Y ⟶ Y ⊞ Z) ≫ biprod.inl) ≫ biprod.snd =
               (biprod.inr ≫ inv (biprod.inl : Y ⟶ Y ⊞ Z)) ≫
               ((biprod.inl : Y ⟶ Y ⊞ Z) ≫ biprod.snd) := by
    simp only [Category.assoc]
  have step3 : (biprod.inr ≫ inv (biprod.inl : Y ⟶ Y ⊞ Z)) ≫
               ((biprod.inl : Y ⟶ Y ⊞ Z) ≫ biprod.snd) = 0 := by
    rw [hzero, biprod.inl_snd, zero_comp]
  rw [← biprod.inr_snd, step1, step2, step3]

/-- If biprod.inr : Z → Y ⊕ Z is an iso, then Y is zero. -/
lemma isZero_of_isIso_biprod_inr {Y Z : C} (h : IsIso (biprod.inr : Z ⟶ Y ⊞ Z)) : IsZero Y := by
  haveI := h
  rw [IsZero.iff_id_eq_zero]
  have heq : inv (biprod.inr : Z ⟶ Y ⊞ Z) = (biprod.snd : Y ⊞ Z ⟶ Z) := by
    apply (cancel_epi (biprod.inr : Z ⟶ Y ⊞ Z)).mp
    simp
  have hzero : (biprod.inl : Y ⟶ Y ⊞ Z) ≫ inv (biprod.inr : Z ⟶ Y ⊞ Z) = 0 := by
    rw [heq, biprod.inl_snd]
  have step1 : (biprod.inl : Y ⟶ Y ⊞ Z) ≫ biprod.fst =
               biprod.inl ≫ (inv (biprod.inr : Z ⟶ Y ⊞ Z) ≫ biprod.inr) ≫ biprod.fst := by
    congr 1
    rw [IsIso.inv_hom_id, Category.id_comp]
  have step2 : biprod.inl ≫ (inv (biprod.inr : Z ⟶ Y ⊞ Z) ≫ biprod.inr) ≫ biprod.fst =
               (biprod.inl ≫ inv (biprod.inr : Z ⟶ Y ⊞ Z)) ≫
               ((biprod.inr : Z ⟶ Y ⊞ Z) ≫ biprod.fst) := by
    simp only [Category.assoc]
  have step3 : (biprod.inl ≫ inv (biprod.inr : Z ⟶ Y ⊞ Z)) ≫
               ((biprod.inr : Z ⟶ Y ⊞ Z) ≫ biprod.fst) = 0 := by
    rw [hzero, biprod.inr_fst, zero_comp]
  rw [← biprod.inl_fst, step1, step2, step3]

/-- When X ≅ Y ⊕ Z with Z nonzero, the subobject from Y is proper (< ⊤).

The proof: If the subobject were ⊤, the embedding Y → X would be an iso,
forcing Z ≅ 0 (contradiction).
-/
lemma subobjectOfBiprodFst_lt_top {X Y Z : C} (i : X ≅ Y ⊞ Z) (hZ : ¬IsZero Z) :
    subobjectOfBiprodFst i < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h
  -- If subobjectOfBiprodFst i = ⊤, then the embedding Y → X is an iso
  have hiso : IsIso (biprod.inl ≫ i.inv) :=
    (Subobject.isIso_iff_mk_eq_top (biprod.inl ≫ i.inv)).mpr h
  -- Since i.inv is an iso, biprod.inl must be an iso
  haveI : IsIso i.inv := inferInstance
  have hinl : IsIso (biprod.inl : Y ⟶ Y ⊞ Z) := by
    have : biprod.inl = (biprod.inl ≫ i.inv) ≫ i.hom := by simp
    rw [this]; infer_instance
  -- But biprod.inl is an iso iff Z is zero
  exact hZ (isZero_of_isIso_biprod_inl hinl)

/-- When X ≅ Y ⊕ Z with Y nonzero, the subobject from Z is proper (< ⊤). -/
lemma subobjectOfBiprodSnd_lt_top {X Y Z : C} (i : X ≅ Y ⊞ Z) (hY : ¬IsZero Y) :
    subobjectOfBiprodSnd i < ⊤ := by
  rw [lt_top_iff_ne_top]
  intro h
  have hiso : IsIso (biprod.inr ≫ i.inv) :=
    (Subobject.isIso_iff_mk_eq_top (biprod.inr ≫ i.inv)).mpr h
  haveI : IsIso i.inv := inferInstance
  have hinr : IsIso (biprod.inr : Z ⟶ Y ⊞ Z) := by
    have : biprod.inr = (biprod.inr ≫ i.inv) ≫ i.hom := by simp
    rw [this]; infer_instance
  exact hY (isZero_of_isIso_biprod_inr hinr)

/-- The underlying object of the first biproduct subobject is isomorphic to Y. -/
def subobjectOfBiprodFst_underlyingIso {X Y Z : C} (i : X ≅ Y ⊞ Z) :
    Subobject.underlying.obj (subobjectOfBiprodFst i) ≅ Y :=
  Subobject.underlyingIso _

/-- The underlying object of the second biproduct subobject is isomorphic to Z. -/
def subobjectOfBiprodSnd_underlyingIso {X Y Z : C} (i : X ≅ Y ⊞ Z) :
    Subobject.underlying.obj (subobjectOfBiprodSnd i) ≅ Z :=
  Subobject.underlyingIso _

/-- Finite length is preserved under isomorphism (source direction). -/
lemma isFiniteLengthObject_of_iso' {X Y : C} (i : X ≅ Y) (hY : IsFiniteLengthObject Y) :
    IsFiniteLengthObject X :=
  isFiniteLengthObject_of_iso i.symm hY

/-- The underlying object of a subobject of a finite length object has finite length. -/
lemma isFiniteLengthObject_subobject {X : C} (hX : IsFiniteLengthObject X)
    (S : Subobject X) : IsFiniteLengthObject (Subobject.underlying.obj S) := by
  have hA := hX.artinian
  have hN := hX.noetherian
  constructor
  · exact isArtinianObject_of_mono S.arrow
  · exact isNoetherianObject_of_mono S.arrow

/-- When S : Subobject X and underlying.obj S ≅ Y ⊕ Z, create the subobject for Y. -/
def subobjectOfBiprodFst_via {X : C} (S : Subobject X) {Y Z : C}
    (iU : Subobject.underlying.obj S ≅ Y ⊞ Z) : Subobject X :=
  Subobject.mk (biprod.inl ≫ iU.inv ≫ S.arrow)

/-- When S : Subobject X and underlying.obj S ≅ Y ⊕ Z, create the subobject for Z. -/
def subobjectOfBiprodSnd_via {X : C} (S : Subobject X) {Y Z : C}
    (iU : Subobject.underlying.obj S ≅ Y ⊞ Z) : Subobject X :=
  Subobject.mk (biprod.inr ≫ iU.inv ≫ S.arrow)

/-- The first biproduct subobject is strictly less than S when Z is nonzero. -/
lemma subobjectOfBiprodFst_via_lt {X : C} (S : Subobject X) {Y Z : C}
    (iU : Subobject.underlying.obj S ≅ Y ⊞ Z) (hZ : ¬IsZero Z) :
    subobjectOfBiprodFst_via S iU < S := by
  rw [lt_iff_le_and_ne]
  constructor
  · -- subobjectOfBiprodFst_via S iU ≤ S
    unfold subobjectOfBiprodFst_via
    exact Subobject.mk_le_of_comm (biprod.inl ≫ iU.inv) (by simp [Category.assoc])
  · -- subobjectOfBiprodFst_via S iU ≠ S
    intro heq
    unfold subobjectOfBiprodFst_via at heq
    -- heq : mk (biprod.inl ≫ iU.inv ≫ S.arrow) = S
    -- Use isoOfEq to get an iso between underlying objects
    let φ := Subobject.isoOfEq _ _ heq
    -- φ : underlying.obj (mk (biprod.inl ≫ iU.inv ≫ S.arrow)) ≅ underlying.obj S
    let ψ := Subobject.underlyingIso (biprod.inl ≫ iU.inv ≫ S.arrow)
    -- ψ : underlying.obj (mk (...)) ≅ Y
    -- Compose: ψ.symm ≪≫ φ : Y ≅ underlying.obj S
    let θ : Y ≅ Subobject.underlying.obj S := ψ.symm ≪≫ φ
    -- Key: θ.hom ≫ S.arrow = (biprod.inl ≫ iU.inv ≫ S.arrow) by the arrow properties
    -- ψ.hom ≫ (mk ...).arrow = biprod.inl ≫ iU.inv ≫ S.arrow (by underlyingIso property)
    -- φ.hom ≫ S.arrow = (mk ...).arrow (by isoOfEq property)
    -- So θ.hom ≫ S.arrow = ψ.inv ≫ φ.hom ≫ S.arrow = ψ.inv ≫ (mk ...).arrow
    --                    = biprod.inl ≫ iU.inv ≫ S.arrow (by ψ.inv ≫ ψ.hom = 𝟙 on domain)
    have hθ : θ.hom ≫ S.arrow = (biprod.inl ≫ iU.inv) ≫ S.arrow := by
      -- θ = ψ.symm ≪≫ φ, where φ = isoOfEq heq, ψ = underlyingIso
      -- Key lemma: (underlyingIso f).inv ≫ (mk f).arrow = f
      have key : ψ.inv ≫ (Subobject.mk (biprod.inl ≫ iU.inv ≫ S.arrow)).arrow =
                 biprod.inl ≫ iU.inv ≫ S.arrow := Subobject.underlyingIso_arrow _
      -- (isoOfEq heq).hom ≫ S.arrow = (mk ...).arrow follows from heq and ofLE_arrow
      have hφ : φ.hom ≫ S.arrow = (Subobject.mk (biprod.inl ≫ iU.inv ≫ S.arrow)).arrow := by
        simp only [φ, Subobject.isoOfEq, Subobject.ofLE_arrow]
      simp only [θ, Iso.trans_hom, Iso.symm_hom, Category.assoc, hφ, key]
    -- Since S.arrow is mono: θ.hom = biprod.inl ≫ iU.inv
    have hθ_val : θ.hom = biprod.inl ≫ iU.inv := (cancel_mono S.arrow).mp hθ
    -- So biprod.inl ≫ iU.inv is an iso (equals θ.hom)
    have hiso : IsIso (biprod.inl ≫ iU.inv) := by rw [← hθ_val]; infer_instance
    -- Since iU.inv is an iso, biprod.inl is an iso
    haveI : IsIso (biprod.inl : Y ⟶ Y ⊞ Z) := by
      have h1 : biprod.inl = (biprod.inl ≫ iU.inv) ≫ iU.hom := by simp
      rw [h1]; infer_instance
    exact hZ (isZero_of_isIso_biprod_inl this)

/-- The second biproduct subobject is strictly less than S when Y is nonzero. -/
lemma subobjectOfBiprodSnd_via_lt {X : C} (S : Subobject X) {Y Z : C}
    (iU : Subobject.underlying.obj S ≅ Y ⊞ Z) (hY : ¬IsZero Y) :
    subobjectOfBiprodSnd_via S iU < S := by
  rw [lt_iff_le_and_ne]
  constructor
  · unfold subobjectOfBiprodSnd_via
    exact Subobject.mk_le_of_comm (biprod.inr ≫ iU.inv) (by simp [Category.assoc])
  · intro heq
    unfold subobjectOfBiprodSnd_via at heq
    let φ := Subobject.isoOfEq _ _ heq
    let ψ := Subobject.underlyingIso (biprod.inr ≫ iU.inv ≫ S.arrow)
    let θ : Z ≅ Subobject.underlying.obj S := ψ.symm ≪≫ φ
    have hθ : θ.hom ≫ S.arrow = (biprod.inr ≫ iU.inv) ≫ S.arrow := by
      have key : ψ.inv ≫ (Subobject.mk (biprod.inr ≫ iU.inv ≫ S.arrow)).arrow =
                 biprod.inr ≫ iU.inv ≫ S.arrow := Subobject.underlyingIso_arrow _
      have hφ : φ.hom ≫ S.arrow = (Subobject.mk (biprod.inr ≫ iU.inv ≫ S.arrow)).arrow := by
        simp only [φ, Subobject.isoOfEq, Subobject.ofLE_arrow]
      simp only [θ, Iso.trans_hom, Iso.symm_hom, Category.assoc, hφ, key]
    have hθ_val : θ.hom = biprod.inr ≫ iU.inv := (cancel_mono S.arrow).mp hθ
    have hiso : IsIso (biprod.inr ≫ iU.inv) := by rw [← hθ_val]; infer_instance
    haveI : IsIso (biprod.inr : Z ⟶ Y ⊞ Z) := by
      have h1 : biprod.inr = (biprod.inr ≫ iU.inv) ≫ iU.hom := by simp
      rw [h1]; infer_instance
    exact hY (isZero_of_isIso_biprod_inr this)

/-- The underlying object of subobjectOfBiprodFst_via is isomorphic to Y. -/
def subobjectOfBiprodFst_via_underlyingIso {X : C} (S : Subobject X) {Y Z : C}
    (iU : Subobject.underlying.obj S ≅ Y ⊞ Z) :
    Subobject.underlying.obj (subobjectOfBiprodFst_via S iU) ≅ Y :=
  Subobject.underlyingIso _

/-- The underlying object of subobjectOfBiprodSnd_via is isomorphic to Z. -/
def subobjectOfBiprodSnd_via_underlyingIso {X : C} (S : Subobject X) {Y Z : C}
    (iU : Subobject.underlying.obj S ≅ Y ⊞ Z) :
    Subobject.underlying.obj (subobjectOfBiprodSnd_via S iU) ≅ Z :=
  Subobject.underlyingIso _

end WellFoundedRecursion

/-! ## Krull-Schmidt Existence Proof -/

section KrullSchmidtExistence

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

/-- Map iso to binary biproduct. -/
def biprodMapIso {W X Y Z : C} (iWY : W ≅ Y) (iXZ : X ≅ Z) : W ⊞ X ≅ Y ⊞ Z :=
  biprod.mapIso iWY iXZ

/-- Helper: concatenated family of objects. -/
private def concatFin {n m : ℕ} (f : Fin n → C) (g : Fin m → C) : Fin (n + m) → C :=
  fun k => if h : k.val < n then f ⟨k.val, h⟩ else g ⟨k.val - n, by omega⟩

private lemma concatFin_left {n m : ℕ} (f : Fin n → C) (g : Fin m → C) (i : Fin n) :
    concatFin f g ⟨i.val, by omega⟩ = f i := by
  simp only [concatFin, i.isLt, ↓reduceDIte, Fin.eta]

private lemma concatFin_right {n m : ℕ} (f : Fin n → C) (g : Fin m → C) (j : Fin m) :
    concatFin f g ⟨n + j.val, by omega⟩ = g j := by
  simp only [concatFin]; have h : ¬ (n + j.val < n) := by omega
  simp only [h, ↓reduceDIte]; congr 1; simp only [Fin.ext_iff]; omega

private lemma concatFin_right' {n m : ℕ} (f : Fin n → C) (g : Fin m → C)
    (k : Fin (n + m)) (h : ¬ k.val < n) : concatFin f g k = g ⟨k.val - n, by omega⟩ := by
  simp only [concatFin, h, ↓reduceDIte]

private lemma add_sub_cancel_of_ge' {n k : ℕ} (h : n ≤ k) : n + (k - n) = k := by omega

private lemma biproduct_ι_cast' {J : Type*} [Fintype J] (h : J → C) [HasBiproduct h]
    (j j' : J) (hj : j = j') : biproduct.ι h j = eqToHom (by rw [hj]) ≫ biproduct.ι h j' := by
  subst hj; simp

private lemma biproduct_ι_fin_eq' {J : Type*} {D : Type*} [Category D] [Preadditive D]
    (p : J → D) [HasBiproduct p] (i j : J) (hij : i = j) :
    biproduct.ι p i = eqToHom (congrArg p hij) ≫ biproduct.ι p j := by
  subst hij; simp

/-- The biproduct of two biproducts is isomorphic to the biproduct over the concatenated index.

This is the key structural lemma for concatenating decompositions.

**Construction:**
- hom: (⨁ f) ⊞ (⨁ g) → ⨁ (concatenated)
  - On left: biproduct.ι f i ↦ biproduct.ι (concat) ⟨i.val, ...⟩
  - On right: biproduct.ι g j ↦ biproduct.ι (concat) ⟨n + j.val, ...⟩
- inv: ⨁ (concatenated) → (⨁ f) ⊞ (⨁ g)
  - For k < n: biproduct.ι k ↦ biproduct.ι f ⟨k, ...⟩ ≫ biprod.inl
  - For k ≥ n: biproduct.ι k ↦ biproduct.ι g ⟨k - n, ...⟩ ≫ biprod.inr
-/
def biproductBiprodIso {n m : ℕ} (f : Fin n → C) (g : Fin m → C) :
    (⨁ f) ⊞ (⨁ g) ≅ ⨁ (concatFin f g) where
  hom := biprod.desc
    (biproduct.desc fun i => eqToHom (concatFin_left f g i).symm ≫
      biproduct.ι (concatFin f g) ⟨i.val, by omega⟩)
    (biproduct.desc fun j => eqToHom (concatFin_right f g j).symm ≫
      biproduct.ι (concatFin f g) ⟨n + j.val, by omega⟩)
  inv := biproduct.desc fun k =>
    if h : k.val < n then
      eqToHom (concatFin_left f g ⟨k.val, h⟩) ≫ biproduct.ι f ⟨k.val, h⟩ ≫ biprod.inl
    else
      eqToHom (concatFin_right' f g k h) ≫ biproduct.ι g ⟨k.val - n, by omega⟩ ≫ biprod.inr
  hom_inv_id := by
    apply biprod.hom_ext'
    · simp only [Category.comp_id]
      rw [show biprod.inl ≫ biprod.desc _ _ ≫ _ =
             (biprod.inl ≫ biprod.desc _ _) ≫ _ from (Category.assoc _ _ _).symm,
           biprod.inl_desc]
      apply biproduct.hom_ext'; intro i
      rw [biproduct.ι_desc_assoc]
      simp only [Category.assoc, biproduct.ι_desc, i.isLt, ↓reduceDIte, eqToHom_trans_assoc,
                 Fin.eta, eqToHom_refl, Category.id_comp]
    · simp only [Category.comp_id]
      rw [show biprod.inr ≫ biprod.desc _ _ ≫ _ =
             (biprod.inr ≫ biprod.desc _ _) ≫ _ from (Category.assoc _ _ _).symm,
           biprod.inr_desc]
      apply biproduct.hom_ext'; intro j
      rw [biproduct.ι_desc_assoc]
      simp only [Category.assoc, biproduct.ι_desc]
      have h : ¬ (n + j.val < n) := by omega
      simp only [h, ↓reduceDIte, eqToHom_trans_assoc]
      have fin_eq : (⟨n + j.val - n, by omega⟩ : Fin m) = j := by
        simp only [Nat.add_sub_cancel_left, Fin.eta]
      rw [biproduct_ι_fin_eq' g _ j fin_eq]
      simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  inv_hom_id := by
    apply biproduct.hom_ext'; intro k
    simp only [biproduct.ι_desc_assoc, Category.comp_id]
    split_ifs with hk
    · simp only [Category.assoc, biprod.inl_desc, biproduct.ι_desc,
                 eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Fin.eta]
    · simp only [Category.assoc, biprod.inr_desc, biproduct.ι_desc]
      have fin_eq : (⟨n + (k.val - n), by omega⟩ : Fin (n + m)) = k :=
        Fin.ext (add_sub_cancel_of_ge' (Nat.not_lt.mp hk))
      rw [eqToHom_trans_assoc, biproduct_ι_cast' _ _ _ fin_eq]
      simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- **Krull-Schmidt Existence**: Every finite length object admits an indecomposable decomposition.

The proof proceeds by well-founded induction on the subobject lattice. For a finite length object X:
- If X is zero, use the empty decomposition
- If X is indecomposable, use the singleton decomposition
- If X ≅ Y ⊞ Z with both nonzero, recursively decompose Y and Z
-/
theorem krullSchmidt_existence (X : C) (hX : IsFiniteLengthObject X) :
    Nonempty (IndecomposableDecomposition C X) := by
  -- The key: use well-founded induction on Subobject X
  -- For Artinian objects, Subobject X has WellFoundedLT
  haveI : IsArtinianObject X := hX.artinian
  -- Prove: for every subobject S, underlying.obj S has a decomposition
  -- Then apply to ⊤ (which is X)
  suffices h : ∀ S : Subobject X,
      Nonempty (IndecomposableDecomposition C (Subobject.underlying.obj S)) by
    obtain ⟨d⟩ := h ⊤
    -- ⊤.arrow : underlying.obj ⊤ → X is an iso
    haveI : IsIso (⊤ : Subobject X).arrow := by rw [Subobject.isIso_arrow_iff_eq_top]
    let topIso : Subobject.underlying.obj (⊤ : Subobject X) ≅ X := asIso (⊤ : Subobject X).arrow
    exact ⟨{ n := d.n
             components := d.components
             indecomposable := d.indecomposable
             iso := topIso.symm ≪≫ d.iso }⟩
  -- Well-founded induction on S : Subobject X
  intro S
  induction S using WellFoundedLT.induction with
  | ind S ih =>
    set U := Subobject.underlying.obj S with hU
    have hUfl : IsFiniteLengthObject U := isFiniteLengthObject_subobject hX S
    by_cases hZero : IsZero U
    · exact ⟨emptyDecomposition U hZero⟩
    · by_cases hIndec : Indecomposable U
      · exact ⟨singletonDecomposition U hIndec⟩
      · -- U is decomposable: U ≅ Y ⊕ Z with both nonzero
        simp only [Indecomposable, not_and, not_forall, not_or] at hIndec
        obtain ⟨Y, Z, iU, hY, hZ⟩ := hIndec hZero
        -- Create subobjects of X for Y and Z, which are < S
        let sY := subobjectOfBiprodFst_via S iU
        let sZ := subobjectOfBiprodSnd_via S iU
        have sY_lt : sY < S := subobjectOfBiprodFst_via_lt S iU hZ
        have sZ_lt : sZ < S := subobjectOfBiprodSnd_via_lt S iU hY
        -- Recursive calls: decompositions of underlying.obj sY and underlying.obj sZ
        obtain ⟨dY'⟩ := ih sY sY_lt
        obtain ⟨dZ'⟩ := ih sZ sZ_lt
        -- Transport to Y and Z using the underlying isos
        let iY : Subobject.underlying.obj sY ≅ Y := subobjectOfBiprodFst_via_underlyingIso S iU
        let iZ : Subobject.underlying.obj sZ ≅ Z := subobjectOfBiprodSnd_via_underlyingIso S iU
        -- Decomposition of Y from dY'
        let dY : IndecomposableDecomposition C Y :=
          { n := dY'.n
            components := dY'.components
            indecomposable := dY'.indecomposable
            iso := iY.symm ≪≫ dY'.iso }
        -- Decomposition of Z from dZ'
        let dZ : IndecomposableDecomposition C Z :=
          { n := dZ'.n
            components := dZ'.components
            indecomposable := dZ'.indecomposable
            iso := iZ.symm ≪≫ dZ'.iso }
        -- Concatenate the decompositions for U
        refine ⟨⟨dY.n + dZ.n, fun k =>
          if h : k.val < dY.n then dY.components ⟨k.val, h⟩
          else dZ.components ⟨k.val - dY.n, by omega⟩, ?_, ?_⟩⟩
        · intro k
          simp only
          split_ifs with h
          · exact dY.indecomposable ⟨k.val, h⟩
          · exact dZ.indecomposable ⟨k.val - dY.n, by omega⟩
        · -- The iso: U ≅ Y ⊕ Z ≅ (⨁ dY.components) ⊕ (⨁ dZ.components) ≅ ⨁ (concatenated)
          exact iU ≪≫ biprodMapIso dY.iso dZ.iso ≪≫ biproductBiprodIso dY.components dZ.components

end KrullSchmidtExistence

/-! ## Krull-Schmidt Uniqueness Proof

The uniqueness proof uses:
1. **Local ring property**: End(X) is local for indecomposable finite-length X
2. **Exchange lemma**: Given two decompositions, the first component of one matches some component of the other
3. **Induction**: Remove matched components and recurse
-/

section KrullSchmidtUniqueness

universe u v
variable {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]

/-- In a local ring, if a + b is a unit, then a is a unit or b is a unit.
This is the contrapositive form of the local ring property. -/
lemma nonunits_add_of_local {R : Type*} [Ring R] [IsLocalRing R] {a b : R}
    (ha : ¬IsUnit a) (hb : ¬IsUnit b) : ¬IsUnit (a + b) := by
  intro h
  obtain ⟨u, hu⟩ := h
  have hinv : u⁻¹ * a + u⁻¹ * b = 1 := by
    rw [← mul_add, ← hu]; exact Units.inv_mul u
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one hinv with h | h
  · exact ha ((Units.isUnit_units_mul u⁻¹ a).mp h)
  · exact hb ((Units.isUnit_units_mul u⁻¹ b).mp h)

/-- In a local ring, if the sum of a finite family equals 1, then some element is a unit. -/
lemma exists_isUnit_of_finsum_eq_one {R : Type*} [Ring R] [IsLocalRing R] {n : ℕ}
    (f : Fin n → R) (hf : ∑ i, f i = 1) : ∃ i, IsUnit (f i) := by
  induction n with
  | zero => simp at hf
  | succ n ih =>
    rw [Fin.sum_univ_succ] at hf
    by_cases h0 : IsUnit (f 0)
    · exact ⟨0, h0⟩
    · -- f 0 + ∑ i, f i.succ = 1, and f 0 is not a unit
      -- By local ring property, ∑ i, f i.succ must be a unit
      have hrest : IsUnit (∑ i : Fin n, f i.succ) := by
        by_contra hnu
        have : ¬IsUnit (f 0 + ∑ i : Fin n, f i.succ) := nonunits_add_of_local h0 hnu
        rw [hf] at this; exact this isUnit_one
      -- Now we need: if ∑ i, g i is a unit, then some g i is a unit
      -- This follows by induction, but requires scaling by the inverse
      obtain ⟨u, hu⟩ := hrest
      have hscaled : ∑ i : Fin n, (u⁻¹ * f i.succ) = 1 := by
        rw [← Finset.mul_sum, ← hu]; exact Units.inv_mul u
      obtain ⟨j, hj⟩ := ih (fun i => u⁻¹ * f i.succ) hscaled
      exact ⟨j.succ, (Units.isUnit_units_mul u⁻¹ (f j.succ)).mp hj⟩

/-- **Exchange Lemma**: Given two indecomposable decompositions of the same object,
the first component of one decomposition is isomorphic to some component of the other.

This is the key lemma for Krull-Schmidt uniqueness. The proof uses:
1. The endomorphism projections Y₀ → X → Zⱼ → X → Y₀ sum to the identity
2. By local ring property, one of these is an isomorphism
3. Since both Y₀ and Zⱼ are indecomposable finite-length, the map Y₀ → Zⱼ is an iso
-/
lemma exchangeLemma {X : C} {n m : ℕ} (hn : 0 < n)
    (Y : Fin n → C) (Z : Fin m → C)
    (hY : ∀ i, Indecomposable (Y i)) (hZ : ∀ j, Indecomposable (Z j))
    (hYfl : ∀ i, IsFiniteLengthObject (Y i)) (hZfl : ∀ j, IsFiniteLengthObject (Z j))
    (iso₁ : X ≅ ⨁ Y) (iso₂ : X ≅ ⨁ Z) :
    ∃ j, Nonempty (Y ⟨0, hn⟩ ≅ Z j) := by
  -- The projections Y₀ → X → Zⱼ → X → Y₀ sum to identity on Y₀
  -- Each such projection is fⱼ ≫ gⱼ where fⱼ : Y₀ → Zⱼ and gⱼ : Zⱼ → Y₀
  -- By exists_isUnit_of_finsum_eq_one, some fⱼ ≫ gⱼ is a unit in End(Y₀)
  -- By Fitting's lemma, gⱼ ≫ fⱼ is also a unit in End(Zⱼ)
  -- Hence fⱼ is an isomorphism
  sorry

end KrullSchmidtUniqueness

/-! ## Summary

**Theorem 1.5.7 (Krull-Schmidt)**: Any object of finite length admits a unique
decomposition into indecomposables.

**Structure:**
- `KrullSchmidt.lean` - Theorem statements and indecomposable recap
- `FittingLemma.lean` - Chain stabilization lemmas and Fitting's Lemma

**Mathlib status**: The definition of `Indecomposable` exists, but the theorem itself
(existence and uniqueness of decompositions) is not formalized.
-/

end LemmaFeld.TensorCategories.Chapter1
