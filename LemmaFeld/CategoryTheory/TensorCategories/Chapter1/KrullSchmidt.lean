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

/-- Helper: sum of π ≫ ι equals identity for biproducts. -/
private lemma biproduct_sum_π_ι {n : ℕ} (f : Fin n → C) :
    ∑ j : Fin n, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f) := by
  apply biproduct.hom_ext'
  intro k
  rw [Preadditive.comp_sum, Category.comp_id]
  conv_lhs =>
    arg 2
    ext j
    rw [← Category.assoc, biproduct.ι_π]
  simp only [dite_comp, zero_comp, Finset.sum_dite_eq, Finset.mem_univ, ↓reduceIte, eqToHom_refl,
    Category.id_comp]

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
  -- Define the projection maps
  -- f_j : Y_0 → Z_j, g_j : Z_j → Y_0
  -- p_j = f_j ≫ g_j : End(Y_0)
  let Y₀ : C := Y ⟨0, hn⟩
  let f : (j : Fin m) → (Y₀ ⟶ Z j) := fun j =>
    biproduct.ι Y ⟨0, hn⟩ ≫ iso₁.inv ≫ iso₂.hom ≫ biproduct.π Z j
  let g : (j : Fin m) → (Z j ⟶ Y₀) := fun j =>
    biproduct.ι Z j ≫ iso₂.inv ≫ iso₁.hom ≫ biproduct.π Y ⟨0, hn⟩
  let p : Fin m → End Y₀ := fun j => f j ≫ g j
  -- Step 1: Show ∑_j p_j = 1 in End(Y₀)
  have sum_eq_id : ∑ i : Fin m, p i = 1 := by
    rw [End.one_def]
    show ∑ j : Fin m, (biproduct.ι Y ⟨0, hn⟩ ≫ iso₁.inv ≫ iso₂.hom ≫ biproduct.π Z j) ≫
         (biproduct.ι Z j ≫ iso₂.inv ≫ iso₁.hom ≫ biproduct.π Y ⟨0, hn⟩) = 𝟙 Y₀
    simp only [Category.assoc]
    have step1 : ∀ j : Fin m,
      biproduct.ι Y ⟨0, hn⟩ ≫ iso₁.inv ≫ iso₂.hom ≫ biproduct.π Z j ≫
      biproduct.ι Z j ≫ iso₂.inv ≫ iso₁.hom ≫ biproduct.π Y ⟨0, hn⟩ =
      biproduct.ι Y ⟨0, hn⟩ ≫ iso₁.inv ≫ iso₂.hom ≫
      ((biproduct.π Z j ≫ biproduct.ι Z j) ≫ iso₂.inv ≫ iso₁.hom ≫ biproduct.π Y ⟨0, hn⟩) := by
      intro j; simp only [Category.assoc]
    simp_rw [step1]
    simp only [← Preadditive.comp_sum]
    have sum_factor : ∑ j : Fin m, (biproduct.π Z j ≫ biproduct.ι Z j) ≫ iso₂.inv ≫ iso₁.hom ≫
                biproduct.π Y ⟨0, hn⟩ =
                iso₂.inv ≫ iso₁.hom ≫ biproduct.π Y ⟨0, hn⟩ := by
      rw [← Preadditive.sum_comp, biproduct_sum_π_ι, Category.id_comp]
    rw [sum_factor]
    simp only [Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc, biproduct.ι_π_self]
    rfl
  -- Step 2: Get local ring instance on End(Y₀)
  haveI : IsLocalRing (End Y₀) :=
    isLocalRing_end_of_indecomposable_finiteLength (hY ⟨0, hn⟩) (hYfl ⟨0, hn⟩)
  -- Step 3: Apply exists_isUnit_of_finsum_eq_one
  obtain ⟨j, hj⟩ := exists_isUnit_of_finsum_eq_one p sum_eq_id
  -- Step 4: p j = f j ≫ g j is a unit, so f j ≫ g j is an isomorphism
  have hfg_iso : IsIso (p j) := by rwa [isUnit_iff_isIso] at hj
  -- Step 5: f j is mono (since f j ≫ g j is iso, hence mono)
  haveI hfg_mono : Mono (f j ≫ g j) := inferInstance
  have hf_mono : Mono (f j) := mono_of_mono_fac (g := g j) (h := f j ≫ g j) rfl
  -- Step 6: q = g j ≫ f j in End(Z j); by Fitting, either nilpotent or unit
  let q : End (Z j) := g j ≫ f j
  haveI hZj_local : IsLocalRing (End (Z j)) :=
    isLocalRing_end_of_indecomposable_finiteLength (hZ j) (hZfl j)
  have hq_or : IsNilpotent q ∨ IsUnit q := fitting_lemma q (hZ j) (hZfl j)
  -- Key lemma: (f ≫ g)^(n+1) = f ≫ (g ≫ f)^n ≫ g
  have pow_key : ∀ k : ℕ, (p j)^(k + 1) = f j ≫ (q^k) ≫ g j := by
    intro k
    induction k with
    | zero =>
      simp only [Nat.zero_add, pow_one, pow_zero, End.one_def, Category.id_comp]; rfl
    | succ l ihl =>
      -- Goal: (p j)^(l+2) = f j ≫ q^(l+1) ≫ g j
      -- Use pow_succ (not pow_succ') since End.mul_def is x * y = y ≫ x
      -- pow_succ : q^(l+1) = q^l * q = q ≫ q^l (with End's opposite mul)
      rw [pow_succ (p j) (l + 1), ihl, End.mul_def, pow_succ q l, End.mul_def]
      -- Goal: p j ≫ f j ≫ (q ^ l) ≫ g j = f j ≫ (q ≫ q ^ l) ≫ g j
      -- Unfold p j = f j ≫ g j and q = g j ≫ f j
      -- LHS = (f j ≫ g j) ≫ f j ≫ q^l ≫ g j = f j ≫ g j ≫ f j ≫ q^l ≫ g j = f j ≫ q ≫ q^l ≫ g j
      -- RHS = f j ≫ q ≫ q^l ≫ g j
      calc p j ≫ f j ≫ (q ^ l) ≫ g j
        = (f j ≫ g j) ≫ f j ≫ (q ^ l) ≫ g j := rfl
      _ = f j ≫ g j ≫ f j ≫ (q ^ l) ≫ g j := by simp only [Category.assoc]
      _ = f j ≫ (g j ≫ f j) ≫ (q ^ l) ≫ g j := by simp only [Category.assoc]
      _ = f j ≫ q ≫ (q ^ l) ≫ g j := rfl  -- since q := g j ≫ f j
      _ = f j ≫ (q ≫ q ^ l) ≫ g j := by simp only [Category.assoc]
  -- If q is nilpotent, contradiction with p j being a unit
  have hq_unit : IsUnit q := by
    rcases hq_or with ⟨k, hk_eq⟩ | hunit
    · -- nilpotent case: q^k = 0
      exfalso
      rcases k with _ | k'
      · -- q^0 = 0 means 1 = 0 in End(Z j), so Z j is zero
        simp only [pow_zero] at hk_eq
        have hid_eq_zero : 𝟙 (Z j) = 0 := by
          simp only [End.one_def] at hk_eq; exact hk_eq
        have hZj_zero : IsZero (Z j) := (Limits.IsZero.iff_id_eq_zero (Z j)).mpr hid_eq_zero
        exact (hZ j).1 hZj_zero
      · -- q^(k'+1) = 0, so (p j)^(k'+2) = f ≫ q^(k'+1) ≫ g = 0
        have h_pow_zero : (p j)^(k' + 2) = 0 := by
          rw [pow_key (k' + 1), hk_eq]
          simp only [Limits.zero_comp, Limits.comp_zero]
        have hpj_unit_pow : IsUnit ((p j)^(k' + 2)) := hj.pow (k' + 2)
        rw [h_pow_zero] at hpj_unit_pow
        exact not_isUnit_zero hpj_unit_pow
    · exact hunit
  -- Step 7: q is a unit, hence iso
  have hq_iso : IsIso q := by rwa [isUnit_iff_isIso] at hq_unit
  -- Step 8: f j is epi (since g j ≫ f j = q is iso, hence epi)
  haveI hgf_epi : Epi (g j ≫ f j) := inferInstance
  have hf_epi : Epi (f j) := epi_of_epi_fac (f := g j) (h := g j ≫ f j) rfl
  -- Step 9: f j is mono + epi in abelian, so iso
  have hf_iso : IsIso (f j) := isIso_of_mono_of_epi (f j)
  exact ⟨j, ⟨asIso (f j)⟩⟩

/-! ### Biproduct Cancellation Infrastructure

These lemmas enable the "cancel matching component" step in KS uniqueness:
Given `Y₀ ⊞ rest_Y ≅ Z_j ⊞ rest_Z` with `Y₀ ≅ Z_j`, conclude `rest_Y ≅ rest_Z`.
-/

/-- Swap j to position 0 in Fin n. Uses Equiv.swap. -/
private def finSwapFront {n : ℕ} (j : Fin n) : Fin n ≃ Fin n :=
  Equiv.swap j ⟨0, j.pos⟩

@[simp]
private lemma finSwapFront_apply_self {n : ℕ} (j : Fin n) :
    finSwapFront j j = ⟨0, j.pos⟩ := Equiv.swap_apply_left j ⟨0, j.pos⟩

@[simp]
private lemma finSwapFront_apply_zero {n : ℕ} (j : Fin n) :
    finSwapFront j ⟨0, j.pos⟩ = j := Equiv.swap_apply_right j ⟨0, j.pos⟩

private lemma finSwapFront_symm {n : ℕ} (j : Fin n) : (finSwapFront j).symm = finSwapFront j := by
  unfold finSwapFront
  ext k
  simp only [Equiv.symm_swap]

/-- Biproduct reindexed by swapping j to front. -/
private def biproductSwapFrontIso {n : ℕ} (f : Fin n → C) (j : Fin n) :
    ⨁ f ≅ ⨁ (f ∘ (finSwapFront j).symm) := by
  have hw : ∀ k, (f ∘ (finSwapFront j).symm) ((finSwapFront j) k) ≅ f k := fun k => by
    simp only [Function.comp_apply, Equiv.symm_apply_apply]; exact Iso.refl _
  exact biproduct.whiskerEquiv (finSwapFront j) hw

/-- After swapping j to front, component 0 is f j. -/
private lemma biproductSwapFront_zero {n : ℕ} (f : Fin n → C) (j : Fin n) :
    (f ∘ (finSwapFront j).symm) ⟨0, j.pos⟩ = f j := by
  simp only [Function.comp_apply, finSwapFront_symm, finSwapFront_apply_zero]

/-- Tail of a family, for head-tail splitting. -/
private def finTail {n : ℕ} (hn : 0 < n) (f : Fin n → C) : Fin (n - 1) → C :=
  fun i => f ⟨i.val + 1, by omega⟩

/-- Head-tail split for biproducts: ⨁ f ≅ f 0 ⊞ ⨁ (tail f) for n > 0. -/
private def biproductHeadTailIso {n : ℕ} (hn : 0 < n) (f : Fin n → C) :
    ⨁ f ≅ f ⟨0, hn⟩ ⊞ ⨁ (finTail hn f) := by
  -- Strategy: Use biproductBiprodIso with singleton head
  let head : Fin 1 → C := fun _ => f ⟨0, hn⟩
  let tail : Fin (n - 1) → C := finTail hn f
  -- biproductBiprodIso gives: (⨁ head) ⊞ (⨁ tail) ≅ ⨁ (concatFin head tail)
  -- We have: 1 + (n - 1) = n
  have hn_eq : 1 + (n - 1) = n := by omega
  -- Build equivalence Fin n ≃ Fin (1 + (n - 1))
  let e : Fin n ≃ Fin (1 + (n - 1)) := {
    toFun := fun i => ⟨i.val, by omega⟩
    invFun := fun k => ⟨k.val, by omega⟩
    left_inv := fun i => by ext; simp
    right_inv := fun k => by ext; simp
  }
  -- The reindexed family matches concatFin head tail
  have heq : ∀ k : Fin (1 + (n - 1)), concatFin head tail k = f ⟨k.val, by omega⟩ := fun k => by
    simp only [concatFin, head, tail, finTail]
    by_cases hk : k.val < 1
    · simp only [hk, ↓reduceDIte]; congr 1; ext
      exact (Nat.lt_one_iff.mp hk).symm
    · simp only [hk, ↓reduceDIte]; congr 1; ext
      have hk_ge : k.val ≥ 1 := Nat.not_lt.mp hk
      exact Nat.sub_add_cancel hk_ge
  -- Build the composite iso
  have hw : ∀ i, f (e.symm (e i)) ≅ f i := fun i => eqToIso (by simp only [Equiv.symm_apply_apply])
  let iso_reindex : ⨁ f ≅ ⨁ (f ∘ e.symm) := biproduct.whiskerEquiv e hw
  have hw2 : ∀ k, (f ∘ e.symm) k ≅ f ⟨k.val, by omega⟩ := fun k =>
    eqToIso (by simp only [Function.comp_apply, e]; rfl)
  let iso_cast : ⨁ (f ∘ e.symm) ≅ ⨁ (fun k : Fin (1 + (n - 1)) => f ⟨k.val, by omega⟩) :=
    biproduct.mapIso hw2
  let iso_concat : ⨁ (fun k : Fin (1 + (n - 1)) => f ⟨k.val, by omega⟩) ≅ ⨁ (concatFin head tail) :=
    biproduct.mapIso (fun k => eqToIso (heq k).symm)
  let iso_split : ⨁ (concatFin head tail) ≅ (⨁ head) ⊞ (⨁ tail) := (biproductBiprodIso head tail).symm
  -- Finally, ⨁ head ≅ head 0 = f 0 via biproductSingletonIso
  let iso_head : ⨁ head ≅ f ⟨0, hn⟩ := biproductSingletonIso (f ⟨0, hn⟩)
  exact iso_reindex ≪≫ iso_cast ≪≫ iso_concat ≪≫ iso_split ≪≫ biprod.mapIso iso_head (Iso.refl _)

/-- A biproduct summand of a zero object is zero. -/
lemma isZero_component_of_isZero_biproduct {n : ℕ} (f : Fin n → C)
    (hZ : IsZero (⨁ f)) (i : Fin n) : IsZero (f i) := by
  rw [IsZero.iff_id_eq_zero]
  have h1 : biproduct.ι f i ≫ biproduct.π f i = 𝟙 (f i) := biproduct.ι_π_self f i
  have h2 : biproduct.ι f i ≫ biproduct.π f i = 0 := by
    have hι := hZ.eq_zero_of_tgt (biproduct.ι f i)
    rw [hι, Limits.zero_comp]
  rw [← h1, h2]

/-- If X is zero and X ≅ ⨁ f with all f i indecomposable, then n = 0. -/
lemma eq_zero_of_isZero_indecomposable_decomposition {n : ℕ} (f : Fin n → C)
    (hf : ∀ i, Indecomposable (f i)) (Y : C) (hY : IsZero Y)
    (e : Y ≅ ⨁ f) : n = 0 := by
  by_contra h
  push_neg at h
  have hn : 0 < n := Nat.pos_of_ne_zero h
  have hZbiprod : IsZero (⨁ f) := hY.of_iso e.symm
  have hZf0 : IsZero (f ⟨0, hn⟩) := isZero_component_of_isZero_biproduct f hZbiprod ⟨0, hn⟩
  exact (hf ⟨0, hn⟩).1 hZf0

/-- Finite length transfer through biproduct iso. -/
lemma isFiniteLengthObject_of_biproduct_iso {n : ℕ} {X : C} (f : Fin n → C)
    (e : X ≅ ⨁ f) (hX : IsFiniteLengthObject X) (i : Fin n) : IsFiniteLengthObject (f i) := by
  have hBiprod : IsFiniteLengthObject (⨁ f) := isFiniteLengthObject_of_iso e hX
  haveI : IsArtinianObject (⨁ f) := hBiprod.artinian
  haveI : IsNoetherianObject (⨁ f) := hBiprod.noetherian
  constructor
  · exact isArtinianObject_of_mono (biproduct.ι f i)
  · exact isNoetherianObject_of_mono (biproduct.ι f i)

/-- Indecomposability transfers through isomorphisms. -/
lemma indecomposable_of_iso_indecomposable {X Y : C} (hX : Indecomposable X) (e : X ≅ Y) :
    Indecomposable Y := by
  constructor
  · intro hYz
    -- hYz : IsZero Y, e : X ≅ Y, want: IsZero X
    exact hX.1 (hYz.of_iso e)
  · intro A B eAB
    -- eAB : Y ≅ A ⊞ B, e : X ≅ Y, want X ≅ A ⊞ B
    have eXAB : X ≅ A ⊞ B := e ≪≫ eAB
    exact hX.2 A B eXAB

/-- When n = 1, the biproduct over Fin n is isomorphic to the single component. -/
def biproductSingletonIso' {n : ℕ} (hn : n = 1) (f : Fin n → C) :
    ⨁ f ≅ f ⟨0, by omega⟩ where
  hom := biproduct.π f ⟨0, by omega⟩
  inv := biproduct.ι f ⟨0, by omega⟩
  hom_inv_id := by
    ext ⟨i, hi⟩ ⟨j, hj⟩
    simp only [Category.assoc, biproduct.ι_π_assoc, Category.id_comp]
    have hi0 : i = 0 := by omega
    have hj0 : j = 0 := by omega
    subst hi0 hj0
    simp [biproduct.ι_π_self]
  inv_hom_id := biproduct.ι_π_self f ⟨0, by omega⟩

/-- Helper: if a biproduct has a nonzero component, the biproduct is nonzero. -/
private lemma not_isZero_biproduct_of_component {J : Type*} [Fintype J] (g : J → C)
    [HasBiproduct g] (j : J) (h : ¬IsZero (g j)) : ¬IsZero (⨁ g) := by
  intro hZ
  apply h
  rw [Limits.IsZero.iff_id_eq_zero]
  have hι : biproduct.ι g j = 0 := hZ.eq_of_tgt _ _
  calc 𝟙 (g j) = biproduct.ι g j ≫ biproduct.π g j := (biproduct.ι_π_self g j).symm
    _ = 0 ≫ biproduct.π g j := by rw [hι]
    _ = 0 := zero_comp

/-- For n > 1, concatFin of singleton head and (n-1)-element tail equals f (reindexed). -/
private lemma concatFin_eq_reindex {n : ℕ} (hn : 1 ≤ n) (f : Fin n → C) :
    concatFin (fun _ : Fin 1 => f ⟨0, by omega⟩)
              (fun i : Fin (n - 1) => f ⟨i.val + 1, by omega⟩) =
    (fun k : Fin (1 + (n - 1)) => f ⟨k.val, by omega⟩) := by
  ext k
  simp only [concatFin]
  by_cases hk : k.val < 1
  · simp only [hk, ↓reduceDIte]
    have hk0 : k.val = 0 := by omega
    congr 1; ext; simp [hk0]
  · simp only [hk, ↓reduceDIte]
    have hk_ge : k.val ≥ 1 := by omega
    congr 1; ext
    -- k.val - 1 + 1 = k.val when k.val ≥ 1
    exact Nat.sub_add_cancel hk_ge

/-- A biproduct of indecomposables with more than one component is decomposable. -/
lemma not_indecomposable_of_biproduct_gt_one {n : ℕ} (f : Fin n → C) (hn : 1 < n)
    (hf : ∀ i, Indecomposable (f i)) : ¬Indecomposable (⨁ f) := by
  intro ⟨hnonzero, hdecomp⟩
  -- Split ⨁ f into f 0 ⊕ (the rest) using biproductBiprodIso
  have h0 : 0 < n := Nat.lt_trans Nat.zero_lt_one hn
  have h1 : 1 < n := hn
  -- f 0 and f 1 are both nonzero (indecomposable ⟹ nonzero)
  have hf0_nz : ¬IsZero (f ⟨0, h0⟩) := (hf ⟨0, h0⟩).1
  have hf1_nz : ¬IsZero (f ⟨1, h1⟩) := (hf ⟨1, h1⟩).1
  -- Define head and tail
  let head : Fin 1 → C := fun _ => f ⟨0, h0⟩
  let tail : Fin (n - 1) → C := fun i => f ⟨i.val + 1, by omega⟩
  -- Key: 1 + (n - 1) = n
  have hn_eq : 1 + (n - 1) = n := by omega
  -- The concatFin of head and tail equals f (after reindexing)
  have hconcat : concatFin head tail = (fun k : Fin (1 + (n - 1)) => f ⟨k.val, by omega⟩) :=
    concatFin_eq_reindex (by omega : 1 ≤ n) f
  -- Build the iso: ⨁ f ≅ (⨁ head) ⊞ (⨁ tail)
  -- Define the equivalence Fin n ≃ Fin (1 + (n - 1))
  have hn1 : 1 + (n - 1) = n := hn_eq
  let e : Fin n ≃ Fin (1 + (n - 1)) := {
    toFun := fun i => ⟨i.val, by omega⟩
    invFun := fun k => ⟨k.val, by omega⟩
    left_inv := fun i => by ext; simp
    right_inv := fun k => by ext; simp
  }
  -- First, ⨁ f ≅ ⨁ (reindexed f) via e
  let g := fun k : Fin (1 + (n - 1)) => f ⟨k.val, by omega⟩
  have iso_reindex : ⨁ f ≅ ⨁ g :=
    biproduct.whiskerEquiv e (fun i => eqToIso (by simp only [g, e]; rfl))
  -- Then, ⨁ (reindexed f) ≅ ⨁ (concatFin head tail)
  have iso_concat : ⨁ g ≅ ⨁ (concatFin head tail) :=
    biproduct.whiskerEquiv (Equiv.refl _) (fun k => eqToIso (by
      simp only [Equiv.refl_apply]
      exact congrFun hconcat k))
  -- Finally, biproductBiprodIso.symm : ⨁ (concatFin head tail) ≅ (⨁ head) ⊞ (⨁ tail)
  let split_iso : ⨁ f ≅ (⨁ head) ⊞ (⨁ tail) :=
    iso_reindex ≪≫ iso_concat ≪≫ (biproductBiprodIso head tail).symm
  -- Now apply hdecomp to split_iso
  have h_decomp := hdecomp (⨁ head) (⨁ tail) split_iso
  -- Show both components are nonzero
  have h_head_nz : ¬IsZero (⨁ head) := by
    have : ⨁ head ≅ f ⟨0, h0⟩ := biproductSingletonIso (f ⟨0, h0⟩)
    intro hZ
    exact hf0_nz (hZ.of_iso this.symm)
  have h_tail_nz : ¬IsZero (⨁ tail) := by
    have h1' : (1 : ℕ) < n := h1
    have hn1 : 0 < n - 1 := by omega
    -- tail ⟨0, hn1⟩ = f ⟨1, h1⟩ which is nonzero
    have htail0 : tail ⟨0, hn1⟩ = f ⟨1, h1⟩ := by simp [tail]
    rw [← htail0] at hf1_nz
    exact not_isZero_biproduct_of_component tail ⟨0, hn1⟩ hf1_nz
  -- Contradiction: hdecomp says one is zero, but both are nonzero
  rcases h_decomp with hZ_head | hZ_tail
  · exact h_head_nz hZ_head
  · exact h_tail_nz hZ_tail

/-- **Krull-Schmidt Uniqueness**: Any two indecomposable decompositions of a finite
length object are equivalent up to permutation and isomorphism.

The proof uses:
1. Base case: If d₁.n = 0, then X is zero, so d₂.n = 0 as well
2. Single component case: If d₁.n = 1, then X is indecomposable, so d₂.n = 1
3. Inductive case: By exchange lemma, d₁.components 0 ≅ d₂.components j for some j
   Then apply cancellation and induction on the remainders
-/
theorem krullSchmidt_uniqueness {X : C} (hX : IsFiniteLengthObject X)
    (d₁ d₂ : IndecomposableDecomposition C X) : DecompositionsEquivalent C d₁ d₂ := by
  -- Case split on d₁.n
  rcases Nat.eq_zero_or_pos d₁.n with hn | hn_pos
  · -- Base case: d₁.n = 0, so X is zero (biproduct over empty index is zero)
    have hBiprod_zero : IsZero (⨁ d₁.components) := by
      have hemp : IsEmpty (Fin d₁.n) := by rw [hn]; exact Fin.isEmpty
      haveI := hemp
      constructor
      · intro Y
        exact ⟨{ default := biproduct.desc (fun i => IsEmpty.elim hemp i)
                 uniq := fun f => by ext j; exact IsEmpty.elim hemp j }⟩
      · intro Y
        exact ⟨{ default := biproduct.lift (fun i => IsEmpty.elim hemp i)
                 uniq := fun f => by ext j; exact IsEmpty.elim hemp j }⟩
    have hXzero : IsZero X := hBiprod_zero.of_iso d₁.iso
    have hd2_n_eq : d₂.n = 0 := eq_zero_of_isZero_indecomposable_decomposition
      d₂.components d₂.indecomposable X hXzero d₂.iso
    refine ⟨by omega, Equiv.refl _, ?_⟩
    intro i
    have : i.val < 0 := by rw [← hn]; exact i.isLt
    exact (Nat.not_lt_zero i.val this).elim
  · -- d₁.n > 0
    have hYfl : ∀ i, IsFiniteLengthObject (d₁.components i) :=
      fun i => isFiniteLengthObject_of_biproduct_iso d₁.components d₁.iso hX i
    have hZfl : ∀ j, IsFiniteLengthObject (d₂.components j) :=
      fun j => isFiniteLengthObject_of_biproduct_iso d₂.components d₂.iso hX j
    obtain ⟨j, ⟨f⟩⟩ := exchangeLemma hn_pos d₁.components d₂.components
      d₁.indecomposable d₂.indecomposable hYfl hZfl d₁.iso d₂.iso
    -- f : d₁.components ⟨0, hn_pos⟩ ≅ d₂.components j
    -- Case split: d₁.n = 1 or d₁.n > 1
    by_cases hn1 : d₁.n = 1
    · -- Single component case: d₁.n = 1
      -- X ≅ d₁.components 0 (single indecomposable), so X is indecomposable
      -- Hence d₂.n = 1 (otherwise X ≅ ⨁ d₂.components with >1 components is decomposable)
      have hd2_n : d₂.n = 1 := by
        by_contra hd2_ne1
        have hd2_pos : 0 < d₂.n := Fin.pos j
        have hd2_gt1 : 1 < d₂.n := Nat.lt_of_le_of_ne
          (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd2_pos)) (Ne.symm hd2_ne1)
        -- The iso: d₁.components 0 ≅ ⨁ d₁.components ≅ X ≅ ⨁ d₂.components
        have iso_chain : d₁.components ⟨0, hn_pos⟩ ≅ ⨁ d₂.components :=
          (biproductSingletonIso' hn1 d₁.components).symm ≪≫ d₁.iso.symm ≪≫ d₂.iso
        exact not_indecomposable_of_biproduct_gt_one d₂.components hd2_gt1 d₂.indecomposable
          (indecomposable_of_iso_indecomposable (d₁.indecomposable ⟨0, hn_pos⟩) iso_chain)
      -- Now d₁.n = 1 and d₂.n = 1
      refine ⟨by omega, Equiv.refl _, ?_⟩
      intro i
      -- i : Fin d₁.n with d₁.n = 1, so i = ⟨0, _⟩
      -- j : Fin d₂.n with d₂.n = 1, so j = ⟨0, _⟩
      -- Both indices reduce to 0, and f gives the iso
      have hi0 : i.val = 0 := by omega
      have hj0 : j.val = 0 := by omega
      -- The goal involves (Equiv.refl _) i which equals i
      -- σ i = i, and we need d₁.components i ≅ d₂.components ⟨σ i, _⟩
      -- Since σ = refl, this is d₁.components i ≅ d₂.components ⟨i.val, _⟩
      -- Since i.val = 0, it's d₁.components ⟨0, _⟩ ≅ d₂.components ⟨0, _⟩
      -- f : d₁.components ⟨0, hn_pos⟩ ≅ d₂.components j where j.val = 0
      have heqi : i = ⟨0, hn_pos⟩ := Fin.ext hi0
      have heqj : j = ⟨0, by omega⟩ := Fin.ext hj0
      rw [heqi]
      -- Goal: Nonempty (d₁.components ⟨0, hn_pos⟩ ≅ d₂.components ⟨_, _⟩)
      simp only [Equiv.refl_apply]
      -- Now goal is: Nonempty (d₁.components ⟨0, hn_pos⟩ ≅ d₂.components ⟨0, _⟩)
      -- Use f after substituting j = ⟨0, _⟩
      exact ⟨f ≪≫ eqToIso (by rw [heqj])⟩
    · -- Inductive case: d₁.n > 1
      -- The full proof requires strong induction on n + biproduct cancellation.
      -- Key steps:
      -- 1. Show d₁.n = d₂.n (both have same size since X is fixed)
      -- 2. Show d₂.n > 1 (else X is indecomposable, contradicting d₁.n > 1)
      -- 3. Use biproduct cancellation: Y₀ ⊞ rest₁ ≅ Z_j ⊞ rest₂ with Y₀ ≅ Z_j implies rest₁ ≅ rest₂
      -- 4. Apply IH on the (n-1)-component remainders
      -- 5. Construct σ from j and the permutation from IH

      have hn_gt1 : 1 < d₁.n := Nat.lt_of_le_of_ne
        (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hn_pos)) (Ne.symm hn1)

      have hd2_pos : 0 < d₂.n := Fin.pos j

      -- d₂.n > 1: if d₂.n = 1, then X is indecomposable, contradicting d₁.n > 1
      have hd2_gt1 : 1 < d₂.n := by
        by_contra hd2_le1
        have hd2_eq1 : d₂.n = 1 := Nat.eq_of_le_of_lt_succ
          (Nat.one_le_iff_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hd2_pos))
          (Nat.lt_succ_of_le (Nat.not_lt.mp hd2_le1))
        have iso_X_single : X ≅ d₂.components ⟨0, by omega⟩ :=
          d₂.iso ≪≫ biproductSingletonIso' hd2_eq1 d₂.components
        have hX_indec : Indecomposable X :=
          indecomposable_of_iso_indecomposable (d₂.indecomposable ⟨0, by omega⟩) iso_X_single.symm
        exact not_indecomposable_of_biproduct_gt_one d₁.components hn_gt1 d₁.indecomposable
          (indecomposable_of_iso_indecomposable hX_indec d₁.iso)

      -- Step 1: Build head-tail split for d₁
      -- ⨁ d₁.components ≅ d₁.components 0 ⊞ ⨁ (finTail hn_pos d₁.components)
      let iso_d1_split : ⨁ d₁.components ≅
          d₁.components ⟨0, hn_pos⟩ ⊞ ⨁ (finTail hn_pos d₁.components) :=
        biproductHeadTailIso hn_pos d₁.components

      -- Step 2: Swap j to front for d₂, then head-tail split
      -- ⨁ d₂.components ≅ ⨁ (swapped) ≅ d₂.components j ⊞ ⨁ (rest)
      let d2_swapped := d₂.components ∘ (finSwapFront j).symm
      let iso_d2_swap : ⨁ d₂.components ≅ ⨁ d2_swapped := biproductSwapFrontIso d₂.components j
      have hd2_swapped_0 : d2_swapped ⟨0, hd2_pos⟩ = d₂.components j := biproductSwapFront_zero _ j
      let iso_d2_split : ⨁ d2_swapped ≅
          d2_swapped ⟨0, hd2_pos⟩ ⊞ ⨁ (finTail hd2_pos d2_swapped) :=
        biproductHeadTailIso hd2_pos d2_swapped

      -- Step 3: Full iso from d₁.components 0 ⊞ rest₁ to d₂.components j ⊞ rest₂
      -- Compose: X → ⨁ d₁ → head ⊞ tail₁ and X → ⨁ d₂ → swap → head ⊞ tail₂
      let iso_full : (d₁.components ⟨0, hn_pos⟩ ⊞ ⨁ (finTail hn_pos d₁.components)) ≅
          (d2_swapped ⟨0, hd2_pos⟩ ⊞ ⨁ (finTail hd2_pos d2_swapped)) :=
        iso_d1_split.symm ≪≫ d₁.iso.symm ≪≫ d₂.iso ≪≫ iso_d2_swap ≪≫ iso_d2_split

      -- Step 4: The (1,1) component of iso_full should be related to f
      -- To apply Biprod.isoElim, we need: IsIso (biprod.inl ≫ iso_full.hom ≫ biprod.fst)
      -- This equals the projection Y₀ → X → Z_j, which is f up to coercion
      --
      -- The remaining work requires:
      -- a) Prove the (1,1) component equals f (the exchange lemma iso)
      -- b) Apply Biprod.isoElim to get remainder iso
      -- c) Build IndecomposableDecomposition for remainders (n-1 components each)
      -- d) Apply strong induction hypothesis
      -- e) Combine permutations
      --
      -- This requires restructuring the proof to use Nat.strong_induction_on.
      -- Tracked in: lemmafeld-cn3q (cancellation), lemmafeld-vxyi (this sorry)
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
