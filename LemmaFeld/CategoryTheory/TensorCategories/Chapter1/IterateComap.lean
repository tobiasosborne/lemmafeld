/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Abelian.Basic

/-!
# Iterate Comap for Subobjects

Categorical analog of `LinearMap.iterateMapComap` from
`Mathlib.Algebra.Module.Submodule.IterateMapComap`.

For an endomorphism `f : X ⟶ X` and subobject `K : Subobject X`, we define
`Subobject.iterateComap f K n` as the nth iterate of pulling back along `f`.

This is used for establishing that an epi endomorphism on a Noetherian object
is mono (the categorical Orzech theorem), which is needed for Fitting's Lemma.

§1.5 of Etingof et al. "Tensor Categories" (AMS 2015)

## References

- Djoković, *Epimorphisms of modules which must be isomorphisms* [djokovic1973]
- `Mathlib.Algebra.Module.Submodule.IterateMapComap`
- `Mathlib.RingTheory.Noetherian.Orzech`
-/

noncomputable section

namespace CategoryTheory.Subobject

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category C] [HasPullbacks C]

/-! ## Definition of iterateComap -/

/-- For an endomorphism `f : X ⟶ X` and subobject `K : Subobject X`,
`iterateComap f K n` is the nth iterate of `(Subobject.pullback f).obj`.

This gives the chain:
- `iterateComap f K 0 = K`
- `iterateComap f K 1 = (pullback f).obj K` (preimage of K)
- `iterateComap f K 2 = (pullback f).obj ((pullback f).obj K)`
- etc.

This is the categorical analog of `LinearMap.iterateMapComap f id n K`. -/
def iterateComap {X : C} (f : X ⟶ X) (K : Subobject X) (n : ℕ) : Subobject X :=
  ((pullback f).obj)^[n] K

/-! ## Basic Properties -/

variable {X : C} (f : X ⟶ X) (K : Subobject X)

/-- At n = 0, iterateComap returns K unchanged. -/
@[simp]
theorem iterateComap_zero : iterateComap f K 0 = K := rfl

/-- iterateComap at n+1 is pullback applied to iterateComap at n. -/
@[simp]
theorem iterateComap_succ (n : ℕ) :
    iterateComap f K (n + 1) = (pullback f).obj (iterateComap f K n) :=
  Function.iterate_succ_apply' _ n K

/-- iterateComap at n+1 can also be expressed as applying pullback first. -/
theorem iterateComap_succ' (n : ℕ) :
    iterateComap f K (n + 1) = iterateComap f ((pullback f).obj K) n :=
  Function.iterate_succ_apply _ n K

/-- The pullback functor preserves the ordering of subobjects. -/
theorem pullback_monotone (A B : Subobject X) (h : A ≤ B) :
    (pullback f).obj A ≤ (pullback f).obj B :=
  (pullback f).monotone h

/-- If A ≤ B, then iterateComap f A n ≤ iterateComap f B n for all n. -/
theorem iterateComap_mono_of_le {A B : Subobject X} (h : A ≤ B) (n : ℕ) :
    iterateComap f A n ≤ iterateComap f B n := by
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [iterateComap_succ]
    exact (pullback f).monotone ih

/-! ## Key Lemma: Monotonicity of the Chain

For the Orzech theorem, we need the chain `iterateComap f K n` to be monotone
(non-decreasing) under certain conditions. The module proof uses:
- `K.map f ≤ K.map i` (or equivalently `K.map f ≤ K` when i = id)

Categorically, this translates to a condition involving the map/exists adjoint.
-/

section MonotoneChain

/-- When K is contained in its own preimage under f, the iterateComap chain is non-decreasing.
The condition `K ≤ (pullback f).obj K` is the categorical analog of `K.map f ≤ K.map id = K`. -/
theorem iterateComap_mono_of_le_pullback (hK : K ≤ (pullback f).obj K) (n : ℕ) :
    iterateComap f K n ≤ iterateComap f K (n + 1) := by
  induction n with
  | zero => exact hK
  | succ n ih =>
    -- iterateComap f K (n+1) = (pullback f).obj (iterateComap f K n)
    -- iterateComap f K (n+2) = (pullback f).obj (iterateComap f K (n+1))
    -- ih : iterateComap f K n ≤ iterateComap f K (n+1)
    -- Goal: iterateComap f K (n+1) ≤ iterateComap f K (n+2)
    rw [iterateComap_succ, iterateComap_succ]
    exact (pullback f).monotone ih

/-- The chain `iterateComap f K n` is monotone when K ≤ pullback(f)(K). -/
theorem iterateComap_mono (hK : K ≤ (pullback f).obj K) :
    Monotone (fun n => iterateComap f K n) := by
  intro m n hmn
  induction hmn with
  | refl => rfl
  | step _ ih => exact le_trans ih (iterateComap_mono_of_le_pullback f K hK _)

end MonotoneChain

/-! ## Connection to Kernel Subobject

For an abelian category with endomorphism f : X ⟶ X, the kernel subobject
`kernelSubobject f` is the preimage of 0 ∈ Subobject X along f.

The chain `iterateComap f ⊥ n` gives ⊥, pullback(f)(⊥), pullback(f)²(⊥), ...
which corresponds to kernels when we identify ⊥ with the zero subobject.
-/

section AbelianConnection

variable [Abelian C]

/-- The pullback of ⊥ along any morphism is ⊥.
This follows from: the pullback of the zero morphism from initial gives initial.
TODO: Complete proof using IsInitial lemmas. -/
theorem pullback_bot : (pullback f).obj (⊥ : Subobject X) = ⊥ := by
  rw [pullback_obj, mk_eq_bot_iff_zero, bot_arrow]
  -- pullback.snd 0 f = 0 because pullback of 0 from initial is initial
  -- The underlying object ((⊥ : Subobject X) : C) ≅ 0 is initial
  -- Pulling back along any morphism f preserves initiality
  apply zero_of_source_iso_zero
  -- pullback 0 f ≅ 0 : use IsPullback.of_isInitial and uniqueness
  sorry

/-- iterateComap f ⊥ n = ⊥ for all n.
The preimage chain starting from 0 stays at 0. -/
@[simp]
theorem iterateComap_bot (n : ℕ) : iterateComap f (⊥ : Subobject X) n = ⊥ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [iterateComap_succ, ih, pullback_bot]

end AbelianConnection

end CategoryTheory.Subobject
