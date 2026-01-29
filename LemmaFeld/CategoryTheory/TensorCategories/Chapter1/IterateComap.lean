/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Subobject.NoetherianObject
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.CommSq
import Mathlib.Order.OrderIsoNat

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

open scoped ZeroObject

/-- The kernel square is a pullback: kernel f is the pullback of 0 : 0 → X along f.
This is the key fact relating pullbacks to kernels in abelian categories. -/
theorem isPullback_kernel_zero :
    IsPullback (0 : kernel f ⟶ (0 : C)) (kernel.ι f) (0 : (0 : C) ⟶ X) f := by
  refine IsPullback.of_isLimit (c := PullbackCone.mk (0 : kernel f ⟶ (0 : C)) (kernel.ι f) ?_) ?_
  · simp
  · refine PullbackCone.isLimitAux' _ ?_
    intro s
    have hs : s.snd ≫ f = 0 := by
      have := s.condition
      simp at this
      exact this.symm
    refine ⟨kernel.lift f s.snd hs, ?_, ?_, ?_⟩
    · apply Subsingleton.elim
    · simp [kernel.lift_ι]
    · intro m _ hsnd
      apply equalizer.hom_ext
      simp only [kernel.lift_ι]
      convert hsnd using 1

/-- The pullback of ⊥ along f equals the kernel subobject of f.
This is because ⊥ : Subobject X represents the zero subobject, and pulling back
0 : 0 → X along f : X → X gives the kernel of f.

Note: This corrects the earlier incorrect claim that pullback of ⊥ is ⊥. -/
theorem pullback_bot_eq_kernelSubobject :
    (pullback f).obj (⊥ : Subobject X) = kernelSubobject f := by
  have h := pullback_obj_mk (isPullback_kernel_zero f)
  rw [kernelSubobject]
  rw [← h]
  congr 1
  exact bot_eq_zero (B := X)

/-- The iterateComap chain starting from ⊥ gives the kernel subobject chain.
- iterateComap f ⊥ 0 = ⊥
- iterateComap f ⊥ 1 = kernelSubobject f
- iterateComap f ⊥ (n+1) = kernelSubobject (f^(n+1)) (conceptually)

This is the categorical analog of how iterateMapComap with i = id and K = ⊥
gives the kernel chain in the module case. -/
theorem iterateComap_bot_succ (n : ℕ) :
    iterateComap f (⊥ : Subobject X) (n + 1) = (pullback f).obj (iterateComap f ⊥ n) :=
  iterateComap_succ f ⊥ n

/-- At step 1, iterateComap f ⊥ gives the kernel subobject. -/
theorem iterateComap_bot_one :
    iterateComap f (⊥ : Subobject X) 1 = kernelSubobject f := by
  simp only [iterateComap_succ, iterateComap_zero, pullback_bot_eq_kernelSubobject]

/-- The chain starting from ⊥ is always monotone (since ⊥ is minimal). -/
theorem iterateComap_bot_mono : Monotone (fun n => iterateComap f (⊥ : Subobject X) n) :=
  iterateComap_mono f ⊥ bot_le

end AbelianConnection

/-! ## Stabilization for Noetherian Objects

For a Noetherian object X (meaning WellFoundedGT on Subobject X, i.e., the ascending
chain condition holds), any monotone chain of subobjects stabilizes.

This applies to the `iterateComap f ⊥` chain, giving the categorical analog of the
kernel chain stabilization used in the Orzech theorem.
-/

section Noetherian

variable [Abelian C] {X : C} (f : X ⟶ X) [IsNoetherianObject X]

/-- For a monotone chain of subobjects of a Noetherian object, there exists n
such that the chain is constant from n onwards. -/
theorem iterateComap_stabilizes (K : Subobject X) (hK : K ≤ (pullback f).obj K) :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → iterateComap f K n = iterateComap f K m := by
  -- The chain is monotone by iterateComap_mono
  have hmon : Monotone (fun n => iterateComap f K n) := iterateComap_mono f K hK
  -- For Noetherian objects, WellFoundedGT holds on Subobject X
  -- So monotone chains stabilize
  have := WellFoundedGT.monotone_chain_condition ⟨fun n => iterateComap f K n, hmon⟩
  exact this

/-- The iterateComap chain starting from ⊥ stabilizes for Noetherian objects.
This is the key stabilization result used for the categorical Orzech theorem.

Since ⊥ ≤ (pullback f).obj ⊥ always holds (⊥ is minimal), the monotonicity
condition is automatically satisfied. -/
theorem iterateComap_bot_stabilizes :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → iterateComap f (⊥ : Subobject X) n = iterateComap f ⊥ m := by
  exact iterateComap_stabilizes f ⊥ bot_le

end Noetherian

end CategoryTheory.Subobject
