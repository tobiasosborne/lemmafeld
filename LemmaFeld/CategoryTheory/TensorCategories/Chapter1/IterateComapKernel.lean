/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.IterateComap

/-!
# Connection: iterateComap and kernelSubobject

This file establishes the connection between `iterateComap` (pullback-based iteration)
and `kernelSubobject` of powers of an endomorphism.

## Main Results

* `pullback_kernelSubobject_eq`: The pullback of kernelSubobject g along f equals
  kernelSubobject (f ≫ g). Categorical version of f⁻¹(ker g) = ker(g ∘ f).
* `iterateComap_bot_eq_kernelSubobject_pow`: iterateComap f ⊥ n = kernelSubobject (f ^ n)
  for n ≥ 1.

## References

* §1.5 of Etingof et al. "Tensor Categories" (AMS 2015)
-/

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Limits Subobject
open LemmaFeld.TensorCategories.Chapter1

variable {C : Type*} [Category C] [Abelian C]
variable {X : C} (f : End X)

/-- The pullback of kernelSubobject g along f equals kernelSubobject (f ≫ g).
This is the categorical version of f⁻¹(ker g) = ker(g ∘ f). -/
theorem pullback_kernelSubobject_eq (g : End X) :
    (Subobject.pullback f).obj (kernelSubobject g) = kernelSubobject (f ≫ g) := by
  -- Construct the induced map kernel(f ≫ g) → kernel(g)
  let k : kernel (f ≫ g) ⟶ kernel g :=
    kernel.lift g (kernel.ι (f ≫ g) ≫ f) (by simp [kernel.condition])
  -- Show the square commutes: k ≫ kernel.ι g = kernel.ι (f ≫ g) ≫ f
  have hsq : k ≫ kernel.ι g = kernel.ι (f ≫ g) ≫ f := kernel.lift_ι _ _ _
  -- Build the IsPullback
  have hp : IsPullback k (kernel.ι (f ≫ g)) (kernel.ι g) f := by
    refine IsPullback.of_isLimit (c := PullbackCone.mk k (kernel.ι (f ≫ g)) hsq) ?_
    refine PullbackCone.isLimitAux' _ ?_
    intro s
    -- s.fst : W ⟶ kernel g, s.snd : W ⟶ X
    -- s.condition : s.fst ≫ kernel.ι g = s.snd ≫ f
    -- Need to show s.snd factors through kernel (f ≫ g)
    have hcond : s.snd ≫ (f ≫ g) = 0 := by
      rw [← Category.assoc, ← s.condition, Category.assoc, kernel.condition, comp_zero]
    let ℓ : s.pt ⟶ kernel (f ≫ g) := kernel.lift (f ≫ g) s.snd hcond
    refine ⟨ℓ, ?_, kernel.lift_ι _ _ _, ?_⟩
    -- First: ℓ ≫ k = s.fst (show by composing with kernel.ι g)
    · apply equalizer.hom_ext
      rw [PullbackCone.mk_fst, Category.assoc, hsq, ← Category.assoc, kernel.lift_ι, s.condition]
    -- Second: uniqueness
    · intro m _ hm2
      apply equalizer.hom_ext
      rw [kernel.lift_ι]
      exact hm2
  rw [kernelSubobject, kernelSubobject]
  exact pullback_obj_mk hp

/-- iterateComap f ⊥ n = kernelSubobject (f ^ n) for n ≥ 1.
This connects the pullback-based iterateComap with kernelSubobject of powers. -/
theorem iterateComap_bot_eq_kernelSubobject_pow (n : ℕ) (hn : 0 < n) :
    iterateComap f (⊥ : Subobject X) n = kernelSubobject (f ^ n) := by
  induction n with
  | zero => exact (Nat.not_lt_zero 0 hn).elim
  | succ n ih =>
    cases n with
    | zero =>
      rw [iterateComap_succ, iterateComap_zero]
      rw [pullback_bot_eq_kernelSubobject f]
      congr 1
      exact (pow_one f).symm
    | succ m =>
      rw [iterateComap_succ, ih (Nat.succ_pos m)]
      rw [pow_succ, End.mul_def]
      exact pullback_kernelSubobject_eq f (f ^ (m + 1))

end CategoryTheory
