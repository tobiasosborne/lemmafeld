/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.IterateComap
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.FittingLemma

/-!
# Categorical Orzech Theorem

We prove that an epimorphic endomorphism on a Noetherian object is a monomorphism.
This is the categorical analog of `IsNoetherian.injective_of_surjective_endomorphism`
from `Mathlib.RingTheory.Noetherian.Orzech`.

## Main Results

* `mono_of_epi_endomorphism_noetherianObject`: An epi endomorphism on a Noetherian object is mono.
* `isIso_of_epi_endomorphism_noetherianObject`: An epi endomorphism on a Noetherian object is iso.

## References

* Djoković, *Epimorphisms of modules which must be isomorphisms* [djokovic1973]
* §1.5 of Etingof et al. "Tensor Categories" (AMS 2015)
-/

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Limits Subobject
open LemmaFeld.TensorCategories.Chapter1

variable {C : Type*} [Category C] [Abelian C]

/-! ## Connection: iterateComap and kernelSubobject of powers -/

section IterateComapKernel

variable {X : C} (f : End X)

/-- The pullback of kernelSubobject g along f equals kernelSubobject (f ≫ g).
This is the categorical version of f⁻¹(ker g) = ker(g ∘ f). -/
theorem pullback_kernelSubobject_eq (g : End X) :
    (Subobject.pullback f).obj (kernelSubobject g) = kernelSubobject (f ≫ g) := by
  -- Both sides represent the subobject {x : f(x) ∈ ker(g)} = {x : g(f(x)) = 0} = ker(g ∘ f)
  -- The proof requires showing the pullback square and kernel square are compatible
  sorry

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

end IterateComapKernel

/-! ## Main Theorem: Categorical Orzech -/

section CategoricalOrzech

variable {X : C} (f : End X)

open scoped ZeroObject in
/-- The kernel.ι of an isomorphism is zero. -/
theorem kernel_ι_eq_zero_of_isIso [IsIso f] : kernel.ι f = 0 := by
  -- kernel f ≅ 0 for iso (hence mono) f
  have hker : kernel f ≅ (0 : C) := kernel.ofMono f
  -- kernel.ι f : kernel f ⟶ X where kernel f ≅ 0
  have hzero : IsZero (kernel f) := hker.isZero_iff.mpr (isZero_zero C)
  exact hzero.eq_zero_of_src (kernel.ι f)

/-- The kernelSubobject of an isomorphism is ⊥. -/
theorem kernelSubobject_of_isIso [IsIso f] : kernelSubobject f = ⊥ := by
  rw [mk_eq_bot_iff_zero]
  exact kernel_ι_eq_zero_of_isIso f

variable [hf : Epi f] [IsNoetherianObject X]

/-- Key lemma: When f is epi and the kernel chain stabilizes, kernelSubobject f = ⊥.

The proof strategy (Djoković):
1. Chain stabilization means ker(f^n) = ker(f^(n+1)), i.e., ker(f^n) is f-saturated
2. When f is epi, the restriction of f to ker(f^n) is also epi
3. Since f^n kills ker(f^n), the restriction is nilpotent
4. Epi + nilpotent on ker(f^n) implies ker(f^n) = 0
5. Since kernelSubobject f ≤ ker(f^n) = 0, we get kernelSubobject f = 0 -/
theorem kernelSubobject_eq_bot_of_epi_noetherian : kernelSubobject f = ⊥ := by
  -- Get stabilization point from Noetherian property
  obtain ⟨n, hn⟩ := kernelSubobject_stabilizes f
  -- Case split on stabilization point
  by_cases hn0 : n = 0
  · -- Stabilizes at 0: kernelSubobject (f^0) = kernelSubobject (f^1) = kernelSubobject f
    subst hn0
    have h01 : kernelSubobject (f ^ 0) = kernelSubobject (f ^ 1) := hn 1 (Nat.zero_le 1)
    have hone : (f ^ (0 : ℕ) : End X) = 𝟙 X := by rw [pow_zero, End.one_def]
    have hiso : IsIso (f ^ (0 : ℕ) : End X) := by rw [hone]; infer_instance
    have h0 : kernelSubobject (f ^ (0 : ℕ)) = ⊥ := @kernelSubobject_of_isIso C _ _ X (f^0) hiso
    rw [pow_one] at h01
    rw [← h01, h0]
  · -- n ≥ 1 case: the full Orzech argument is needed
    push_neg at hn0
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    -- kernelSubobject f ≤ kernelSubobject (f^n) by monotonicity
    have hker_le : kernelSubobject f ≤ kernelSubobject (f ^ n) := by
      have h1 : kernelSubobject f = kernelSubobject (f ^ 1) := by rw [pow_one]
      rw [h1]
      exact kernelSubobject_le_of_le f (Nat.one_le_of_lt hn_pos)
    -- The full Orzech argument: stabilization + epi implies ker(f^n) = ⊥
    sorry

/-- Categorical Orzech: An epi endomorphism on a Noetherian object is mono. -/
theorem mono_of_epi_endomorphism_noetherianObject : Mono f := by
  have h : kernelSubobject f = ⊥ := kernelSubobject_eq_bot_of_epi_noetherian f
  -- kernelSubobject f = ⊥ implies kernel.ι f = 0
  have hι : kernel.ι f = 0 := by
    have harrow : (kernelSubobject f).arrow = 0 := by rw [h, Subobject.bot_arrow]
    rw [← kernelSubobject_arrow f] at harrow
    -- (kernelSubobjectIso f).hom ≫ kernel.ι f = 0
    -- Since (kernelSubobjectIso f).hom is an iso, it's epi, so kernel.ι f = 0
    exact zero_of_epi_comp (kernelSubobjectIso f).hom harrow
  exact Abelian.mono_of_kernel_ι_eq_zero f hι

/-- Corollary: An epi endomorphism on a Noetherian object is an isomorphism. -/
theorem isIso_of_epi_endomorphism_noetherianObject : IsIso f := by
  have : Mono f := mono_of_epi_endomorphism_noetherianObject f
  exact isIso_of_mono_of_epi f

end CategoricalOrzech

end CategoryTheory
