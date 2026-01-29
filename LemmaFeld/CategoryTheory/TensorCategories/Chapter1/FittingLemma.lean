/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.RingTheory.Nilpotent.Defs
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.FiniteLength

/-!
# Fitting's Lemma

This file contains Fitting's Lemma for abelian categories, a key ingredient in the
proof of the Krull-Schmidt theorem (Theorem 1.5.7).

## Mathematical Context

**Fitting's Lemma**: For an indecomposable object X of finite length, any
endomorphism f : X → X is either nilpotent or an isomorphism.

The proof relies on:
1. The kernel chain Ker(f) ⊆ Ker(f²) ⊆ ... is ascending and stabilizes (Noetherian)
2. The image chain Im(f) ⊇ Im(f²) ⊇ ... is descending and stabilizes (Artinian)
3. At stabilization n: X = Ker(f^n) ⊕ Im(f^n)
4. Indecomposability forces one summand to be zero

## References

- Etingof et al. "Tensor Categories" (AMS 2015), §1.5
- Fitting "Die Theorie der Automorphismenringe Abelscher Gruppen" (1934)
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

/-! ## Chain Stabilization Lemmas

These lemmas establish the monotonicity of kernel and image chains for powers
of an endomorphism. Together with the Noetherian/Artinian properties of finite
length objects, they guarantee chain stabilization.
-/

section ChainStabilization

variable {C : Type*} [Category C] [Abelian C]
variable {X : C} (f : End X)

/-- Powers of an endomorphism can be composed in either order. -/
lemma pow_comp_comm (m k : ℕ) : (f ^ m) ≫ (f ^ k) = (f ^ k) ≫ (f ^ m) := by
  rw [← End.mul_def, ← End.mul_def, pow_mul_comm]

/-- f^(m+k) = f^m ≫ f^k (useful form for kernel chain proofs). -/
lemma pow_add_eq_comp (m k : ℕ) : f ^ (m + k) = (f ^ m) ≫ (f ^ k) := by
  rw [pow_add, End.mul_def, pow_comp_comm]

/-- Alternative form: f^(m+k) = f^k ≫ f^m (useful for image chains). -/
lemma pow_add_eq_comp' (m k : ℕ) : f ^ (m + k) = (f ^ k) ≫ (f ^ m) := by
  rw [pow_add, End.mul_def]

/-- The kernel chain Ker(f) ≤ Ker(f²) ≤ ... is monotone (ascending). -/
lemma kernelSubobject_le_of_le {m n : ℕ} (h : m ≤ n) :
    kernelSubobject (f ^ m) ≤ kernelSubobject (f ^ n) := by
  apply Subobject.mk_le_mk_of_comm (kernel.lift (f ^ n) (kernel.ι (f ^ m)) ?_)
  · exact kernel.lift_ι _ _ _
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [pow_add_eq_comp, ← Category.assoc, kernel.condition, zero_comp]

/-- The kernel chain is monotone. -/
lemma kernelSubobject_mono : Monotone (fun n => kernelSubobject (f ^ n)) :=
  fun _ _ h => kernelSubobject_le_of_le f h

/-- Im(f^n) ≤ Im(f^m) when m ≤ n. -/
lemma imageSubobject_le_of_ge {m n : ℕ} (h : m ≤ n) :
    imageSubobject (f ^ n) ≤ imageSubobject (f ^ m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add_eq_comp']
  exact imageSubobject_comp_le (f ^ k) (f ^ m)

/-- The image chain is antitone. -/
lemma imageSubobject_antitone : Antitone (fun n => imageSubobject (f ^ n)) :=
  fun _ _ h => imageSubobject_le_of_ge f h

end ChainStabilization

/-! ## Fitting's Lemma -/

section FittingLemma

variable {C : Type*} [Category C] [Abelian C] [HasFiniteBiproducts C]
variable {X : C}

/-- **Fitting's Lemma**: For an indecomposable object X of finite length,
any endomorphism f : X → X is either nilpotent or an isomorphism.

The proof uses chain stabilization: since X has finite length, both the kernel
chain and image chain stabilize. At stabilization n, X decomposes as
Ker(f^n) ⊕ Im(f^n). Indecomposability forces one summand to be zero:
- If Ker(f^n) = X then f^n = 0 (nilpotent)
- If Im(f^n) = X then f^n is an isomorphism, hence f is an isomorphism -/
theorem fitting_lemma (f : End X) (hX : Indecomposable X) (hfl : IsFiniteLengthObject X) :
    IsNilpotent f ∨ IsUnit f := by
  -- The full proof requires showing the decomposition X = Ker(f^n) ⊕ Im(f^n)
  -- at chain stabilization. This needs the following steps:
  -- 1. By Noetherian property, ∃ n such that Ker(f^n) = Ker(f^(n+1)) = ...
  -- 2. By Artinian property, ∃ m such that Im(f^m) = Im(f^(m+1)) = ...
  -- 3. At N = max(n,m): f^N|_{Im(f^N)} : Im(f^N) → Im(f^N) is an isomorphism
  -- 4. Hence X = Ker(f^N) ⊕ Im(f^N)
  -- 5. By indecomposability: Ker(f^N) = 0 or Im(f^N) = 0
  sorry

/-- Local ring property for End(X): the non-units form a two-sided ideal.

This is a consequence of Fitting's Lemma: if f and g are non-units (hence nilpotent),
then f + g is also nilpotent (hence non-unit), assuming X is indecomposable of
finite length. -/
def EndomorphismRingIsLocal (X : C) : Prop :=
  ∀ f g : X ⟶ X, IsIso (f + g) → IsIso f ∨ IsIso g

end FittingLemma

end LemmaFeld.TensorCategories.Chapter1
