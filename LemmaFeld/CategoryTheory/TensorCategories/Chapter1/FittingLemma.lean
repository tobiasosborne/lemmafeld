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

Fitting's Lemma for abelian categories: for an indecomposable object X of finite
length, any endomorphism f : X → X is either nilpotent or an isomorphism.

§1.5 of Etingof et al. "Tensor Categories" (AMS 2015)
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

/-- The kernel chain of f stabilizes: there exists n such that Ker(f^m) = Ker(f^n) for all m ≥ n. -/
lemma kernelSubobject_stabilizes [IsNoetherianObject X] :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → kernelSubobject (f ^ n) = kernelSubobject (f ^ m) := by
  have hf : Monotone (fun n => kernelSubobject (f ^ n)) := kernelSubobject_mono f
  exact monotone_chain_condition_of_isNoetherianObject ⟨_, hf⟩

/-- The image chain of f stabilizes: there exists n such that Im(f^m) = Im(f^n) for all m ≥ n. -/
lemma imageSubobject_stabilizes [IsArtinianObject X] :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → imageSubobject (f ^ n) = imageSubobject (f ^ m) := by
  have hf : Antitone (fun n => imageSubobject (f ^ n)) := imageSubobject_antitone f
  -- Antitone in α is monotone in αᵒᵈ
  have hf' : Monotone (fun n => OrderDual.toDual (imageSubobject (f ^ n))) := hf
  obtain ⟨n, hn⟩ := antitone_chain_condition_of_isArtinianObject ⟨_, hf'⟩
  refine ⟨n, fun m hm => ?_⟩
  have heq := hn m hm
  simp only [OrderHom.coe_mk, OrderDual.toDual_inj] at heq
  exact heq

/-- At chain stabilization, the image chain satisfies Im(f^(n+k)) = Im(f^n). -/
lemma imageSubobject_stable [IsArtinianObject X] {n : ℕ}
    (hn : ∀ m : ℕ, n ≤ m → imageSubobject (f ^ n) = imageSubobject (f ^ m)) (k : ℕ) :
    imageSubobject (f ^ (n + k)) = imageSubobject (f ^ n) :=
  (hn (n + k) (Nat.le_add_right n k)).symm

/-- At chain stabilization, the kernel chain satisfies Ker(f^(n+k)) = Ker(f^n). -/
lemma kernelSubobject_stable [IsNoetherianObject X] {n : ℕ}
    (hn : ∀ m : ℕ, n ≤ m → kernelSubobject (f ^ n) = kernelSubobject (f ^ m)) (k : ℕ) :
    kernelSubobject (f ^ (n + k)) = kernelSubobject (f ^ n) :=
  (hn (n + k) (Nat.le_add_right n k)).symm

end ChainStabilization

/-! ## Key Lemmas for Fitting Decomposition

At the stabilization point n, we have the key property:
- Ker(f^n) ∩ Im(f^n) = 0
- Ker(f^n) + Im(f^n) = X

These imply X ≅ Ker(f^n) ⊕ Im(f^n).
-/

section FittingDecomposition

variable {C : Type*} [Category C] [Abelian C]
variable {X : C} (f : End X)

open scoped ZeroObject in
/-- If a subobject's arrow is zero, the subobject equals ⊥. -/
lemma subobject_eq_bot_of_arrow_eq_zero (A : Subobject X) (h : A.arrow = 0) : A = ⊥ := by
  have hiso : Subobject.underlying.obj A ≅ (0 : C) := isoZeroOfMonoEqZero h
  apply Subobject.eq_of_comm (hiso ≪≫ Subobject.botCoeIsoZero.symm)
  simp only [Iso.trans_hom, Subobject.bot_arrow, comp_zero, h]

/-- The intersection of kernel and image, composed with f^n, is zero. -/
lemma inf_arrow_comp_pow_eq_zero {n : ℕ} :
    (kernelSubobject (f ^ n) ⊓ imageSubobject (f ^ n)).arrow ≫ f ^ n = 0 := by
  rw [← Subobject.ofLE_arrow (inf_le_left (a := kernelSubobject (f ^ n)))]
  rw [Category.assoc, kernelSubobject_arrow_comp, comp_zero]

/-- At stabilization, Ker(f^n) ∩ Im(f^n) = 0. Key: f^n|_{Im(f^n)} is iso at stabilization. -/
lemma kernelSubobject_inf_imageSubobject_eq_bot {n : ℕ}
    (hker : ∀ m : ℕ, n ≤ m → kernelSubobject (f ^ n) = kernelSubobject (f ^ m))
    (him : ∀ m : ℕ, n ≤ m → imageSubobject (f ^ n) = imageSubobject (f ^ m)) :
    kernelSubobject (f ^ n) ⊓ imageSubobject (f ^ n) = ⊥ := by
  apply subobject_eq_bot_of_arrow_eq_zero
  -- Need: (K ⊓ I).arrow = 0. Uses both stabilization conditions:
  -- If x ∈ Im(f^n), x = f^n(y). If also f^n(x) = 0, then f^(2n)(y) = 0.
  -- By kernel stabilization, y ∈ Ker(f^n), so x = f^n(y) = 0.
  sorry

/-- At stabilization, Ker(f^n) + Im(f^n) = X. For any x, f^n(x) ∈ Im(f^(2n)) = Im(f^n). -/
lemma kernelSubobject_sup_imageSubobject_eq_top {n : ℕ}
    (hker : ∀ m : ℕ, n ≤ m → kernelSubobject (f ^ n) = kernelSubobject (f ^ m))
    (him : ∀ m : ℕ, n ≤ m → imageSubobject (f ^ n) = imageSubobject (f ^ m)) :
    kernelSubobject (f ^ n) ⊔ imageSubobject (f ^ n) = ⊤ := by
  sorry

end FittingDecomposition

/-! ## Fitting's Lemma -/

section FittingLemma

variable {C : Type*} [Category C] [Abelian C] [HasFiniteBiproducts C]
variable {X : C}

/-- **Fitting's Lemma**: For indecomposable X of finite length, f ∈ End(X) is nilpotent or unit.
At stabilization n, X = Ker(f^n) ⊕ Im(f^n). Indecomposability forces one summand to be 0. -/
theorem fitting_lemma (f : End X) (hX : Indecomposable X) (hfl : IsFiniteLengthObject X) :
    IsNilpotent f ∨ IsUnit f := by
  sorry  -- Requires X = Ker(f^n) ⊕ Im(f^n) decomposition at chain stabilization

/-- Local ring property: non-units form a two-sided ideal. Follows from Fitting's Lemma. -/
def EndomorphismRingIsLocal (X : C) : Prop :=
  ∀ f g : X ⟶ X, IsIso (f + g) → IsIso f ∨ IsIso g

end FittingLemma

end LemmaFeld.TensorCategories.Chapter1
