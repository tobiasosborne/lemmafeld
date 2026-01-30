/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Subobject.NoetherianObject
import Mathlib.CategoryTheory.Subobject.ArtinianObject

/-!
# Chain Stabilization for Endomorphism Powers

These lemmas establish the monotonicity of kernel and image chains for powers
of an endomorphism. Together with the Noetherian/Artinian properties of finite
length objects, they guarantee chain stabilization.

§1.5 of Etingof et al. "Tensor Categories" (AMS 2015)
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

/-! ## Chain Stabilization Lemmas -/

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

end LemmaFeld.TensorCategories.Chapter1
