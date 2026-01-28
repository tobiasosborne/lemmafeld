/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Project
-/
import LemmaFeld.Analysis.OperatorAlgebras.GNS.NullSpace.Quotient
import LemmaFeld.Analysis.OperatorAlgebras.GNS.State.CauchySchwarzTight

/-!
# GNS Inner Product

This file defines the inner product on the quotient A/N_φ.

## Main definitions

* `State.gnsInner` - Inner product ⟨[a], [b]⟩ = φ(b*a) on the quotient

## Main results

* `State.gnsInner_mk` - gnsInner φ (mk a) (mk b) = φ (star b * a)
* `State.gnsInner_conj_symm` - gnsInner φ y x = conj (gnsInner φ x y)
* `State.gnsInner_add_left` - Linearity in first argument
* `State.gnsInner_smul_left` - Sesquilinearity
-/

namespace State

variable {A : Type*} [CStarAlgebra A] (φ : State A)

/-! ### Well-definedness lemmas -/

/-- If a₁ - a₂ ∈ N_φ, then φ(star b * a₁) = φ(star b * a₂). -/
theorem sesqForm_eq_of_sub_mem_gnsNullIdeal_left {a₁ a₂ : A}
    (ha : a₁ - a₂ ∈ φ.gnsNullIdeal) (b : A) :
    φ (star b * a₁) = φ (star b * a₂) := by
  have h_null : φ (star (a₁ - a₂) * (a₁ - a₂)) = 0 := ha
  have h_zero : φ (star b * (a₁ - a₂)) = 0 :=
    apply_star_mul_eq_zero_of_apply_star_self_eq_zero φ h_null b
  have h1 : φ (star b * a₁) - φ (star b * a₂) = φ (star b * (a₁ - a₂)) := by
    rw [mul_sub, ← φ.map_sub]
  rw [← sub_eq_zero, h1, h_zero]

/-- If b₁ - b₂ ∈ N_φ, then φ(star b₁ * a) = φ(star b₂ * a). -/
theorem sesqForm_eq_of_sub_mem_gnsNullIdeal_right {b₁ b₂ : A}
    (hb : b₁ - b₂ ∈ φ.gnsNullIdeal) (a : A) :
    φ (star b₁ * a) = φ (star b₂ * a) := by
  have h_null : φ (star (b₁ - b₂) * (b₁ - b₂)) = 0 := hb
  have h_left : φ (star a * (b₁ - b₂)) = 0 :=
    apply_star_mul_eq_zero_of_apply_star_self_eq_zero φ h_null a
  have h_right : φ (star (b₁ - b₂) * a) = 0 := by
    have h_symm := sesqForm_conj_symm φ a (b₁ - b₂)
    unfold sesqForm at h_symm
    simp only [h_left, starRingEnd_apply, star_zero] at h_symm
    exact h_symm
  have h1 : φ (star b₁ * a) - φ (star b₂ * a) = φ (star (b₁ - b₂) * a) := by
    rw [star_sub, sub_mul, ← φ.map_sub]
  rw [← sub_eq_zero, h1, h_right]

/-- Combined well-definedness: the sesquilinear form descends to the quotient. -/
theorem sesqForm_eq_of_sub_mem_gnsNullIdeal {a₁ a₂ b₁ b₂ : A}
    (ha : a₁ - a₂ ∈ φ.gnsNullIdeal) (hb : b₁ - b₂ ∈ φ.gnsNullIdeal) :
    φ (star b₁ * a₁) = φ (star b₂ * a₂) :=
  calc φ (star b₁ * a₁) = φ (star b₁ * a₂) := sesqForm_eq_of_sub_mem_gnsNullIdeal_left φ ha b₁
    _ = φ (star b₂ * a₂) := sesqForm_eq_of_sub_mem_gnsNullIdeal_right φ hb a₂

/-! ### The inner product definition -/

/-- Helper: convert from quotient relation to submodule membership. -/
private theorem quotient_rel_to_mem {a b : A} (h : φ.gnsNullIdeal.quotientRel a b) :
    a - b ∈ φ.gnsNullIdeal := by
  have h1 : -a + b ∈ φ.gnsNullIdeal := QuotientAddGroup.leftRel_apply.mp h
  have h2 : b - a ∈ φ.gnsNullIdeal := by
    convert h1 using 1
    abel
  simpa only [neg_sub] using φ.gnsNullIdeal.neg_mem h2

/-- The inner product on the GNS quotient: ⟨[a], [b]⟩ = φ(b*a). -/
def gnsInner : φ.gnsQuotient → φ.gnsQuotient → ℂ := fun x y =>
  Quotient.liftOn₂ x y (fun a b => φ (star b * a)) <| by
    intro a₁ a₂ b₁ b₂ ha hb
    exact sesqForm_eq_of_sub_mem_gnsNullIdeal φ
      (quotient_rel_to_mem φ ha) (quotient_rel_to_mem φ hb)

/-- The inner product on representatives. -/
@[simp]
theorem gnsInner_mk (a b : A) :
    φ.gnsInner (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = φ (star b * a) := rfl

/-! ### Inner product properties -/

/-- Conjugate symmetry: ⟨x, y⟩ = conj(⟨y, x⟩). -/
theorem gnsInner_conj_symm (x y : φ.gnsQuotient) :
    φ.gnsInner x y = starRingEnd ℂ (φ.gnsInner y x) := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal y
  simp only [gnsInner_mk]
  exact sesqForm_conj_symm φ _ _

/-- Linearity in the first argument: ⟨x + y, z⟩ = ⟨x, z⟩ + ⟨y, z⟩. -/
theorem gnsInner_add_left (x y z : φ.gnsQuotient) :
    φ.gnsInner (x + y) z = φ.gnsInner x z + φ.gnsInner y z := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal y
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal z
  simp only [← Submodule.Quotient.mk_add, gnsInner_mk, mul_add, φ.map_add]

/-- Scalar multiplication in the first argument: ⟨c • x, y⟩ = c * ⟨x, y⟩. -/
theorem gnsInner_smul_left (c : ℂ) (x y : φ.gnsQuotient) :
    φ.gnsInner (c • x) y = c * φ.gnsInner x y := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal x
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal y
  simp only [← Submodule.Quotient.mk_smul, gnsInner_mk]
  rw [mul_smul_comm, φ.map_smul]

/-- The inner product with zero on the left. -/
@[simp]
theorem gnsInner_zero_left (y : φ.gnsQuotient) : φ.gnsInner 0 y = 0 := by
  obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal y
  simp only [← Submodule.Quotient.mk_zero, gnsInner_mk, mul_zero, map_zero]

/-- The inner product with zero on the right. -/
@[simp]
theorem gnsInner_zero_right (x : φ.gnsQuotient) : φ.gnsInner x 0 = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective φ.gnsNullIdeal x
  simp only [← Submodule.Quotient.mk_zero, gnsInner_mk, star_zero, zero_mul, map_zero]

end State
