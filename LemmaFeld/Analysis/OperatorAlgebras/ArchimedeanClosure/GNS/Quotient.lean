/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.NullSpace
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.Analysis.InnerProductSpace.Defs

/-! # GNS Quotient Space for M-Positive States

This file constructs the quotient A₀/N_φ with ℝ-module structure.

## Main definitions

* `MPositiveState.gnsQuotient` - The quotient FreeStarAlgebra n ⧸ N_φ
* `MPositiveState.gnsQuotientMk` - The quotient map A₀ →ₗ[ℝ] A₀ ⧸ N_φ

## Mathematical Background

The quotient by the null space N_φ = {a : φ(star a * a) = 0} gives a pre-Hilbert space
structure. The inner product on the quotient is ⟨[a], [b]⟩ = φ(star b * a).
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} (φ : MPositiveState n)

/-! ### The quotient space -/

/-- The GNS quotient space A₀ ⧸ N_φ. -/
abbrev gnsQuotient := FreeStarAlgebra n ⧸ φ.gnsNullIdeal

/-- The quotient map A₀ →ₗ[ℝ] A₀ ⧸ N_φ. -/
def gnsQuotientMk : FreeStarAlgebra n →ₗ[ℝ] φ.gnsQuotient := φ.gnsNullIdeal.mkQ

/-- Apply the quotient map. -/
theorem gnsQuotientMk_apply (a : FreeStarAlgebra n) :
    φ.gnsQuotientMk a = Submodule.Quotient.mk a := rfl

/-- Surjectivity of the quotient map. -/
theorem gnsQuotient_mk_surjective :
    Function.Surjective (Submodule.Quotient.mk (p := φ.gnsNullIdeal)) :=
  Submodule.Quotient.mk_surjective φ.gnsNullIdeal

/-! ### Well-definedness lemmas for inner product -/

/-- If a₁ - a₂ ∈ N_φ, then φ(star b * a₁) = φ(star b * a₂). -/
theorem sesqForm_eq_of_sub_mem_left {a₁ a₂ : FreeStarAlgebra n}
    (ha : a₁ - a₂ ∈ φ.gnsNullIdeal) (b : FreeStarAlgebra n) :
    φ (star b * a₁) = φ (star b * a₂) := by
  have h_null : φ (star (a₁ - a₂) * (a₁ - a₂)) = 0 := ha
  have h_zero : φ (star b * (a₁ - a₂)) = 0 :=
    apply_star_mul_eq_zero_of_apply_star_self_eq_zero φ h_null b
  -- φ(star b * a₁) = φ(star b * a₂ + star b * (a₁ - a₂)) = φ(star b * a₂) + 0 = φ(star b * a₂)
  have hexp : star b * a₁ = star b * a₂ + star b * (a₁ - a₂) := by
    rw [mul_sub, add_sub_cancel]
  rw [hexp, φ.map_add, h_zero, add_zero]

/-- If b₁ - b₂ ∈ N_φ, then φ(star b₁ * a) = φ(star b₂ * a). -/
theorem sesqForm_eq_of_sub_mem_right {b₁ b₂ : FreeStarAlgebra n}
    (hb : b₁ - b₂ ∈ φ.gnsNullIdeal) (a : FreeStarAlgebra n) :
    φ (star b₁ * a) = φ (star b₂ * a) := by
  have h_null : φ (star (b₁ - b₂) * (b₁ - b₂)) = 0 := hb
  -- φ(star a * (b₁ - b₂)) = 0 by Cauchy-Schwarz
  have h_left : φ (star a * (b₁ - b₂)) = 0 :=
    apply_star_mul_eq_zero_of_apply_star_self_eq_zero φ h_null a
  -- φ(star(b₁ - b₂) * a) = φ(star a * (b₁ - b₂)) by sesqForm_symm
  have h_right : φ (star (b₁ - b₂) * a) = 0 := by
    rw [sesqForm_symm φ (b₁ - b₂) a, h_left]
  -- φ(star b₁ * a) = φ(star b₂ * a + star(b₁-b₂) * a) = φ(star b₂ * a) + 0 = φ(star b₂ * a)
  have hexp : star b₁ * a = star b₂ * a + star (b₁ - b₂) * a := by
    rw [star_sub, sub_mul, add_sub_cancel]
  rw [hexp, φ.map_add, h_right, add_zero]

/-- Combined well-definedness: the sesquilinear form descends to the quotient. -/
theorem sesqForm_eq_of_sub_mem {a₁ a₂ b₁ b₂ : FreeStarAlgebra n}
    (ha : a₁ - a₂ ∈ φ.gnsNullIdeal) (hb : b₁ - b₂ ∈ φ.gnsNullIdeal) :
    φ (star b₁ * a₁) = φ (star b₂ * a₂) :=
  calc φ (star b₁ * a₁) = φ (star b₁ * a₂) := sesqForm_eq_of_sub_mem_left φ ha b₁
    _ = φ (star b₂ * a₂) := sesqForm_eq_of_sub_mem_right φ hb a₂

/-! ### The inner product definition -/

/-- Helper: convert from quotient relation to submodule membership. -/
private theorem quotient_rel_to_mem {a b : FreeStarAlgebra n}
    (h : φ.gnsNullIdeal.quotientRel a b) : a - b ∈ φ.gnsNullIdeal := by
  have h1 : -a + b ∈ φ.gnsNullIdeal := QuotientAddGroup.leftRel_apply.mp h
  have h2 : b - a ∈ φ.gnsNullIdeal := by convert h1 using 1; abel
  simpa only [neg_sub] using φ.gnsNullIdeal.neg_mem h2

/-- The inner product on the GNS quotient: ⟨[a], [b]⟩ = φ(star b * a).
    This is ℝ-valued since MPositiveState maps to ℝ. -/
def gnsInner : φ.gnsQuotient → φ.gnsQuotient → ℝ := fun x y =>
  Quotient.liftOn₂ x y (fun a b => φ (star b * a)) <| by
    intro a₁ a₂ b₁ b₂ ha hb
    exact sesqForm_eq_of_sub_mem φ (quotient_rel_to_mem φ ha) (quotient_rel_to_mem φ hb)

/-- The inner product on representatives. -/
@[simp]
theorem gnsInner_mk (a b : FreeStarAlgebra n) :
    φ.gnsInner (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = φ (star b * a) := rfl

/-! ### Inner product properties -/

/-- The inner product is symmetric: ⟨x, y⟩ = ⟨y, x⟩.
    This follows from sesqForm_symm: φ(star a * b) = φ(star b * a). -/
theorem gnsInner_symm (x y : φ.gnsQuotient) : φ.gnsInner x y = φ.gnsInner y x := by
  obtain ⟨a, rfl⟩ := φ.gnsQuotient_mk_surjective x
  obtain ⟨b, rfl⟩ := φ.gnsQuotient_mk_surjective y
  simp only [gnsInner_mk]
  exact sesqForm_symm φ b a

/-- The inner product ⟨x, x⟩ is nonnegative.
    This follows from apply_star_mul_self_nonneg: φ(star a * a) ≥ 0. -/
theorem gnsInner_nonneg (x : φ.gnsQuotient) : 0 ≤ φ.gnsInner x x := by
  obtain ⟨a, rfl⟩ := φ.gnsQuotient_mk_surjective x
  simp only [gnsInner_mk]
  exact φ.apply_star_mul_self_nonneg a

/-- The inner product is additive in the first argument:
    ⟨x + y, z⟩ = ⟨x, z⟩ + ⟨y, z⟩. -/
theorem gnsInner_add_left (x y z : φ.gnsQuotient) :
    φ.gnsInner (x + y) z = φ.gnsInner x z + φ.gnsInner y z := by
  obtain ⟨a, rfl⟩ := φ.gnsQuotient_mk_surjective x
  obtain ⟨b, rfl⟩ := φ.gnsQuotient_mk_surjective y
  obtain ⟨c, rfl⟩ := φ.gnsQuotient_mk_surjective z
  simp only [← Submodule.Quotient.mk_add, gnsInner_mk]
  rw [mul_add, φ.map_add]

/-- The inner product is ℝ-linear in the first argument:
    ⟨r • x, y⟩ = r * ⟨x, y⟩. -/
theorem gnsInner_smul_left (r : ℝ) (x y : φ.gnsQuotient) :
    φ.gnsInner (r • x) y = r * φ.gnsInner x y := by
  obtain ⟨a, rfl⟩ := φ.gnsQuotient_mk_surjective x
  obtain ⟨b, rfl⟩ := φ.gnsQuotient_mk_surjective y
  simp only [← Submodule.Quotient.mk_smul, gnsInner_mk]
  -- r • a = algebraMap r * a, and algebraMap r commutes to the front
  rw [Algebra.smul_def, ← mul_assoc]
  rw [← Algebra.commutes r (star b), mul_assoc, ← Algebra.smul_def, φ.map_smul]

/-! ### Positive definiteness -/

/-- Positive definiteness: ⟨x, x⟩ = 0 ↔ x = 0.

**Proof:**
- (→): If φ(star a * a) = 0, then a ∈ N_φ by definition, so [a] = 0 in the quotient.
- (←): If x = 0, then ⟨0, 0⟩ = φ(star 0 * 0) = φ(0) = 0. -/
theorem gnsInner_self_eq_zero_iff (x : φ.gnsQuotient) :
    φ.gnsInner x x = 0 ↔ x = 0 := by
  obtain ⟨a, rfl⟩ := φ.gnsQuotient_mk_surjective x
  simp only [gnsInner_mk]
  rw [Submodule.Quotient.mk_eq_zero]
  -- Now goal: φ(star a * a) = 0 ↔ a ∈ φ.gnsNullIdeal
  -- This is exactly mem_gnsNullIdeal_iff
  rfl

/-! ### Pre-inner product space structure -/

/-- The Inner instance for the GNS quotient over ℝ. -/
instance gnsQuotientInner : Inner ℝ φ.gnsQuotient := ⟨φ.gnsInner⟩

/-- The inner product equals gnsInner. -/
theorem inner_eq_gnsInner (x y : φ.gnsQuotient) :
    @inner ℝ φ.gnsQuotient φ.gnsQuotientInner x y = φ.gnsInner x y := rfl

/-- The PreInnerProductSpace.Core instance for the GNS quotient over ℝ.

For ℝ, the starRingEnd is the identity, so:
- conj_inner_symm reduces to symmetry
- smul_left reduces to ℝ-linearity -/
noncomputable def gnsPreInnerProductCore : PreInnerProductSpace.Core ℝ φ.gnsQuotient where
  conj_inner_symm x y := by simp only [RCLike.conj_to_real]; exact gnsInner_symm φ y x
  re_inner_nonneg x := by simp only [RCLike.re_to_real]; exact gnsInner_nonneg φ x
  add_left x y z := gnsInner_add_left φ x y z
  smul_left x y r := by simp only [RCLike.conj_to_real]; exact gnsInner_smul_left φ r x y

end MPositiveState

end FreeStarAlgebra
