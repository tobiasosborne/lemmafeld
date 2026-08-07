import Mathlib

/-!
# Double orthogonal complement over a field

Let `F` be a field and `V` a subspace of `F^n`.  With respect to the dot
product `<x, y> = ∑ i, x_i * y_i` on `F^n`, the double orthogonal complement
satisfies `(V⊥)⊥ = V`.

## Formalization

* `E F n` is the space `Fin n → F`, i.e. `F^n`;
* `dot x y` is the dot product `<x, y> = ∑ i, x i * y i`;
* `Perp V` is the orthogonal complement `{x | ∀ y ∈ V, dot x y = 0}` of a
  subspace `V`;
* `double_orthogonal_eq` is the main theorem `Perp (Perp V) = V`.

## Proof sketch

The dot product induces a linear equivalence
`toDual : E F n ≃ₗ[F] Module.Dual F (E F n)` (namely
`dotProductEquiv F (Fin n)` from `Mathlib.LinearAlgebra.Matrix.Dual`), sending
`x` to the functional `y ↦ <x, y>`.  A vector `x` is orthogonal to a subspace
`W` iff the functional `toDual x` annihilates `W`
(`mem_Perp_iff_mem_dualAnnihilator`).

For `x ∈ Perp (Perp V)`, take any functional `φ` annihilating `V`.  Since
`toDual` is surjective, `φ = toDual y` for some `y`, and then `y ∈ Perp V`
(again by the annihilation translation).  Symmetry of the dot product gives
`φ x = dot y x = dot x y = 0`.  Hence every functional annihilating `V`
vanishes at `x`, so `x ∈ V` by the double-annihilator theorem
`Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff`.

Conversely, if `x ∈ V`, then every `y ∈ Perp V` satisfies
`dot x y = dot y x = 0` by symmetry of the dot product, so
`x ∈ Perp (Perp V)`.
-/

open scoped BigOperators

namespace PerpPerpControl

variable {F : Type*} [Field F] {n : ℕ}

/-- The ambient space `F^n`, realized as functions `Fin n → F`. -/
abbrev E (F : Type*) (n : ℕ) := Fin n → F

/-- The dot product `<x, y> = ∑ i, x_i * y_i` on `F^n`. -/
def dot (x y : E F n) : F :=
  ∑ i : Fin n, x i * y i

/-- The dot product is symmetric: `<x, y> = <y, x>`. -/
@[simp]
lemma dot_comm (x y : E F n) : dot x y = dot y x := by
  simpa [dot] using dotProduct_comm x y

/-- The dot product is additive in its first argument. -/
lemma dot_add_left (x y z : E F n) : dot (x + y) z = dot x z + dot y z := by
  simp [dot, add_mul, Finset.sum_add_distrib]

/-- The dot product is `F`-linear in its first argument. -/
lemma dot_smul_left (a : F) (x y : E F n) : dot (a • x) y = a * dot x y := by
  unfold dot
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The orthogonal complement `Perp V = {x | ∀ y ∈ V, <x, y> = 0}` of a
subspace `V ≤ F^n` with respect to the dot product. -/
def Perp (V : Submodule F (E F n)) : Submodule F (E F n) where
  carrier := { x | ∀ y ∈ V, dot x y = 0 }
  zero_mem' := by
    intro y hy
    simp [dot]
  add_mem' := by
    intro x₁ x₂ hx₁ hx₂ y hy
    rw [dot_add_left, hx₁ y hy, hx₂ y hy]
    simp
  smul_mem' := by
    intro a x hx y hy
    rw [dot_smul_left, hx y hy]
    simp

/-- The dot product induces a linear equivalence between `F^n` and its dual,
sending `x` to the functional `y ↦ <x, y>`.  This is exactly
`dotProductEquiv F (Fin n)` from `Mathlib.LinearAlgebra.Matrix.Dual`. -/
def toDual : E F n ≃ₗ[F] Module.Dual F (E F n) :=
  dotProductEquiv F (Fin n)

/-- The equivalence `toDual` acts by the dot product. -/
@[simp]
lemma toDual_apply (x y : E F n) : toDual x y = dot x y := by
  simp [toDual, dot, dotProduct]

/-- A vector is orthogonal to `V` iff its associated functional annihilates `V`. -/
lemma mem_Perp_iff_mem_dualAnnihilator (V : Submodule F (E F n)) (x : E F n) :
    x ∈ Perp V ↔ toDual x ∈ V.dualAnnihilator := by
  constructor
  · intro hx
    rw [Submodule.mem_dualAnnihilator]
    intro y hy
    simpa using hx y hy
  · intro hx y hy
    rw [Submodule.mem_dualAnnihilator] at hx
    simpa using hx y hy

/-- **Double orthogonal complement theorem.**  For every field `F`, every
`n : ℕ` and every subspace `V` of `F^n`, the orthogonal complement of the
orthogonal complement of `V` — with respect to the dot product
`<x, y> = ∑ i, x_i * y_i` — is `V` itself. -/
theorem double_orthogonal_eq (V : Submodule F (E F n)) : Perp (Perp V) = V := by
  ext x
  constructor
  · -- If every functional annihilating `V` vanishes at `x`, then `x ∈ V`
    -- (double-annihilator theorem); we prove the premise from
    -- `x ∈ Perp (Perp V)`.
    intro hx
    rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff V x]
    intro φ hφ
    rcases toDual.surjective φ with ⟨y, hy⟩
    have hy_perp : y ∈ Perp V := by
      rw [mem_Perp_iff_mem_dualAnnihilator]
      simpa [hy] using hφ
    calc
      φ x = toDual y x := by rw [← hy]
      _ = dot y x := by simp
      _ = dot x y := dot_comm y x
      _ = 0 := hx y hy_perp
  · -- If `x ∈ V`, then `x` is orthogonal to every `y ∈ Perp V`, by symmetry
    -- of the dot product.
    intro hx y hy
    simpa using hy x hx

end PerpPerpControl
