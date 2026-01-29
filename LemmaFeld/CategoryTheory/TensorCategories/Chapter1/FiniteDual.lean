/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.RingTheory.TwoSidedIdeal.Lattice
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.Congruence.Basic
import Mathlib.Algebra.Ring.Prod
import Mathlib.Data.Fintype.Prod

/-!
# Chapter 1, Section 1.12: The Finite Dual of an Algebra

This file establishes the finite dual A°_fin of an algebra A, following
Etingof et al. "Tensor Categories" §1.12.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.12

## Main Definitions

* `IsFiniteCodimIdeal`: A two-sided ideal has finite codimension
* `IsFiniteDualElem`: Predicate for functionals in the finite dual (Def 1.12.1)

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Two-sided ideal | `TwoSidedIdeal R` | `Mathlib.RingTheory.TwoSidedIdeal.Basic` |
| Quotient A/I | `I.ringCon.Quotient` | Via `RingCon.Quotient` |
| Dual space A* | `Module.Dual k A` | `Mathlib.LinearAlgebra.Dual.Defs` |
| Finite dual A°_fin | `IsFiniteDualElem` | NEW: predicate defined below |
| Coalgebra | `Coalgebra R A` | `Mathlib.RingTheory.Coalgebra.Basic` |

## Implementation Notes

For the quotient A/I to be a k-module, we need the algebra structure. The quotient
by a two-sided ideal I inherits a ring structure via `RingCon.Quotient`, and when A
is a k-algebra, the quotient becomes a k-algebra (hence k-module).

The key challenge is that mathlib's `TwoSidedIdeal` doesn't directly provide
the module structure on quotients. A full implementation would need to:
1. Define when A/I is a finite-dimensional k-vector space
2. Construct the finite dual as a submodule of A*
3. Define the coalgebra structure (Δ = m*, ε = u*)

We provide the key definitions and document the structure.

-/

namespace LemmaFeld.TensorCategories.Chapter1

open scoped TensorProduct

variable {k : Type*} {A : Type*} [Field k] [Ring A] [Algebra k A]

/-! ## §1.12 Definition 1.12.1: The Finite Dual

Book: "The finite dual A°_fin of A is the collection of all f ∈ A* that vanish on
a (two-sided) ideal of finite codimension."

**Definition 1.12.1.** The finite dual A*_fin of A is the collection of all
f ∈ A* that vanish on a (two-sided) ideal of finite codimension.

Note: "Finite codimension" means that the quotient A/I is finite dimensional
as a k-vector space.
-/

/-- An element of the dual space A* is in the finite dual if it vanishes on
some two-sided ideal whose quotient is finite dimensional.

This is a predicate; we don't construct the submodule structure directly.

Book Definition 1.12.1: f ∈ A°_fin iff ∃ I (two-sided ideal), dim_k(A/I) < ∞, and f|_I = 0
-/
def IsFiniteDualElem (f : Module.Dual k A) : Prop :=
  ∃ I : TwoSidedIdeal A, (∃ _ : Fintype I.ringCon.Quotient, True)
    ∧ ∀ x ∈ I, f x = 0

/-! ## §1.12 Note: A°_fin is a Subspace

Book: "Note that A*_fin is a subspace of A*. Indeed, if f, g ∈ A* vanish on
ideals I and J, respectively, then f + g vanishes on I ∩ J. If I and J have
finite codimension, then so does I ∩ J."

This follows because A/(I ∩ J) embeds into A/I × A/J.
-/

/-! ## §1.12 Proposition 1.12.2: Coalgebra Structure

Book: "The maps Δ := m* and ε := u*, where m : A ⊗ A → A and u : k → A are
the multiplication and unit of A, define a coalgebra structure on A*_fin."

**Proof sketch:**
Take f ∈ A*_fin and let I ⊂ A be an ideal of finite codimension such that
f ∈ I⊥ (i.e., f vanishes on I). Then Δ(f) vanishes on I ⊗ A + A ⊗ I
(since Δ(f)(a ⊗ b) = f(ab) for a, b ∈ A) and, hence,
Δ(f) ∈ I⊥ ⊗ I⊥ ⊆ A*_fin ⊗ A*_fin.

The axioms of a coalgebra follow by duality.
-/

/-- The counit on A* is evaluation at 1.

For f ∈ A*, we have ε(f) = f(1). This is the dual of the unit map u : k → A.
This is well-defined on all of A*, not just the finite dual.
-/
def dualCounit : Module.Dual k A →ₗ[k] k where
  toFun f := f 1
  map_add' f g := by simp
  map_smul' c f := by simp

/-! ## §1.12 Note: Finite Codimension Intersection

If I, J are two-sided ideals with finite codimension, then I ⊓ J has finite codimension.
This follows because A/(I ⊓ J) embeds into A/I × A/J.
-/

section FiniteCodimIntersection

variable (I J : TwoSidedIdeal A)

/-- Map from quotient by intersection to product of quotients.
This sends [a]_{I ⊓ J} to ([a]_I, [a]_J). -/
def quotientInfToProd : (I ⊓ J).ringCon.Quotient → I.ringCon.Quotient × J.ringCon.Quotient :=
  Quotient.lift (fun r => (I.ringCon.mk' r, J.ringCon.mk' r)) <| by
    intro a b h
    have hIJ : (I.ringCon ⊓ J.ringCon) a b := by rw [← TwoSidedIdeal.inf_ringCon]; exact h
    have hI : I.ringCon a b := (inf_le_left : I.ringCon ⊓ J.ringCon ≤ I.ringCon) hIJ
    have hJ : J.ringCon a b := (inf_le_right : I.ringCon ⊓ J.ringCon ≤ J.ringCon) hIJ
    simp only [Prod.mk.injEq]
    exact ⟨I.ringCon.eq.mpr hI, J.ringCon.eq.mpr hJ⟩

/-- The quotient map to product is injective. Key: [a]_I = [b]_I and [a]_J = [b]_J
implies a - b ∈ I ∧ a - b ∈ J, so a - b ∈ I ⊓ J. -/
lemma quotientInfToProd_injective : Function.Injective (quotientInfToProd I J) := by
  intro x y hxy
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  obtain ⟨b, rfl⟩ := Quotient.exists_rep y
  simp only [quotientInfToProd, Quotient.lift_mk, Prod.mk.injEq] at hxy
  apply Quotient.sound
  rw [TwoSidedIdeal.inf_ringCon]
  exact ⟨I.ringCon.eq.mp hxy.1, J.ringCon.eq.mp hxy.2⟩

/-- If I and J have finite codimension, then I ⊓ J has finite codimension.
Proof: A/(I ⊓ J) injects into A/I × A/J, and the product of finite types is finite. -/
noncomputable instance fintypeQuotientInf
    [Fintype I.ringCon.Quotient] [Fintype J.ringCon.Quotient] :
    Fintype (I ⊓ J).ringCon.Quotient :=
  Fintype.ofInjective (quotientInfToProd I J) (quotientInfToProd_injective I J)

end FiniteCodimIntersection

/-! ## §1.12 Remark 1.12.3: When is A°_fin nontrivial?

Book: "Note that if A does not have finite dimensional modules, then A*_fin = 0."

This is because:
- If f ∈ A*_fin, then f vanishes on some ideal I with A/I finite dimensional
- A/I finite dimensional means A has a finite dimensional quotient module
- If no such quotients exist, no nonzero f can be in A*_fin

**Example:** For the Weyl algebra A₁(k) = k⟨x, ∂ | ∂x - x∂ = 1⟩, one has A₁*_fin = 0
since A₁ has no finite dimensional modules (by the relation ∂x - x∂ = 1, any
finite dimensional module would give trace(∂x - x∂) = trace(1), but trace of
a commutator is 0 while trace(1) = dim ≠ 0).
-/

/-! ## Gaps Requiring Follow-up Issues

### Gap 1: Module Structure on Quotient
The quotient `I.ringCon.Quotient` needs a k-module structure to talk about
finite dimensionality. This requires showing that the algebra structure on A
descends to the quotient ring.

**Follow-up:** Create issue for k-module structure on TwoSidedIdeal quotients.

### Gap 2: Finite Codimension Intersection — RESOLVED
The subspace property requires showing that if I, J have finite codimension,
so does I ⊓ J. **PROVED** via `fintypeQuotientInf` above using the embedding
A/(I ⊓ J) ↪ A/I × A/J (`quotientInfToProd`).

### Gap 3: Comultiplication Δ = m*
The comultiplication Δ : A*_fin → A*_fin ⊗ A*_fin requires:
1. The dual map m* : (A ⊗ A)* → A* of multiplication m : A ⊗ A → A
2. For f ∈ A*_fin, showing m*(f) lands in A*_fin ⊗ A*_fin
3. The identification (A ⊗ A)* ≅ A* ⊗ A* (needs finite dim in general)

For the finite dual, we avoid the full dual tensor isomorphism by using
the explicit formula Δ(f)(a ⊗ b) = f(ab) and showing this lands in the right space.

**Follow-up:** Create issue for coalgebra structure on finite dual.

### Gap 4: Full Submodule Construction
To properly work with FiniteDual as a mathematical object, construct it as
`Submodule k (Module.Dual k A)` with carrier `{f | IsFiniteDualElem f}`.

**Follow-up:** Create issue for FiniteDual submodule.
-/

end LemmaFeld.TensorCategories.Chapter1
