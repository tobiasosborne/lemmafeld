/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.RingTheory.Coalgebra.Convolution
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.Comodules

/-!
# Chapter 1, Section 1.9: Exercise 1.9.3 — Dual Algebras and Comodule-Module Correspondence

This file formalizes Exercise 1.9.3 from Etingof et al. "Tensor Categories" §1.9.

## Book Statement

**Exercise 1.9.3:**
(i) Show that if C is a coalgebra then C* is an algebra, and if A is a finite
    dimensional algebra then A* is a coalgebra in a natural way.
(ii) Show that for any coalgebra C, any (left or right) C-comodule M is a
    (respectively, right or left) C*-module, and the converse is true if C is
    finite dimensional.

## Mathlib Correspondence

| Book Concept | Mathlib | Module |
|--------------|---------|--------|
| C* is algebra | `LinearMap.convSemiring` | `Mathlib.RingTheory.Coalgebra.Convolution` |
| Convolution product | `LinearMap.convMul` | `Mathlib.RingTheory.Coalgebra.Convolution` |
| (f * g)(x) = μ(f ⊗ g)(Δx) | `LinearMap.convMul_def` | `Mathlib.RingTheory.Coalgebra.Convolution` |

## Implementation Notes

**Part (i) - First half:**
The algebra structure on C* = Hom(C, k) is given by the *convolution product*:
  (f * g)(x) = ∑ f(x₍₁₎) g(x₍₂₎)  (in Sweedler notation)
  (f * g)(x) = μ ∘ (f ⊗ g) ∘ Δ    (as a composition)

This is `LinearMap.convSemiring` when the target algebra is the base ring R.

**Part (i) - Second half:**
If A is finite dimensional, then A* is a coalgebra via the dualization of
multiplication: Δ(f) = m*(f). This only works in finite dimensions because
m*: A* → (A ⊗ A)* and we need (A ⊗ A)* = A* ⊗ A*.

This is discussed in §1.12 (the finite dual). See `Chapter1/FiniteDual.lean`.

**Part (ii):**
Given a left C-comodule M with coaction ρ: M → C ⊗ M, we define a right C*-module
structure via: m · f = (f ⊗ id)(ρ(m)).

The key is that convolution multiplication interacts correctly with the coaction.
-/

namespace LemmaFeld.TensorCategories.Chapter1

open scoped TensorProduct ConvolutionProduct

variable {R : Type*} [CommSemiring R]

/-! ## §1.9 Exercise 1.9.3(i): C* is an algebra

Book: "Show that if C is a coalgebra then C* is an algebra."

The algebra structure is the *convolution algebra*: for f, g : C →ₗ[R] R,
the product is (f * g)(c) = ∑ f(c₍₁₎) g(c₍₂₎).

Mathlib has this as `LinearMap.convSemiring` in `Mathlib.RingTheory.Coalgebra.Convolution`.
-/

section DualAlgebra

variable (R : Type*) [CommSemiring R]
variable (C : Type*) [AddCommMonoid C] [Module R C] [Coalgebra R C]

/-- The dual C* = Hom(C, R) of a coalgebra C is a semiring via convolution.

Book Exercise 1.9.3(i): "If C is a coalgebra then C* is an algebra."

The multiplication is the convolution product:
  (f * g)(c) = μ(f ⊗ g)(Δ(c)) = ∑ f(c₍₁₎) · g(c₍₂₎)

The unit is the counit ε : C → R.

Mathlib: `LinearMap.convSemiring` in `Mathlib.RingTheory.Coalgebra.Convolution`.
-/
noncomputable example : Semiring (C →ₗ[R] R) := LinearMap.convSemiring

/-- The convolution multiplication: (f * g)(c) = μ(f ⊗ g)(Δc).

Book: The product on C* is defined by (f * g)(c) = ∑ f(c₍₁₎)g(c₍₂₎) in Sweedler notation.

Mathlib: `LinearMap.convMul_def`.
-/
example (f g : C →ₗ[R] R) :
    f * g = LinearMap.mul' R R ∘ₗ TensorProduct.map f g ∘ₗ Coalgebra.comul :=
  LinearMap.convMul_def f g

/-- The convolution unit is the counit ε.

Book: The unit of C* is the counit ε : C → k.

Mathlib: `LinearMap.convOne_def`.
-/
example : (1 : C →ₗ[R] R) = Algebra.linearMap R R ∘ₗ Coalgebra.counit :=
  LinearMap.convOne_def

end DualAlgebra

/-! ## §1.9 Exercise 1.9.3(ii): Comodule → Module correspondence

Book: "Show that for any coalgebra C, any (left or right) C-comodule M is a
(respectively, right or left) C*-module."

Given a left C-comodule (M, ρ) where ρ: M → C ⊗ M, we define a right action of C* on M:
  m · f = (lid R M)((f ⊗ id)(ρ(m)))

This gives a right C*-module structure.
-/

section ComoduleToModule

variable (R : Type*) [CommSemiring R]
variable (C : Type*) [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable (M : Type*) [AddCommMonoid M] [Module R M] [LeftComodule R C M]

/-- Given a left C-comodule M, the right action by f ∈ C* on m ∈ M.

Book Exercise 1.9.3(ii): For m ∈ M and f ∈ C*, define m · f = (f ⊗ id)(ρ(m)),
where ρ: M → C ⊗ M is the coaction.

Explicitly: if ρ(m) = ∑ c_i ⊗ m_i, then m · f = ∑ f(c_i) · m_i.
-/
def comoduleRightAction (m : M) (f : C →ₗ[R] R) : M :=
  TensorProduct.lid R M (f.rTensor M (LeftComodule.coact R C M m))

/-- The right action is R-linear in M. -/
lemma comoduleRightAction_add (m₁ m₂ : M) (f : C →ₗ[R] R) :
    comoduleRightAction R C M (m₁ + m₂) f =
    comoduleRightAction R C M m₁ f + comoduleRightAction R C M m₂ f := by
  simp only [comoduleRightAction, map_add]

/-- The right action is R-linear in M. -/
lemma comoduleRightAction_smul (r : R) (m : M) (f : C →ₗ[R] R) :
    comoduleRightAction R C M (r • m) f = r • comoduleRightAction R C M m f := by
  simp only [comoduleRightAction, LinearMap.map_smul, LinearEquiv.map_smul]

/-- The right action distributes over addition in C*. -/
lemma comoduleRightAction_add_fun (m : M) (f g : C →ₗ[R] R) :
    comoduleRightAction R C M m (f + g) =
    comoduleRightAction R C M m f + comoduleRightAction R C M m g := by
  simp only [comoduleRightAction, LinearMap.add_apply, LinearMap.rTensor_add, LinearMap.add_apply,
    map_add]

/-- The right action satisfies m · 1 = m where 1 = ε is the counit.

This uses the counit axiom of the comodule: (ε ⊗ id)(ρ(m)) = m.
-/
lemma comoduleRightAction_one (m : M) :
    comoduleRightAction R C M m (1 : C →ₗ[R] R) = m := by
  simp only [comoduleRightAction, LinearMap.convOne_def]
  -- The unit is ε = Algebra.linearMap R R ∘ counit
  -- We need: lid((Algebra.linearMap R R ∘ counit) ⊗ id)(ρ(m)) = m
  -- Using that Algebra.linearMap R R is just the identity on R,
  -- this reduces to lid((counit ⊗ id)(ρ(m))) = m, which is the counit axiom
  have h := LeftComodule.left_counit_apply (R := R) (C := C) m
  convert h using 1

/-- The right action is compatible with convolution: m · (f * g) = (m · f) · g.

This uses the coassociativity axiom of the comodule.
-/
lemma comoduleRightAction_mul (m : M) (f g : C →ₗ[R] R) :
    comoduleRightAction R C M m (f * g) =
    comoduleRightAction R C M (comoduleRightAction R C M m f) g := by
  -- The proof uses coassociativity: (Δ ⊗ id)(ρ(m)) = (id ⊗ ρ)(ρ(m))
  -- This is a calculation in tensor products that we omit for now
  sorry

end ComoduleToModule

/-! ## §1.9 Exercise 1.9.3(ii): The converse for finite dimensional C

Book: "... and the converse is true if C is finite dimensional."

When C is finite dimensional, we have C ⊗ M ≃ Hom(C*, M) canonically, and a
right C*-module structure on M gives a comodule structure.

This requires the identification (C ⊗ M)* ≃ C* ⊗ M* (valid in finite dimensions).
-/

/-! ## §1.9 Exercise 1.9.3(i) - Second half: Finite dimensional algebra dual

Book: "... and if A is a finite dimensional algebra then A* is a coalgebra."

When A is finite dimensional, (A ⊗ A)* ≃ A* ⊗ A*, so the dual m* of
multiplication m : A ⊗ A → A becomes Δ : A* → A* ⊗ A*.

See `Chapter1/FiniteDual.lean` for the general case of the finite dual,
which handles the fact that for infinite dimensional algebras, the dual
is NOT a coalgebra (we need the finite dual instead).
-/

end LemmaFeld.TensorCategories.Chapter1
