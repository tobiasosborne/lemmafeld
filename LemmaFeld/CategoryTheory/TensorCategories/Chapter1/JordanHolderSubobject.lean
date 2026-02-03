/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.Order.JordanHolder
import Mathlib.CategoryTheory.Simple

/-!
# Jordan-Hölder Lattice for Subobjects

§1.5 Theorem 1.5.4 (Etingof et al.): Jordan-Hölder theorem for abelian categories.

Mathlib provides `JordanHolderLattice (Submodule R M)` for modules but not for
`Subobject X` in abelian categories. This file builds toward that instance.

## Definitions

- `SubobjectIsMaximal A B`: the covering relation `A ⋖ B` on `Subobject X`
- `SubobjectQuotient h`: the quotient object `B/A` as `cokernel (A.ofLE B h)`
- `SubobjectIso p q`: isomorphism of quotient objects for pairs of subobjects
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C] {X : C}

/-! ## IsMaximal: Covering relation on subobjects

Following the module case (`JordanHolderModule`), we define `IsMaximal` as the
covering relation `⋖` (Covby). For subobjects of an object in an abelian category,
`A ⋖ B` means `A < B` and there is no `C` with `A < C < B`, which is equivalent
to B/A being simple.
-/

/-- `IsMaximal A B` means `A` is a maximal proper subobject of `B`,
i.e., the covering relation `A ⋖ B`. -/
def SubobjectIsMaximal (A B : Subobject X) : Prop := A ⋖ B

omit [Abelian C] in
theorem subobjectIsMaximal_lt {A B : Subobject X} (h : SubobjectIsMaximal A B) :
    A < B :=
  h.lt

/-! ## Quotient object B/A

For `A ≤ B` as subobjects of `X`, the quotient `B/A` is the cokernel of the
inclusion `A.ofLE B h : underlying A ⟶ underlying B`.
-/

/-- The quotient object `B/A` for subobjects `A ≤ B`, defined as the cokernel
of the inclusion morphism. -/
def SubobjectQuotient {A B : Subobject X} (h : A ≤ B) : C :=
  cokernel (A.ofLE B h)

/-! ## Iso: Isomorphism of quotient pairs

For pairs `(A₁, B₁)` and `(A₂, B₂)` of subobjects, `SubobjectIso` holds when the
quotients `B₁/(A₁ ⊓ B₁) ≅ B₂/(A₂ ⊓ B₂)` are isomorphic as objects.

Using `A ⊓ B` ensures the definition is well-typed for arbitrary pairs (since
`A ⊓ B ≤ B` always holds). When `A ≤ B`, we have `A ⊓ B = A`, so this
reduces to the standard quotient `B/A`.
-/

/-- Two pairs of subobjects are `SubobjectIso` when their quotient objects
are isomorphic. Uses `A ⊓ B` to handle arbitrary pairs. -/
def SubobjectIso (p q : Subobject X × Subobject X) : Prop :=
  Nonempty (cokernel ((p.1 ⊓ p.2).ofLE p.2 inf_le_right) ≅
            cokernel ((q.1 ⊓ q.2).ofLE q.2 inf_le_right))

theorem subobjectIso_symm {p q : Subobject X × Subobject X}
    (h : SubobjectIso p q) : SubobjectIso q p :=
  h.map Iso.symm

theorem subobjectIso_trans {p q r : Subobject X × Subobject X}
    (h₁ : SubobjectIso p q) (h₂ : SubobjectIso q r) : SubobjectIso p r :=
  ⟨h₁.some ≪≫ h₂.some⟩

end LemmaFeld.TensorCategories.Chapter1
