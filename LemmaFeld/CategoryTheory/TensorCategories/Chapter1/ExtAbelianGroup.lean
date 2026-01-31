/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# Abelian Group Structure on Ext

This file documents the abelian group structure on Ext groups from Exercise 1.4.3(i)
of Etingof et al. "Tensor Categories" (AMS 2015), §1.4.

## Main Results

Mathlib provides `AddCommGroup (Ext X Y n)` for any n ≥ 0 via the derived category.
We document:
- The AddCommGroup instance on Ext¹
- Composition distributes over addition
- The standard abelian group axioms

## Key Mathlib APIs

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Ext¹(Y, X) | `Ext X Y 1` | Arguments are reversed |
| Abelian group on Ext | `AddCommGroup (Ext X Y n)` | Instance |
| Zero element | `0 : Ext X Y 1` | Split extension |
| Addition | `α + β` | From AddCommGroup |
| Negation | `-α` | From AddCommGroup |

## References

- Etingof et al. "Tensor Categories" (AMS 2015), §1.4, Exercise 1.4.3(i)
- mathlib: `Mathlib.Algebra.Homology.DerivedCategory.Ext`
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Abelian

/-! ## §1.4 Exercise 1.4.3(i): The Abelian Group Structure on Ext¹

The book asks us to show that the Baer sum defines an abelian group structure on Ext¹(Y, X).
Mathlib already has `AddCommGroup (Ext X Y n)` for any n ≥ 0.
-/

section ExtAbelianGroup

variable {C : Type*} [Category C] [Abelian C] [HasExt C]

-- Book: Ext¹(Y, X) is an abelian group
-- Mathlib: `AddCommGroup (Ext X Y n)` is an instance
example (X Y : C) : AddCommGroup (Ext X Y 1) := inferInstance

-- The zero element corresponds to the split extension 0 → X → X ⊕ Y → Y → 0
example (X Y : C) : Ext X Y 1 := 0

-- Addition on Ext is compatible with composition
-- (α + β) ∘ γ = α ∘ γ + β ∘ γ
example {X Y Z : C} (α β : Ext X Y 1) (γ : Ext Y Z 0) :
    (α + β).comp γ (Nat.add_zero 1) = α.comp γ (Nat.add_zero 1) + β.comp γ (Nat.add_zero 1) :=
  Ext.add_comp α β γ (Nat.add_zero 1)

-- α ∘ (β + γ) = α ∘ β + α ∘ γ
example {X Y Z : C} (α : Ext X Y 0) (β γ : Ext Y Z 1) :
    α.comp (β + γ) (Nat.zero_add 1) = α.comp β (Nat.zero_add 1) + α.comp γ (Nat.zero_add 1) :=
  Ext.comp_add α β γ (Nat.zero_add 1)

-- Negation: (-α) ∘ β = -(α ∘ β)
example {X Y Z : C} (α : Ext X Y 1) (β : Ext Y Z 0) :
    (-α).comp β (Nat.add_zero 1) = -(α.comp β (Nat.add_zero 1)) :=
  Ext.neg_comp α β (Nat.add_zero 1)

-- Zero is absorbing: 0 ∘ β = 0
example {X Y Z : C} (β : Ext Y Z 1) :
    (0 : Ext X Y 0).comp β (Nat.zero_add 1) = 0 :=
  Ext.zero_comp X 0 β 1 (Nat.zero_add 1)

end ExtAbelianGroup

/-! ## Abelian Group Axioms

Exercise 1.4.3(i) asks us to verify:
1. Well-definedness (independent of representatives)
2. Associativity: (S + S') + S'' = S + (S' + S'')
3. Zero element: the split extension
4. Inverses: the opposite extension
5. Commutativity: S + S' = S' + S

All follow from `AddCommGroup (Ext X Y 1)`.
-/

section AbelianGroupAxioms

variable {C : Type*} [Category C] [Abelian C] [HasExt C]
variable (X Y : C)

-- 1. Well-definedness is built into the Ext type (quotient by quasi-isomorphisms)

-- 2. Associativity
example (α β γ : Ext X Y 1) : (α + β) + γ = α + (β + γ) := add_assoc α β γ

-- 3. Zero element (identity for addition)
example (α : Ext X Y 1) : α + 0 = α := add_zero α
example (α : Ext X Y 1) : 0 + α = α := zero_add α

-- 4. Inverses exist
example (α : Ext X Y 1) : α + (-α) = 0 := add_neg_cancel α
example (α : Ext X Y 1) : (-α) + α = 0 := neg_add_cancel α

-- 5. Commutativity
example (α β : Ext X Y 1) : α + β = β + α := add_comm α β

end AbelianGroupAxioms

end LemmaFeld.TensorCategories.Chapter1
