/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
# §1.7 Example 1.7.4: Cohomology of Cyclic Groups

This file covers Example 1.7.4 from Etingof et al. "Tensor Categories".

## Book Reference

Etingof et al. "Tensor Categories" (AMS 2015), §1.7, Example 1.7.4

## Main Definitions

* `PeriodicComplex` - The periodic cochain complex for finite cyclic groups
* `subMap` - The (g-1) differential
* `normMap` - The norm differential Σ g^k
* `subNormShort` - Short complex A →^{g-1} A →^{norm} A
* `normSubShort` - Short complex A →^{norm} A →^{g-1} A

## Main Results

* `subMap_comp_normMap` - (g-1) ∘ norm = 0
* `normMap_comp_subMap` - norm ∘ (g-1) = 0
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1.CyclicCohomology

open CategoryTheory Limits Rep

universe u
variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]
variable (A : Rep k G) (g : G)

/-! ## §1.7.4 Book Content

**Example 1.7.4.** Let G = ℤ/nℤ. The bar resolution is too big, but there is a
smaller periodic resolution P_i = ℤG with:
  - ∂_i = (g-1) if i odd
  - ∂_i = 1 + g + ⋯ + g^{n-1} if i even

Result: H⁰ = ℤ, H^{2j} = ℤ/nℤ for j > 0, H^{2j+1} = 0 for j ≥ 0.
-/

/-! ## Definitions -/

/-- The periodic cochain complex for cohomology of finite cyclic groups.
Book: P_i = ℤG with alternating differentials (g-1) and norm. -/
abbrev PeriodicComplex : CochainComplex (ModuleCat k) ℕ :=
  Rep.FiniteCyclicGroup.moduleCatCochainComplex A g

/-- The "sub" map: multiplication by (g - 1).
Book: ∂_i(f) = (g-1)f for i odd. -/
abbrev subMap : A.V ⟶ A.V :=
  (A.applyAsHom g - CategoryTheory.CategoryStruct.id A).hom

/-- The norm map: Σ_{h∈G} ρ(h).
Book: ∂_i(f) = (1 + g + ⋯ + g^{n-1})f for i even. -/
abbrev normMap : A.V ⟶ A.V :=
  A.norm.hom

/-- Short complex A →^{g-1} A →^{norm} A.
Used for computing cohomology at even degrees. -/
abbrev subNormShort : ShortComplex (ModuleCat k) :=
  Rep.FiniteCyclicGroup.subCompNormHom A g

/-- Short complex A →^{norm} A →^{g-1} A.
Used for computing cohomology at odd degrees. -/
abbrev normSubShort : ShortComplex (ModuleCat k) :=
  Rep.FiniteCyclicGroup.normHomCompSub A g

/-! ## Key Properties -/

/-- The composition (g-1) ∘ norm = 0.
This is the exactness condition for even-degree cohomology. -/
theorem subMap_comp_normMap : subMap A g ≫ normMap A = 0 := by
  have h := (subNormShort A g).zero
  simp only [subNormShort, Rep.FiniteCyclicGroup.subCompNormHom] at h
  exact h

/-- The composition norm ∘ (g-1) = 0.
This is the exactness condition for odd-degree cohomology. -/
theorem normMap_comp_subMap : normMap A ≫ subMap A g = 0 := by
  have h := (normSubShort A g).zero
  simp only [normSubShort, Rep.FiniteCyclicGroup.normHomCompSub] at h
  exact h

/-- The periodic complex has constant objects (all equal to A.V). -/
theorem periodicComplex_X (n : ℕ) : (PeriodicComplex A g).X n = A.V := rfl

/-! ## Gap: Cohomology Computation

The book's result H^{2j} = ℤ/nℤ for j > 0 and H^{2j+1} = 0 requires:
1. Quasi-iso between periodic and bar resolution
2. Explicit kernel/image calculations for trivial action

These are NOT in mathlib. See issue tracker for gap documentation.
-/

end LemmaFeld.TensorCategories.Chapter1.CyclicCohomology
