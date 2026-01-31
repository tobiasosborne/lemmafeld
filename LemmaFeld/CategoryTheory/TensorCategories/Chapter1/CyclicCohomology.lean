/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.RepresentationTheory.Homological.FiniteCyclic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic

/-!
# §1.7 Example 1.7.4: Cohomology of Cyclic Groups

This file covers Example 1.7.4 from Etingof et al. "Tensor Categories",
concerning the computation of H^i(ℤ/nℤ, ℤ).

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.7, Example 1.7.4

## Book Content

**Example 1.7.4.** Let G = ℤ/nℤ be a finite cyclic group. To compute H^i(G, ℤ):

The bar resolution is too big for convenient computation, but there is a much smaller
free resolution. Let P_i = ℤG = ℤ[g]/(g^n - 1), with differentials:
  - ∂_i(f) = (g - 1)·f  if i is odd
  - ∂_i(f) = (1 + g + ⋯ + g^{n-1})·f  if i is even

Using this resolution:
  - H⁰(G, ℤ) = ℤ
  - H^{2j}(G, ℤ) = ℤ/nℤ  for j > 0
  - H^{2j+1}(G, ℤ) = 0  for j ≥ 0

## Mathlib Correspondence

Mathlib provides the periodic resolution setup in
`Mathlib.RepresentationTheory.Homological.FiniteCyclic`:

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| P_i = A (constant) | `moduleCatCochainComplex` | Alternating complex |
| ∂ = (g-1) on odd | `subCompNormHom.f` | "Sub" map |
| ∂ = Σg^k on even | `subCompNormHom.g` = `A.norm` | Norm map |
| Short: A →^{g-1} A →^{norm} A | `subCompNormHom` | |
| Short: A →^{norm} A →^{g-1} A | `normHomCompSub` | |

**Gap:** The actual cohomology computation theorems (H^n ≅ ...) are NOT yet
proven in mathlib. The setup exists but explicit computation requires additional work.

-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1.CyclicCohomology

open CategoryTheory Limits Rep

universe u
variable {k G : Type u} [CommRing k] [CommGroup G] [Fintype G]
variable (A : Rep k G) (g : G)

/-! ## The Periodic Resolution

For a finite commutative group G with generator g, mathlib defines a periodic
cochain complex using `HomologicalComplex.alternatingConst`. This alternates
between two maps:
  - φ = (g-1) : A → A  (the "sub" map)
  - ψ = norm : A → A   (the "norm" map: Σ_{h∈G} h•a)

These satisfy φ∘ψ = 0 and ψ∘φ = 0, giving the periodic complex:
  A →^ψ A →^φ A →^ψ A →^φ ⋯
-/

#check Rep.FiniteCyclicGroup.moduleCatCochainComplex
-- `moduleCatCochainComplex A g` is a CochainComplex (ModuleCat k) ℕ

/-! ## Short Complexes

The two short complexes capture the periodicity:
  - `subCompNormHom`: A →^{g-1} A →^{norm} A
  - `normHomCompSub`: A →^{norm} A →^{g-1} A
-/

#check Rep.FiniteCyclicGroup.subCompNormHom
-- ShortComplex with f = (g-1).hom, g = norm.hom

#check Rep.FiniteCyclicGroup.normHomCompSub
-- ShortComplex with f = norm.hom, g = (g-1).hom

/-! ## The Norm Map

The norm map Σ_{h∈G} ρ(h) is captured by `Rep.norm`:
-/

#check @Rep.norm
-- Rep.norm A : End A, where (Rep.norm A).hom = A.ρ.norm

/-! ## Key Properties

The complexes satisfy zero composition:
  - (g-1) ∘ norm = 0
  - norm ∘ (g-1) = 0

These are encoded in the `zero` fields of the short complexes, which
assert that the composition of the two maps is zero.
-/

-- The zero property is built into the ShortComplex structure
#check (Rep.FiniteCyclicGroup.subCompNormHom A g).zero
-- States: (g-1) ≫ norm = 0

#check (Rep.FiniteCyclicGroup.normHomCompSub A g).zero
-- States: norm ≫ (g-1) = 0

/-! ## Gap: Cohomology Computation

The book states:
  - H⁰(ℤ/nℤ, ℤ) = ℤ
  - H^{2j}(ℤ/nℤ, ℤ) = ℤ/nℤ for j > 0
  - H^{2j+1}(ℤ/nℤ, ℤ) = 0 for j ≥ 0

To prove this in Lean, we would need:
1. A quasi-isomorphism between the periodic complex and the bar resolution
2. Explicit computation of ker(g-1)/im(norm) and ker(norm)/im(g-1)
3. Specialization to the trivial ℤ-representation

These theorems are NOT yet in mathlib. The infrastructure exists but the
actual computation requires proving:
  - For trivial action: ker(g-1) = A (everything is invariant)
  - For trivial action: im(norm) = n·A (norm = n·id when action is trivial)
  - ker(norm)/im(g-1) = A/nA for even degrees
  - ker(g-1)/im(norm) = 0 for odd degrees
-/

/-! ## What Would Be Needed

To complete Example 1.7.4 in mathlib, one would need:

```lean
-- Quasi-iso between periodic and bar resolution (for cyclic groups)
def periodicQuasiIso : QuasiIso (Rep.FiniteCyclicGroup.moduleCatCochainComplex A g)
    (groupCohomology.inhomogeneousCochains A) := sorry

-- Cohomology at even degrees
def cohomologyEvenIso (j : ℕ) (hj : j > 0) :
    (Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).homology (2 * j) ≅
    A.V ⧸ (LinearMap.range A.norm.hom.hom) := sorry

-- Cohomology at odd degrees is zero
def cohomologyOddIsZero (j : ℕ) :
    IsZero ((Rep.FiniteCyclicGroup.moduleCatCochainComplex A g).homology (2 * j + 1)) := sorry
```

These would be substantial additions to mathlib.
-/

end LemmaFeld.TensorCategories.Chapter1.CyclicCohomology
