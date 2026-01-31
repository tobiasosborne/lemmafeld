/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# §1.7 Exercise 1.7.5: Ring Structure on H*(ℤ/nℤ, ℤ)

This file covers Exercise 1.7.5 from Etingof et al. "Tensor Categories",
concerning the graded ring structure on H*(ℤ/nℤ, ℤ).

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.7, Exercise 1.7.5

## Book Content

**Exercise 1.7.5.** Show that the graded ring H*(ℤ/nℤ, ℤ) is

  H*(ℤ/nℤ, ℤ) = ℤ[x]/(nx) = ℤ ⊕ x(ℤ/nℤ)[x]

where x is a generator in degree 2.

## Explanation

The group cohomology H*(G, A) has a graded ring structure via the **cup product**:
  ∪ : H^a(G, A) ⊗ H^b(G, A) → H^{a+b}(G, A)

For G = ℤ/nℤ with trivial ℤ-coefficients:
- H⁰ = ℤ (Example 1.7.4)
- H^{2j} = ℤ/nℤ for j > 0 (Example 1.7.4)
- H^{2j+1} = 0 for j ≥ 0 (Example 1.7.4)

Let x ∈ H² be a generator (so x generates H² ≅ ℤ/nℤ). Then:
- x² ∈ H⁴ generates H⁴ ≅ ℤ/nℤ
- x³ ∈ H⁶ generates H⁶ ≅ ℤ/nℤ
- etc.

Since nx = 0 in H², the ring is ℤ[x]/(nx).

## Mathlib Correspondence

### The Yoneda Product (Ext Composition)

The cup product on group cohomology is a special case of the Yoneda product on Ext:
  Ext^a(X, Y) × Ext^b(Y, Z) → Ext^{a+b}(X, Z)

Since H^n(G, A) = Ext^n_G(k, A), the cup product on H*(G, k) corresponds to
composing Ext classes with X = Y = Z = k (the trivial representation).

**Mathlib:** `CategoryTheory.Abelian.Ext.comp`
```
Ext.comp : Ext X Y a → Ext Y Z b → (h : a + b = c) → Ext X Z c
```

### Gap: No Explicit Cup Product or Graded Ring Structure

Mathlib does NOT have:
1. An explicit cup product `H^a(G, A) → H^b(G, A) → H^{a+b}(G, A)`
2. A graded ring structure `GradedRing` on `⨁_n H^n(G, k)`
3. The isomorphism H*(ℤ/nℤ, ℤ) ≅ ℤ[x]/(nx)

The infrastructure exists (Ext.comp for Yoneda product, GradedRing for graded
algebras) but the connection to group cohomology is not formalized.

-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1.CohomologyRing

open CategoryTheory CategoryTheory.Abelian

/-! ## The Yoneda Product (Ext Composition)

The Yoneda product composes Ext classes:
  Ext^a(X, Y) × Ext^b(Y, Z) → Ext^{a+b}(X, Z)

This is the underlying operation for the cup product on group cohomology.
-/

#check @Ext.comp
-- Ext X Y a → Ext Y Z b → (h : a + b = c) → Ext X Z c

/-! ## Specializing to Group Cohomology

For a group G and trivial representation k:
  H^n(G, k) = Ext^n_G(k, k)

The cup product H^a(G, k) × H^b(G, k) → H^{a+b}(G, k) is Ext.comp with X = Y = Z = k.

However, mathlib does not have this specialization or the construction of
the graded ring structure on ⨁_n H^n(G, k).
-/

/-! ## What Would Be Needed

To complete Exercise 1.7.5 in mathlib, one would need:

1. **Cup product definition:**
```lean
def groupCohomology.cup {A : Rep k G} (x : groupCohomology A a) (y : groupCohomology A b)
    : groupCohomology A (a + b) := sorry
```

2. **Graded ring structure:**
```lean
instance : GradedRing (fun n => groupCohomology (Rep.trivial k G k) n) := sorry
```

3. **Ring isomorphism for cyclic groups:**
```lean
def cyclicCohomologyRingIso (n : ℕ) [NeZero n] :
    (⨁ i, groupCohomology (Rep.trivial ℤ (Multiplicative (ZMod n)) ℤ) i) ≃+*
    (Polynomial ℤ ⧸ Ideal.span {Polynomial.C n * Polynomial.X}) := sorry
```

These would be substantial additions to mathlib.
-/

/-! ## Related Mathlib Structures

For graded rings, mathlib has:
- `GradedRing` for internally graded rings
- `GradedAlgebra` for graded algebras
- `DirectSum.GRing` for externally graded rings

The connection to cohomology requires constructing the multiplicative structure
on the direct sum of cohomology groups.
-/

#check @GradedRing
#check @DirectSum.GRing

end LemmaFeld.TensorCategories.Chapter1.CohomologyRing
