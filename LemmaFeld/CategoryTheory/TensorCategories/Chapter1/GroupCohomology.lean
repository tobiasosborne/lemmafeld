/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.Resolution

/-!
# §1.7: Group Cohomology — Explicit Differential Formulas

This file covers Example 1.7.1 from Etingof et al. "Tensor Categories",
giving explicit formulas for the differentials d₁, d₂, d₃, d₄ in the
standard complex (inhomogeneous cochains) for group cohomology.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.7, Example 1.7.1

## Main Content

The book defines the standard complex C^i(G, A) = Fun(G^i, A) with differential:
  d_i(f)(g₁,...,gᵢ) = g₁·f(g₂,...,gᵢ)
                    - f(g₁g₂,g₃,...,gᵢ)
                    + f(g₁,g₂g₃,...,gᵢ)
                    - ...
                    + (-1)^{i-1}·f(g₁,...,g_{i-1}gᵢ)
                    + (-1)^i·f(g₁,...,g_{i-1})

## Mathlib Correspondence

The differential is `inhomogeneousCochains.d` with explicit formula:
```
(A.ρ (g 0)) (f (g ∘ Fin.succ)) +
  ∑ j : Fin (n+1), (-1)^(j+1) • f (j.contractNth (· * ·) g)
```

| Book | Mathlib | Notes |
|------|---------|-------|
| C^n(G,A) = Fun(G^n, A) | `(Fin n → G) → A.V` | Finite product form |
| d_n : C^n → C^{n+1} | `inhomogeneousCochains.d A n` | |
| g₁·f(g₂,...) | `(A.ρ (g 0)) (f (g ∘ Fin.succ))` | G-action on first arg |
| f(g_j·g_{j+1}, ...) | `f (j.contractNth (· * ·) g)` | Contract at position j |

-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1.GroupCohomology

open CategoryTheory Limits Rep

universe u
variable {k G : Type u} [CommRing k] [Group G] [DecidableEq G]
variable (A : Rep k G)

/-! ## The Differential Formula

The general formula in mathlib is given by `inhomogeneousCochains.d_hom_apply`:

For f : (Fin n → G) → A.V and g : Fin (n+1) → G,

  (d_n f)(g) = (A.ρ (g 0)) (f (g ∘ Fin.succ))
            + ∑ j : Fin (n+1), (-1)^(j+1) • f (j.contractNth (·*·) g)

where `j.contractNth (·*·) g` multiplies g(j) with g(j+1), reducing (n+1) elements to n.
-/

#check @inhomogeneousCochains.d_hom_apply

/-! ## Example 1.7.1: Explicit Formulas for d₁, d₂, d₃, d₄

### d₁ : C⁰(G,A) → C¹(G,A)

Book: d₁(f)(g) = g·f - f

Note: C⁰(G,A) = Fun(G⁰, A) ≅ A (constant functions), so f ∈ A and
d₁(f)(g) = g·f - f = (ρ_g - 1)·f

Mathlib: `inhomogeneousCochains.d A 0` with
  - First term: (A.ρ (g 0)) (f fun i => g i.succ) = g·f (since Fin 0 → G is trivial)
  - Sum over j : Fin 1: j=0 gives (-1)^1 • f (...) = -f
-/

/-! ### d₂ : C¹(G,A) → C²(G,A)

Book: d₂(f)(g, h) = g·f(h) - f(gh) + f(g)

Mathlib: `inhomogeneousCochains.d A 1` with g : Fin 2 → G where g 0 = g, g 1 = h
  - First term: (A.ρ (g 0)) (f (g ∘ Fin.succ)) = g·f(h)
  - j=0: (-1)^1 • f (0.contractNth (·*·) g) = -f(gh)  [contracts g·h]
  - j=1: (-1)^2 • f (1.contractNth (·*·) g) = f(g)   [drops h]
-/

/-! ### d₃ : C²(G,A) → C³(G,A)

Book: d₃(f)(g, h, k) = g·f(h,k) - f(gh,k) + f(g,hk) - f(g,h)

Mathlib: `inhomogeneousCochains.d A 2` with g : Fin 3 → G where g 0 = g, g 1 = h, g 2 = k
  - First term: (A.ρ (g 0)) (f (g ∘ Fin.succ)) = g·f(h,k)
  - j=0: (-1)^1 • f (0.contractNth (·*·) g) = -f(gh, k)
  - j=1: (-1)^2 • f (1.contractNth (·*·) g) = +f(g, hk)
  - j=2: (-1)^3 • f (2.contractNth (·*·) g) = -f(g, h)
-/

/-! ### d₄ : C³(G,A) → C⁴(G,A)

Book: d₄(f)(g, h, k, l) = g·f(h,k,l) - f(gh,k,l) + f(g,hk,l) - f(g,h,kl) + f(g,h,k)

Mathlib: `inhomogeneousCochains.d A 3` with g : Fin 4 → G
  - First term: (A.ρ (g 0)) (f (g ∘ Fin.succ)) = g·f(h,k,l)
  - j=0: (-1)^1 • f (...) = -f(gh,k,l)
  - j=1: (-1)^2 • f (...) = +f(g,hk,l)
  - j=2: (-1)^3 • f (...) = -f(g,h,kl)
  - j=3: (-1)^4 • f (...) = +f(g,h,k)
-/

/-! ## The Inhomogeneous Cochains Complex

The full cochain complex is built from these differentials:
  0 → C⁰(G,A) →^{d₁} C¹(G,A) →^{d₂} C²(G,A) →^{d₃} C³(G,A) → ...

The key property d_{n+1} ∘ d_n = 0 is `inhomogeneousCochains.d_comp_d`.
-/

#check @groupCohomology.inhomogeneousCochains.d_comp_d

/-! ## Group Cohomology

The cohomology of the inhomogeneous cochains complex gives group cohomology:
  H^n(G, A) = Ker(d_{n+1}) / Im(d_n)

Mathlib: `groupCohomology A n : ModuleCat k`
-/

#check groupCohomology

/-! ## Key Low-Degree Results (§1.7 Example 1.7.2)

- H⁰(G, A) = A^G (G-invariants): `groupCohomology.H0Iso`
- For trivial action: H¹(G, A) = Hom(G, A): special case via LowDegree module
-/

#check @groupCohomology.H0Iso

/-! ## The Bar Resolution

The bar resolution P_i = ℤ[G^{i+1}] with ∂_i as in the book is:
  `Rep.barResolution k G : ProjectiveResolution (Rep.trivial k G k)`

This provides a projective resolution of the trivial representation.
-/

#check @Rep.barResolution

end LemmaFeld.TensorCategories.Chapter1.GroupCohomology
