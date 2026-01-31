# Chapter 1: Higher Ext Groups and Group Cohomology (§1.7)

## §1.7.1: Derived Functors Setup

**Lean file:** `Chapter1/DerivedFunctors.lean`

### Projective Resolutions

**Book:** "A projective resolution of M is an exact sequence · · · → P₂ → P₁ → P₀ → M → 0 where Pᵢ are projective."

**Mathlib (`Mathlib.CategoryTheory.Preadditive.Projective.Resolution`):**
```lean
structure ProjectiveResolution (Z : C) where
  complex : ChainComplex C ℕ
  π : complex ⟶ (ChainComplex.single₀ C).obj Z
  projective : ∀ n, Projective (complex.X n)
  -- plus exactness conditions
```

Existence: `ProjectiveResolution.of X` when `[EnoughProjectives C]`

---

### Injective Resolutions

**Mathlib (`Mathlib.CategoryTheory.Preadditive.Injective.Resolution`):**
```lean
structure InjectiveResolution (Z : C) where
  cocomplex : CochainComplex C ℕ
  ι : (CochainComplex.single₀ C).obj Z ⟶ cocomplex
  injective : ∀ n, Injective (cocomplex.X n)
  -- plus exactness conditions
```

Existence: `InjectiveResolution.of X` when `[EnoughInjectives C]`

---

### Left Derived Functors

**Book:** L_n F(M) = H_n(F(P•)) for right exact F.

**Mathlib:**
```lean
def Functor.leftDerived (F : C ⥤ D) [F.Additive] (n : ℕ) : C ⥤ D
```

**Key insight:** Mathlib requires `[F.Additive]` (F preserves addition), not `[PreservesFiniteColimits F]`. Right exactness is only needed for the 0th derived functor isomorphism.

---

### Right Derived Functors

**Book:** R^n F(M) = H^n(F(I•)) for left exact F.

**Mathlib:**
```lean
def Functor.rightDerived (F : C ⥤ D) [F.Additive] (n : ℕ) : C ⥤ D
```

Same note: requires `[F.Additive]`, not `[PreservesFiniteLimits F]`.

---

### Ext Groups

**Book:** Ext^i(M, N) := Ker(d_{i+1})/Im(d_i) using Hom(P•, N).

**Mathlib (`Mathlib.CategoryTheory.Abelian.Ext`):**
```lean
def Ext (n : ℕ) : Cᵒᵖ ⥤ C ⥤ ModuleCat R
```

Defined by left-deriving the linear Yoneda functor in the first argument:
`Ext R C n := ((linearYoneda R C).obj Y).rightOp.leftDerived n`

---

### Group Cohomology

**Book:** H^i(G, A) = Ext^i_G(ℤ, A) in category of G-modules.

**Mathlib (`Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic`):**
```lean
def groupCohomology (n : ℕ) : Rep k G ⥤ ModuleCat k
def groupCohomologyIsoExt : groupCohomology n ≅ ...  -- isomorphism to Ext
```

---

## Example 1.7.1: Explicit Differential Formulas

**Lean file:** `Chapter1/GroupCohomology.lean`

**Book:** The standard complex C^i(G, A) = Fun(G^i, A) has differential:
```
d_i(f)(g₁,...,gᵢ) = g₁·f(g₂,...,gᵢ)
                  - f(g₁g₂,...,gᵢ)
                  + ... + (-1)^{i-1}·f(g₁,...,g_{i-1}gᵢ)
                  + (-1)^i·f(g₁,...,g_{i-1})
```

**Explicit formulas (Example 1.7.1):**
- d₁(f)(g) = g·f - f
- d₂(f)(g,h) = g·f(h) - f(gh) + f(g)
- d₃(f)(g,h,k) = g·f(h,k) - f(gh,k) + f(g,hk) - f(g,h)
- d₄(f)(g,h,k,l) = g·f(h,k,l) - f(gh,k,l) + f(g,hk,l) - f(g,h,kl) + f(g,h,k)

**Mathlib (`Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic`):**
```lean
inhomogeneousCochains.d_hom_apply :
  (inhomogeneousCochains.d A n).hom f g =
    (A.ρ (g 0)) (f (g ∘ Fin.succ)) +
    ∑ j : Fin (n+1), (-1)^(j+1) • f (j.contractNth (·*·) g)
```

| Component | Book | Mathlib |
|-----------|------|---------|
| G-action term | g₁·f(g₂,...) | `(A.ρ (g 0)) (f (g ∘ Fin.succ))` |
| Contract term | f(g_j·g_{j+1},...) | `f (j.contractNth (·*·) g)` |
| Alternating sign | (-1)^j | `(-1)^(j+1)` in sum |

The bar resolution is `Rep.barResolution k G : ProjectiveResolution (Rep.trivial k G k)`.

---

## Example 1.7.2: Low-Degree Group Cohomology

**Lean file:** `Chapter1/GroupCohomology.lean`

### Part (i): H⁰(G, A) = A^G

**Book:** H⁰(G, A) = A^G (G-invariants). For trivial action, H⁰(G, A) = A.

**Mathlib:**
```lean
groupCohomology.H0Iso : H0 A ≅ ModuleCat.of k ↥A.ρ.invariants
groupCohomology.H0IsoOfIsTrivial : H0 A ≅ A.V  -- when [A.IsTrivial]
```

### Part (ii): H¹(G, A) = Hom(G, A) for trivial action

**Book:** If G acts trivially on A then H¹(G, A) = Hom(G, A).

**Mathlib:**
```lean
groupCohomology.H1IsoOfIsTrivial : H1 A ≅ ModuleCat.of k (Additive G →+ ↑A.V)
```

Note: Uses `Additive G →+ A.V` (additive homomorphisms) rather than multiplicative.

### Part (iii): H²(G, A) classifies extensions

**Book:** H²(G, A) classifies abelian extensions of G by A.

**Mathlib:** Partially formalized. `groupCohomology.H2` exists but explicit
classification theorem needs development. See `Mathlib.GroupTheory.GroupExtension`.

---

## Remark 1.7.3: Non-Abelian 1-Cocycles

**Lean file:** `Chapter1/GroupCohomology.lean`

**Book:** For non-abelian A, a 1-cocycle satisfies:
  f(gh) = f(g) · g·f(h)

Cocycles form a set (not a group) with A-action: (a ∘ f)(g) = a · f(g) · g(a)⁻¹.
H¹(G,A) = orbits. Classifies sections G → A ⋊ G.

**Mathlib:**
```lean
def IsMulCocycle₁ (f : G → M) : Prop := ∀ g h, f (g * h) = g • f h * f g
```

**Convention difference:** Mathlib uses `f(gh) = (g • f(h)) * f(g)`, book uses
`f(gh) = f(g) * (g • f(h))`. Order of multiplication differs.

Semidirect product: `SemidirectProduct N G φ` in `Mathlib.GroupTheory.SemidirectProduct`.

---

## §1.7.2: Ext^n(X, Y) Definition

**Lean file:** `Chapter1/ExtGroups.lean`

### Two Ext APIs in Mathlib

Mathlib provides TWO Ext constructions:

1. **Functor-based** (`Mathlib.CategoryTheory.Abelian.Ext`):
   ```lean
   Ext R C n : Cᵒᵖ ⥤ C ⥤ ModuleCat R
   ```
   Defined by left-deriving the linear Yoneda functor.

2. **Element-based** (`Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`):
   ```lean
   Abelian.Ext X Y n : Type
   ```
   Defined via the derived category. More convenient for explicit calculations.

### Key Results

| Book | Mathlib | Notes |
|------|---------|-------|
| Ext^0(M, N) = Hom(M, N) | `Ext.homEquiv₀` | `Ext X Y 0 ≃ (X ⟶ Y)` |
| Ext^{n+1}(P, Y) = 0 for P projective | `isZero_Ext_succ_of_projective` | |
| Long exact (covariant) | `Ext.covariantSequence_exact` | In second variable |
| Long exact (contravariant) | `Ext.contravariantSequence_exact` | In first variable |
| Computation via resolution | `ProjectiveResolution.isoExt` | `Ext^n ≅ H^n(Hom(P•, Y))` |

### Element-based Ext Operations

```lean
-- Construct Ext^0 from a morphism
Ext.mk₀ : (X ⟶ Y) → Abelian.Ext X Y 0

-- Precomposition (contravariant in first argument)
Ext.precomp : Abelian.Ext X Y n → Abelian.Ext X' Y n  -- given X' ⟶ X

-- Postcomposition (covariant in second argument)
Ext.postcomp : Abelian.Ext X Y n → Abelian.Ext X Y' n  -- given Y ⟶ Y'
```

---

## API Gotcha

**`F.Additive` vs exactness:** The mathlib definition of derived functors requires `[F.Additive]` (functor preserves addition of morphisms), NOT exactness conditions. Exactness is only used for specific theorems like `leftDerivedZeroIsoSelf`.

**Two Ext APIs:** Use `Ext R C n` (functor) for general theory, use `Abelian.Ext X Y n` (element) for explicit calculations with specific objects.

---

## Example 1.7.4: Cohomology of Cyclic Groups

**Lean file:** `Chapter1/CyclicCohomology.lean`

**Book:** For G = ℤ/nℤ, there is a smaller periodic resolution P_i = ℤG with:
- ∂_i = (g-1) if i is odd
- ∂_i = 1 + g + ⋯ + g^{n-1} (norm) if i is even

**Result:**
- H⁰(G, ℤ) = ℤ
- H^{2j}(G, ℤ) = ℤ/nℤ for j > 0
- H^{2j+1}(G, ℤ) = 0 for j ≥ 0

**Mathlib (`Mathlib.RepresentationTheory.Homological.FiniteCyclic`):**

| Book | Mathlib | Notes |
|------|---------|-------|
| Periodic complex | `moduleCatCochainComplex A g` | Alternating (g-1) and norm |
| (g-1) map | `subCompNormHom.f` | "Sub" = g - id |
| norm map | `A.norm` / `subCompNormHom.g` | Σ ρ(h) over h ∈ G |
| A →^{g-1} A →^{norm} A | `subCompNormHom` | Short complex |
| A →^{norm} A →^{g-1} A | `normHomCompSub` | Short complex |

**Gap:** The actual cohomology computation (H^n(ℤ/nℤ, ℤ) ≅ ...) is NOT in mathlib.
The periodic complex structure exists but theorems computing its cohomology
groups (quasi-iso to bar resolution, explicit kernel/image calculations) are missing.

---

## Exercise 1.7.5: Ring Structure on H*(ℤ/nℤ, ℤ)

**Lean file:** `Chapter1/CohomologyRing.lean`

**Book:** The graded ring H*(ℤ/nℤ, ℤ) is:
  H*(ℤ/nℤ, ℤ) = ℤ[x]/(nx) = ℤ ⊕ x(ℤ/nℤ)[x]
where x is a generator in degree 2.

**Mathlib:** The cup product comes from the Yoneda product on Ext:

| Book | Mathlib | Notes |
|------|---------|-------|
| Cup product | `Ext.comp` | Yoneda product |
| Graded ring | `GradedRing` | Internal grading |
| Direct sum ring | `DirectSum.GRing` | External grading |

**Gap:** Mathlib does NOT have:
1. Explicit cup product `H^a(G, A) → H^b(G, A) → H^{a+b}(G, A)`
2. Graded ring structure on `⨁_n H^n(G, k)`
3. The isomorphism H*(ℤ/nℤ, ℤ) ≅ ℤ[x]/(nx)
