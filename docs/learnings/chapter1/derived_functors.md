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
