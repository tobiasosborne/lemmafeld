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

## API Gotcha

**`F.Additive` vs exactness:** The mathlib definition of derived functors requires `[F.Additive]` (functor preserves addition of morphisms), NOT exactness conditions. Exactness is only used for specific theorems like `leftDerivedZeroIsoSelf`.
