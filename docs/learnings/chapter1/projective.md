# Chapter 1: Projective and Injective Objects (§1.6)

## §1.6.1: Exact Functors

**Book Definition 1.6.1:**
- Left exact: preserves left portion of short exact (kernels)
- Right exact: preserves right portion (cokernels)
- Exact: both

**Mathlib approach:** Uses `PreservesFiniteLimits`/`PreservesFiniteColimits`

| Book | Mathlib |
|------|---------|
| Left exact | `PreservesFiniteLimits F` |
| Right exact | `PreservesFiniteColimits F` |
| Exact | Both properties |
| Bundled | `LeftExactFunctor`, `RightExactFunctor`, `ExactFunctor` |

Equivalence in `Functor.exact_tfae` (`Mathlib.Algebra.Homology.ShortComplex.ExactFunctor`).

---

## §1.6.2: Hom Functors

**Book Example 1.6.2:** Hom functors are left exact.

**Mathlib:**
- `PreservesLimits (coyoneda.obj X)` — Hom(X, -) preserves limits
- `PreservesLimits (yoneda.obj Y)` — Hom(-, Y) preserves limits

---

## §1.6.4: Adjoint Exactness

**Book Exercise 1.6.4:** Left adjoints preserve colimits, right adjoints preserve limits.

**Mathlib:**
- `Adjunction.rightAdjoint_preservesLimits`
- `Adjunction.leftAdjoint_preservesColimits`

---

## §1.6.5: Projective and Injective Objects

**Book Definition 1.6.5:**
- Projective P: Hom(P, -) is exact
- Injective I: Hom(-, I) is exact

**Mathlib (`Mathlib.CategoryTheory.Preadditive.Projective.Basic`):**

```lean
class Projective (P : C) : Prop where
  factors : ∀ {E X : C} (f : P ⟶ X) (e : E ⟶ X) [Epi e], ∃ f', f' ≫ e = f

class Injective (J : C) : Prop where
  factors : ∀ {X E : C} (f : X ⟶ J) (e : X ⟶ E) [Mono e], ∃ f', e ≫ f' = f
```

---

## §1.6.6-1.6.7: Covers and Hulls

**Book Definition 1.6.6:** Projective cover = epimorphism P → X with P projective, minimal.

**Mathlib:**
```lean
structure ProjectivePresentation (X : C) where
  p : C
  f : p ⟶ X
  projective : Projective p := by infer_instance
  epi : Epi f := by infer_instance

structure InjectivePresentation (X : C) where
  J : C
  f : X ⟶ J
  injective : Injective J := by infer_instance
  mono : Mono f := by infer_instance
```

**Enough projectives/injectives:**
```lean
class EnoughProjectives (C : Type*) [Category C] : Prop where
  presentation : ∀ X : C, Nonempty (ProjectivePresentation X)

class EnoughInjectives (C : Type*) [Category C] : Prop where
  presentation : ∀ X : C, Nonempty (InjectivePresentation X)
```

**Note:** `(0 : C)` notation requires `open scoped ZeroObject`.

**Lean file:** `Chapter1/Projective.lean`
