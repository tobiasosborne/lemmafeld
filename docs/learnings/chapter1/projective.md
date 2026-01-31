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

**Book Definition 1.6.6:** Projective cover = projective P(X) with epi p: P(X) → X such that
any other epi g: Q → X from projective Q factors through p via an epi h: Q → P(X).

**Book Definition 1.6.7:** Injective hull = injective Q(X) with mono i: X → Q(X) such that
any other mono g: X → I to injective I factors through i via a mono h: Q(X) → I.

### Mathlib Gap: Minimality Property

**Mathlib has `ProjectivePresentation`/`InjectivePresentation`:**
```lean
structure ProjectivePresentation (X : C) where
  p : C
  f : p ⟶ X
  projective : Projective p := by infer_instance
  epi : Epi f := by infer_instance
```

**The gap:** Mathlib's presentations are just (projective + epi) or (injective + mono).
The book's covers/hulls have a **minimality/universality property**: any other presentation
factors through them via an epi/mono.

### Our Implementation (2026-01-31)

```lean
/-- Projective cover with universality property -/
structure ProjectiveCover (X : C) where
  P : C
  projective : Projective P
  p : P ⟶ X
  epi : Epi p
  universalProperty : ∀ (Q : C) [Projective Q] (g : Q ⟶ X) [Epi g],
    ∃ (h : Q ⟶ P), Epi h ∧ h ≫ p = g

/-- Injective hull with universality property -/
structure InjectiveHull (X : C) where
  Q : C
  injective : Injective Q
  i : X ⟶ Q
  mono : Mono i
  universalProperty : ∀ (I : C) [Injective I] (g : X ⟶ I) [Mono g],
    ∃ (h : Q ⟶ I), Mono h ∧ i ≫ h = g
```

**Conversions:** `ProjectiveCover.toProjectivePresentation`, `InjectiveHull.toInjectivePresentation`

**Enough projectives/injectives:**
```lean
class EnoughProjectives (C : Type*) [Category C] : Prop where
  presentation : ∀ X : C, Nonempty (ProjectivePresentation X)

class EnoughInjectives (C : Type*) [Category C] : Prop where
  presentation : ∀ X : C, Nonempty (InjectivePresentation X)
```

**Note:** `(0 : C)` notation requires `open scoped ZeroObject`.

**Lean file:** `Chapter1/Projective.lean`
