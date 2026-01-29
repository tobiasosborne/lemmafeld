# Chapter 1: Length Objects (§1.5)

## §1.5.1: Simple Objects

**Book Definition 1.5.1:** Nonzero X is simple if 0 and X are its only subobjects.

**Mathlib (`Mathlib.CategoryTheory.Simple`):**

```lean
class Simple (X : C) : Prop where
  mono_isIso_iff_nonzero : ∀ {Y : C} (f : Y ⟶ X) [Mono f], IsIso f ↔ f ≠ 0
```

**Lean file:** `Chapter1/Simple.lean`

---

## §1.5.2-1.5.3: Schur's Lemma

**Book Lemma 1.5.2:**
- Nonzero f : X → Y (X, Y simple) is iso
- X ≇ Y ⟹ Hom(X, Y) = 0
- Hom(X, X) is a division algebra

**Mathlib (`Mathlib.CategoryTheory.Preadditive.Schur`):**
- `isIso_of_hom_simple` — core Schur
- `finrank_hom_simple_simple_eq_zero_of_not_iso`
- `finrank_endomorphism_simple_eq_one`

**Lean file:** `Chapter1/Simple.lean`

---

## §1.5.2: Semisimple Objects

**Book Definition 1.5.1:** X is semisimple if direct sum of simples.

**Mathlib gap:** No categorical `Semisimple X`. Module version `IsSemisimpleModule` exists.

**Our implementation:**

```lean
def IsSemisimple (X : C) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (S : ι → C), (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S)

class SemisimpleCategory (C : Type*) [Category C] [HasZeroMorphisms C]
    [HasFiniteBiproducts C] : Prop where
  isSemisimple : ∀ X : C, IsSemisimple X
```

**Lean file:** `Chapter1/Semisimple.lean`

---

## §1.5.3-1.5.5: Finite Length and Jordan-Hölder

**Book Definition 1.5.3:** X has finite length if admits Jordan-Hölder series.

**Our definition:**
```lean
def IsFiniteLengthObject (X : C) : Prop := IsArtinianObject X ∧ IsNoetherianObject X
```

**Mathlib has:**
- `IsArtinianObject X` → `WellFoundedLT (Subobject X)` (DCC)
- `IsNoetherianObject X` → `WellFoundedGT (Subobject X)` (ACC)
- `JordanHolderLattice` for abstract lattices
- `instJordanHolderLattice : JordanHolderLattice (Submodule R M)` for modules

**Gap:** No `JordanHolderLattice (Subobject X)` for abelian categories.

**Lean files:** `Chapter1/FiniteLength.lean`, `Chapter1/JordanHolder.lean`

---

## §1.5.7: Krull-Schmidt Theorem

**Book Theorem 1.5.7:** Finite length object admits unique decomposition into indecomposables.

**Mathlib status:** `Indecomposable X` exists. NO Krull-Schmidt theorem.

**Our structures:**

```lean
structure IndecomposableDecomposition (C : Type*) [Category C] (X : C) where
  n : ℕ
  components : Fin n → C
  indecomposable : ∀ i, Indecomposable (components i)
  iso : X ≅ ⨁ components
```

**Gap:** Full proof requires Fitting's Lemma (~50-100 LOC), local End ring (~30-50 LOC), existence by induction (~50-100 LOC), uniqueness via exchange (~100-150 LOC).

**Lean file:** `Chapter1/KrullSchmidt.lean`

---

## Fitting's Lemma

**Statement:** For f : X → X on finite length X, ∃ n such that X = Ker(f^n) ⊕ Im(f^n).

### Chain Stabilization

```lean
lemma kernelSubobject_stabilizes [IsNoetherianObject X] :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → kernelSubobject (f ^ n) = kernelSubobject (f ^ m)

lemma imageSubobject_stabilizes [IsArtinianObject X] :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → imageSubobject (f ^ n) = imageSubobject (f ^ m)
```

### Critical: End X Multiplication is Reversed

In `End X`, multiplication is `x * y = y ≫ x`. So `f^m * f^k = f^k ≫ f^m`.

Use:
- `pow_add_eq_comp` — `f^(m+k) = f^m ≫ f^k` (for kernel chain)
- `pow_add_eq_comp'` — `f^(m+k) = f^k ≫ f^m` (for image chain)

### Decomposition Gap — BOTH Proofs Need Research

**Proved:**
- `inf_arrow_comp_pow_eq_zero` — (K ⊓ I).arrow ≫ f^n = 0

**Gaps (both blocked by same research issue):**

1. **⊓ = ⊥ (lemmafeld-zy7n):** Need (K ⊓ I).arrow = 0 from composition = 0
2. **⊔ = ⊤ (lemmafeld-c5gz):** Need to construct decomposition x = k + i

**Root cause:** Both require that `f^n|_I : Im(f^n) → Im(f^n)` is an isomorphism.
- Image stabilization gives: f^n|_I is **epi**
- Missing lemma: epi endo on Noetherian → **mono** (hence iso)
- Mathlib has `IsNoetherian.injective_of_surjective_endomorphism` for **modules only**
- No categorical version for `IsNoetherianObject`

**Module proof of ⊔ = ⊤ (from `LinearMap.eventually_codisjoint_ker_pow_range_pow`):**
1. For any x, want x ∈ K + I
2. Find y such that f^m(f^n(y)) = f^m(x) (uses Im(f^m) = Im(f^n))
3. Then x - f^n(y) ∈ Ker(f^m) = Ker(f^n), and f^n(y) ∈ Im(f^n)
4. So x = (x - f^n(y)) + f^n(y) ∈ K + I

**Categorical translation failure:**
- Step 2 requires "choosing preimage" from surjective map
- Categorically: epi ≠ surjective (no element selection)
- Fix: if f^n|_I is **iso** (not just epi), we can construct y via inverse

**Research issue:** lemmafeld-hyvg (epi endo on Noetherian → mono)

**Lean file:** `Chapter1/FittingLemma.lean`

---

## §1.5.8: Grothendieck Group

**Book Definition 1.5.8:** Gr(C) is the free abelian group on isomorphism classes of simple objects. The class [X] = ∑_i [X : X_i] X_i uses Jordan-Hölder multiplicities.

**Mathlib:**
- `FreeAbelianGroup α` — free abelian group on type α
- `Algebra.GrothendieckGroup M` — localization of monoid at ⊤ (DIFFERENT construction)
- `JordanHolderLattice (Submodule R M)` — for modules only

**Our implementation:**

```lean
def SimpleObject (C) := { X : C // Simple X }
def IsoClassSimple (C) := Quotient (SimpleObject.setoid C)
def GrothendieckGroup (C) := FreeAbelianGroup (IsoClassSimple C)

class HasMultiplicity (C) where
  multiplicity : (X : C) → (Y : C) → [Simple Y] → ℕ
  multiplicity_add : ∀ (S : ShortComplex C), S.ShortExact → ...
```

**Key property:** If 0 → X → Y → Z → 0 is exact, then [Y] = [X] + [Z].

**Gap:** Full class map [X] requires `JordanHolderLattice (Subobject X)` for categories.

**Lean file:** `Chapter1/GrothendieckGroup.lean`
