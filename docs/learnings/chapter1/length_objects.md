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

### Decomposition Gap — Categorical Orzech Theorem Needed

**Proved:**
- `inf_arrow_comp_pow_eq_zero` — (K ⊓ I).arrow ≫ f^n = 0

**Gaps (both blocked by categorical Orzech):**

1. **⊓ = ⊥ (lemmafeld-zy7n):** Need (K ⊓ I).arrow = 0 from composition = 0
2. **⊔ = ⊤ (lemmafeld-c5gz):** Need to construct decomposition x = k + i

**Root cause:** Both require that `f^n|_I : Im(f^n) → Im(f^n)` is an isomorphism.
- Image stabilization gives: f^n|_I is **epi**
- Missing lemma: epi endo on Noetherian → **mono** (hence iso)

### Categorical Orzech Theorem (2026-01-29 Research)

**Problem:** Mathlib has `IsNoetherian.injective_of_surjective_endomorphism` for **modules only**.
No categorical version exists for `IsNoetherianObject`.

**Module proof technique (Djoković):**
- Uses `LinearMap.iterateMapComap f i n K` = `(f⁻¹ ∘ i)^n(K)`
- For endomorphism f with i=id, this is the kernel chain
- Stabilization + surjectivity ⟹ kernel is trivial

**Why it doesn't categorify directly:**
- Module proof relies on "choosing preimages" from surjective maps
- Categorically: epi ≠ surjective (no element selection)
- Step "x ∈ Im(f^n) ⟹ x = f^n(y) for some y" fails

**Solution: Categorical iterateComap chain**

**Lean file:** `Chapter1/IterateComap.lean` (230 LOC)

**Definition implemented (2026-01-29):**
```lean
/-- For endomorphism f : X ⟶ X, iterateComap f K n is the nth iterate of pullback along f. -/
def iterateComap {X : C} (f : X ⟶ X) (K : Subobject X) (n : ℕ) : Subobject X :=
  ((pullback f).obj)^[n] K
```

**Key lemmas proved:**
- `iterateComap_zero` — `iterateComap f K 0 = K`
- `iterateComap_succ` — `iterateComap f K (n+1) = (pullback f).obj (iterateComap f K n)`
- `iterateComap_mono_of_le` — preserves ≤ between starting subobjects
- `iterateComap_mono_of_le_pullback` — chain is monotone when `K ≤ (pullback f).obj K`
- `iterateComap_mono` — full monotonicity under same condition

**Critical correction (2026-01-29):** The earlier claims that `pullback_bot = ⊥` and
`iterateComap_bot = ⊥` were **WRONG**. The pullback of ⊥ is the **kernel**, not ⊥!

**Corrected lemmas:**
- `isPullback_kernel_zero` — kernel f is the pullback of 0 : 0 → X along f
- `pullback_bot_eq_kernelSubobject` — `(pullback f).obj ⊥ = kernelSubobject f`
- `iterateComap_bot_one` — `iterateComap f ⊥ 1 = kernelSubobject f`
- `iterateComap_bot_mono` — chain from ⊥ is always monotone (since ⊥ is minimal)

**Stabilization lemmas (2026-01-29 - lemmafeld-ovvv COMPLETE):**
- `iterateComap_stabilizes` — monotone chain stabilizes for Noetherian objects
- `iterateComap_bot_stabilizes` — chain from ⊥ stabilizes for Noetherian objects

**Categorical Orzech Theorem (2026-01-29 - lemmafeld-8sen COMPLETE, lemmafeld-bl7f COMPLETE):**

**Lean file:** `Chapter1/CategoricalOrzech.lean` (~280 LOC)

**Lemmas proved:**
- `isZero_of_epi_pow_eq_zero` — epi g + g^n = 0 ⟹ IsZero Y (helper for nilpotent argument)
- `kernel_ι_eq_zero_of_isIso` — kernel.ι of iso is zero
- `kernelSubobject_of_isIso` — kernelSubobject of iso is ⊥
- `pullback_kernelSubobject_eq` — (pullback f).obj (kernelSubobject g) = kernelSubobject (f ≫ g)
  - **Proof technique:** Construct IsPullback via `PullbackCone.isLimitAux'`
- `iterateComap_bot_eq_kernelSubobject_pow` — iterateComap f ⊥ n = kernelSubobject (f^n)
- `kernelSubobject_eq_bot_of_epi_noetherian` — epi f + Noetherian ⟹ kernelSubobject f = ⊥
  - n = 0 case: if stabilizes at 0, f^0 = id is iso, so kernel is ⊥
  - **n ≥ 1 case (Djoković argument):** COMPLETE
    1. Extract isomorphism φ from saturation via `isoOfMkEqMk`
    2. Construct induced map k via pullback, induced endo g = φ.hom ≫ k
    3. g is epi: k is epi (by `Abelian.epi_fst_of_isLimit`), φ.hom is iso
    4. g^n = 0: from g ≫ kernel.ι = kernel.ι ≫ f and kernel.ι ≫ f^n = 0
    5. By `isZero_of_epi_pow_eq_zero`: kernel (f^n) is zero, hence ⊥
- `mono_of_epi_endomorphism_noetherianObject` — **MAIN THEOREM** (no sorries!)
- `isIso_of_epi_endomorphism_noetherianObject` — corollary: epi endo on Noetherian is iso

**Key insights from proof:**
- Epi stability under pullback (`Abelian.epi_fst_of_isLimit`) is crucial
- The induced map construction uses `isoOfMkEqMk` + kernel.lift
- Nilpotent + epi argument: g^n = 0, g epi ⟹ g^(n-1) = 0 by cancel_epi, inductively g = 0

**Dependency chain:** ~~8yab~~ → ~~ovvv~~ → ~~8sen~~ → ~~bl7f~~ → ~~{zy7n, c5gz}~~ → txf9 (Fitting)

### Fitting Decomposition Proofs (2026-01-29 - zy7n, c5gz COMPLETE)

**Proved lemmas:**
- `kernelSubobject_inf_imageSubobject_eq_bot` — K ⊓ I = ⊥ at stabilization
- `kernelSubobject_sup_imageSubobject_eq_top` — K ⊔ I = ⊤ at stabilization

**Key construction (for both proofs):**
1. h = I.factorThru (I.arrow ≫ f^n) : End(underlying(I))
2. h ≫ I.arrow = I.arrow ≫ f^n
3. h is epi (image stabilization)
4. h is iso (categorical Orzech + Noetherian)

**Proof of inf = ⊥:**
- Construct (K ⊓ I).arrow → 0 by showing ofLE ≫ h = 0 and h is iso

**Proof of sup = ⊤:**
1. s_I = factorThru(f^n) ≫ inv(h) is a section of I.arrow
2. p_I = s_I ≫ I.arrow is idempotent projection onto I
3. (𝟙 X - p_I) ≫ f^n = 0, so (𝟙 X - p_I) factors through K
4. 𝟙 X = q_K ≫ K.arrow + s_I ≫ I.arrow (splitting)
5. This shows (K ⊔ I).arrow is epi, hence K ⊔ I = ⊤

**Mathlib references:**
- `Mathlib.Algebra.Module.Submodule.IterateMapComap` — module version
- `Mathlib.RingTheory.Noetherian.Orzech` — Orzech theorem for modules
- `Mathlib.CategoryTheory.Subobject.NoetherianObject` — categorical Noetherian

**Lean file:** `Chapter1/FittingLemma.lean`

### End(X) is Local Ring (2026-01-30 - lemmafeld-6xvp COMPLETE)

**Statement:** For indecomposable X of finite length, End(X) is a local ring.

**Key lemma:** `eq_zero_of_isNilpotent_of_left_inv`
- If x is nilpotent and has a left inverse l (l*x = 1), then x = 0
- Proof: By induction, l*x^(k+1) = x^k, so x^n = 0 implies x^(n-1) = 0, etc.

**Main theorem:** `isLocalRing_end_of_indecomposable_finiteLength`
- Uses `IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add`
- By Fitting, every endo is nilpotent or unit
- If f, g both nilpotent but f+g unit with inverse v:
  - Apply Fitting to v*f
  - If v*f unit: f has left inverse → f = 0 → contradiction
  - If v*f nilpotent: v*g = 1 - v*f is unit → g has left inverse → g = 0 → contradiction

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
