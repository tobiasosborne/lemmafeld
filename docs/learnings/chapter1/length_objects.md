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

### Krull-Schmidt Existence (2026-01-30 - lemmafeld-zczy PARTIAL, 2 sorries)

**Statement:** Any finite length object admits an indecomposable decomposition.

**Proof structure implemented:**
1. **Zero case:** `emptyDecomposition` - decomposition with n=0 components
2. **Indecomposable case:** `singletonDecomposition` - decomposition with n=1 component
3. **Decomposable case:** X ≅ Y ⊞ Z with both nonzero, recursively decompose Y and Z

**Helper lemmas proved:**
- `isFiniteLengthObject_of_iso` - finite length preserved under iso
- `isFiniteLengthObject_biprod_fst/snd` - biproduct components have finite length
- `biproduct_empty_isZero` - ⨁ Fin.elim0 is zero
- `biproductSingletonIso` - ⨁ (fun _ : Fin 1 => X) ≅ X

**biproductBiprodIso — COMPLETE (2026-01-30, lemmafeld-lxg9):**

Proves `(⨁ f) ⊞ (⨁ g) ≅ ⨁ (concatFin f g)` for concatenating decompositions.

- `hom`: biprod.desc that maps left components to first n indices, right to last m
- `inv`: biproduct.desc that routes back based on index being < n or ≥ n
- `hom_inv_id`: Proved using `biprod.hom_ext'` then `biproduct.hom_ext'`
  - Key insight: Use extensionality from both directions
  - Simplify index arithmetic with `Nat.add_sub_cancel_left`
- `inv_hom_id`: Proved using `biproduct.hom_ext'` + split_ifs on index

Helper lemmas:
- `concatFin` - concatenated family definition
- `concatFin_left/right/right'` - key equalities for index mapping
- `biproduct_ι_cast'` - reindexing biproduct inclusions via eqToHom
- `biproduct_ι_fin_eq'` - biproduct.ι with equal indices via congrArg

**Remaining sorries (2):**
1. Recursive decomposition of Y - needs well-founded recursion
2. Recursive decomposition of Z - needs well-founded recursion

**Key insight:** The recursive calls need well-founded recursion. The termination
argument is that Y and Z embed into X via proper monomorphisms, and the Artinian
property ensures well-foundedness. Setting up this well-founded relation is the
main remaining work.

**Approach for well-founded recursion:**
- Define relation: Y ≺ X iff Y iso to proper subobject of X
- Show this is well-founded for finite-length objects (by Artinian)
- Use `WellFounded.fix` with this relation

**Lean file:** `Chapter1/KrullSchmidt.lean`

### Well-Founded Recursion Infrastructure (2026-01-30 - lemmafeld-4ik7 PARTIAL)

For the recursion in Krull-Schmidt existence, we need to show Y and Z are "smaller"
than X when X ≅ Y ⊕ Z with both nonzero.

**Completed lemmas (NO SORRIES):**

1. `isZero_of_isIso_biprod_inl` — If `biprod.inl : Y → Y ⊕ Z` is iso, then Z is zero
   - Proof: inv biprod.inl = biprod.fst (by uniqueness of left inverse)
   - Then biprod.inr ≫ biprod.fst = 0, and tracing through shows 𝟙_Z = 0

2. `isZero_of_isIso_biprod_inr` — Symmetric for inr

3. `subobjectOfBiprodFst` — Creates Subobject X from Y when X ≅ Y ⊕ Z
   ```lean
   def subobjectOfBiprodFst {X Y Z : C} (i : X ≅ Y ⊞ Z) : Subobject X :=
     Subobject.mk (biprod.inl ≫ i.inv)
   ```

4. `subobjectOfBiprodFst_lt_top` — **KEY LEMMA**: This subobject is proper when Z ≠ 0
   - If subobject = ⊤, then biprod.inl ≫ i.inv is iso
   - Therefore biprod.inl is iso
   - By isZero_of_isIso_biprod_inl, Z = 0, contradiction

5. `subobjectOfBiprodFst_underlyingIso` — The underlying object is isomorphic to Y

6. `isFiniteLengthObject_subobject` — Subobjects of finite length objects have finite length

**Key insight:** The Artinian property gives `WellFoundedLT (Subobject X)`. When X ≅ Y ⊕ Z
with both nonzero:
- Y ≅ underlying(subobjectOfBiprodFst i) as objects
- subobjectOfBiprodFst i < ⊤ in Subobject X (by lt_top lemma)
- This provides the well-founded recursion measure

**Remaining for WellFounded.fix integration:**
- Connect Y (as object) to its subobject representation
- Use `WellFounded.fix` on Subobject X lattice
- Handle the iso transport between Y and the subobject's underlying object

**Lean file:** `Chapter1/KrullSchmidt.lean`

### Krull-Schmidt Uniqueness (2026-01-30 - lemmafeld-01k3 PARTIAL, 1 sorry)

**Statement:** Indecomposable decompositions are unique up to permutation and isomorphism.

**Approach:** Exchange lemma + induction on number of components.

**Completed lemmas (NO SORRIES):**

1. `nonunits_add_of_local` — Contrapositive of local ring property
2. `exists_isUnit_of_finsum_eq_one` — Finite sum version
3. `exchangeLemma` — **COMPLETE** (2026-01-30)
4. `isZero_component_of_isZero_biproduct` — Biproduct summand of zero is zero
5. `eq_zero_of_isZero_indecomposable_decomposition` — Zero object has no indecomposables
6. `isFiniteLengthObject_of_biproduct_iso` — Finite length transfers through biproduct

**Exchange Lemma (lemmafeld-y9yx — COMPLETE):**
```lean
lemma exchangeLemma {X : C} {n m : ℕ} (hn : 0 < n) ... :
    ∃ j, Nonempty (Y ⟨0, hn⟩ ≅ Z j)
```

**Proof strategy (completed):**
1. Define projections pⱼ = (Y₀ ↪ X → Zⱼ ↪ X → Y₀) via compositions
2. Show ∑ⱼ pⱼ = 𝟙_{Y₀} using biproduct identities
3. Apply `exists_isUnit_of_finsum_eq_one`: some pⱼ is unit in End(Y₀)
4. Write pⱼ = fⱼ ≫ gⱼ where fⱼ : Y₀ → Zⱼ, gⱼ : Zⱼ → Y₀
5. Show gⱼ ≫ fⱼ is unit in End(Zⱼ) using Fitting's lemma
6. Conclude fⱼ is iso (mono + epi in abelian category)

**Uniqueness Theorem (krullSchmidt_uniqueness — 1 SORRY):**

**Base case (n = 0):** COMPLETE
- If d₁.n = 0, X is zero (biproduct over empty index)
- Therefore d₂.n = 0 as well (no indecomposables in zero)

**Single component case (n = 1):** COMPLETE
- If d₁.n = 1, X is indecomposable
- Therefore d₂.n = 1 as well
- The iso f from exchange lemma provides the component matching

**Inductive case (n > 1):** PARTIAL (1 SORRY)
- Proved: If d₁.n > 1, then d₂.n > 1 (via indecomposability argument)
- Exchange lemma gives Y₀ ≅ Z_j for some j
- Remaining: biproduct cancellation + strong induction

**Key Mathlib lemma for cancellation (2026-01-31):**
```lean
-- CategoryTheory.Biprod.isoElim (Mathlib.CategoryTheory.Preadditive.Biproducts)
def isoElim (f : X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂)
    [IsIso (biprod.inl ≫ f.hom ≫ biprod.fst)] : X₂ ≅ Y₂
```

This gives biproduct cancellation when the (1,1) component is an iso.

**Strategy for biproduct cancellation:**
1. Factor `⨁ Y ≅ Y₀ ⊞ (⨁ tail Y)` (head-tail split)
2. Factor `⨁ Z ≅ Z_j ⊞ (⨁ other Z)` (bring matched index j to front)
3. Compose to get iso: `Y₀ ⊞ rest₁ ≅ Z_j ⊞ rest₂`
4. The (1,1) component is f_j from exchange lemma (which is iso)
5. Apply `Biprod.isoElim` to get `rest₁ ≅ rest₂`
6. Apply IH on remainders to get full equivalence

**Next steps for completion:**
1. Implement head-tail split isomorphism for biproducts
2. Implement "bring index j to front" isomorphism (uses reindex/permutation)
3. Verify (1,1) component equals f_j
4. Apply Biprod.isoElim + strong induction
5. Construct permutation σ from matched indices

**Lean file:** `Chapter1/KrullSchmidt.lean`

### biproductHeadTailIso Computation Challenge (2026-01-31)

**Problem:** The current `biproductHeadTailIso` is a 5-way iso composition:
```lean
iso_reindex ≪≫ iso_cast ≪≫ iso_concat ≪≫ iso_split ≪≫ biprod.mapIso iso_head (Iso.refl _)
```
This makes computing `biprod.inl ≫ biproductHeadTailIso.inv` difficult.

**Attempted solution:** Direct definition via universal properties:
```lean
def biproductHeadTailIso {n : ℕ} (hn : 0 < n) (f : Fin n → C) :
    ⨁ f ≅ f ⟨0, hn⟩ ⊞ ⨁ (finTail hn f) where
  hom := biprod.lift (biproduct.π f ⟨0, hn⟩)
           (biproduct.lift fun i => biproduct.π f ⟨i.val + 1, _⟩)
  inv := biprod.desc (biproduct.ι f ⟨0, hn⟩)
           (biproduct.desc fun i => biproduct.ι f ⟨i.val + 1, _⟩)
  hom_inv_id := ...
  inv_hom_id := ...
```

**Result:** Types check correctly, but proving the inverse properties is complex:

1. **Nested extensionality:** Need `biproduct.hom_ext` then `biprod.hom_ext` (or vice versa), creating 3+ nested levels

2. **Index inequality proofs:** `biproduct.ι_π_ne _ h` requires `h : j ≠ k` where indices are `Fin n`. Must construct proofs like:
   ```lean
   have hne : (⟨k.val + 1, _⟩ : Fin n) ≠ ⟨0, hn⟩ := by simp [Fin.ext_iff]; omega
   ```

3. **No biprod.desc_comp:** To compute `biprod.desc f g ≫ h`, must use:
   ```lean
   biprod.desc_eq : biprod.desc f g = biprod.fst ≫ f + biprod.snd ≫ g
   ```
   Then expand with `Preadditive.add_comp`.

4. **Key lemma signatures:**
   - `biproduct.ι_π_ne (f : J → C) {j j' : J} (h : j ≠ j') : biproduct.ι f j ≫ biproduct.π f j' = 0`
   - Note: first explicit arg is `f`, not the proof!
   - `biprod.lift_desc : biprod.lift f g ≫ biprod.desc h i = f ≫ h + g ≫ i`
   - `biprod.inl_fst : biprod.inl ≫ biprod.fst = 𝟙 X`
   - `biprod.inl_snd : biprod.inl ≫ biprod.snd = 0`

**Alternative approaches:**
1. Use `aesop_cat` for automation
2. Add simp lemmas to existing 5-way definition (also complex)
3. Prove needed computation properties directly in Uniqueness.lean via `eqToHom` manipulation

**Lean file:** `Chapter1/KrullSchmidt/BiproductCancellation.lean`

### Simp Lemma Strategy (2026-01-31 - COMPLETE)

**Strategy:** Add simp lemmas to the existing biproductHeadTailIso definition.

**Key simp lemmas (all complete, 0 sorries):**
```lean
lemma biproductHeadTailIso_ι_zero_hom {n : ℕ} (hn : 0 < n) (f : Fin n → C) :
    biproduct.ι f ⟨0, hn⟩ ≫ (biproductHeadTailIso hn f).hom = biprod.inl

@[simp]
lemma biproductHeadTailIso_hom_fst {n : ℕ} (hn : 0 < n) (f : Fin n → C) :
    (biproductHeadTailIso hn f).hom ≫ biprod.fst = biproduct.π f ⟨0, hn⟩

@[simp]
lemma biproductHeadTailIso_inl_inv {n : ℕ} (hn : 0 < n) (f : Fin n → C) :
    biprod.inl ≫ (biproductHeadTailIso hn f).inv = biproduct.ι f ⟨0, hn⟩
```

**Proof technique (discovered 2026-01-31):**

The key insight is that after proper setup, `aesop_cat` handles the remaining complexity:

```lean
lemma biproductHeadTailIso_ι_zero_hom ... := by
  unfold biproductHeadTailIso
  simp only [Iso.trans_hom]
  rw [biproduct.whiskerEquiv_hom]
  simp only [biproduct.ι_desc_assoc, biproduct.mapIso_hom, Category.assoc]
  -- Key: use _assoc versions to thread ι through both maps
  rw [biproduct.ι_map_assoc, biproduct.ι_map_assoc]
  -- Collapse eqToIso.inv ≫ eqToIso.hom chains
  simp only [Iso.inv_hom_id_assoc]
  -- Unfold the biproductBiprodIso
  simp only [Iso.symm_hom, biproductBiprodIso, Nat.lt_one_iff]
  -- aesop_cat handles the rest (dite branching, remaining simp)
  aesop_cat
```

**Why this works:**
1. `biproduct.ι_map_assoc` rewrites `ι ≫ map ≫ rest` to `p ≫ ι ≫ rest` even with prefix terms
2. `Iso.inv_hom_id_assoc` collapses `(eqToIso h).inv ≫ (eqToIso h).hom ≫ rest` to `rest`
3. `aesop_cat` handles the dite branching and remaining biproduct lemmas

**For j ≠ 0 case in hom_fst:**
Same setup, plus `have hj_nlt : ¬ j.val < 1` to guide the dite, then `aesop_cat`.

**Lean file:** `Chapter1/KrullSchmidt/BiproductCancellation.lean`

### biproductSwapFrontIso Simp Lemma Challenge (2026-01-31 - COMPLETE)

**Goal:** Prove `biproductSwapFrontIso.hom ≫ biproduct.π _ ⟨0, _⟩ = biproduct.π f j ≫ eqToHom _`

**Issue:** lemmafeld-zpys ✓

**Original challenge:** Dependent type issues when using `whiskerEquiv` definition.

**Solution (2026-01-31):** Redefined `biproductSwapFrontIso` using direct `biproduct.desc` construction.

**Key insight:**
- `whiskerEquiv` creates complex proof terms `(hw k).inv` from simp-generated proofs
- These proof terms cause "motive is not type correct" errors during rewriting
- Direct `desc`-based construction avoids this by using explicit `eqToHom` with named lemmas

**New definition:**
```lean
def biproductSwapFrontIso {n : ℕ} (f : Fin n → C) (j : Fin n) :
    ⨁ f ≅ ⨁ (f ∘ (finSwapFront j).symm) where
  hom := biproduct.desc fun k =>
    eqToHom (biproductSwapFront_hom_eq f j k) ≫
    biproduct.ι (f ∘ (finSwapFront j).symm) ((finSwapFront j) k)
  inv := biproduct.desc fun k => biproduct.ι f ((finSwapFront j).symm k)
  -- hom_inv_id and inv_hom_id proved via split_ifs + explicit contradiction handling
```

**Why this works:**
1. **inv doesn't need eqToHom** because `g k = f (symm k)` is definitional (function composition)
2. **hom uses explicit eqToHom** with named lemma `biproductSwapFront_hom_eq`
3. **Proofs use `split_ifs`** with explicit `exfalso` for contradiction cases
4. **No dependent type issues** because indices are handled via if-then-else, not subst

**Proof technique for hom_inv_id/inv_hom_id:**
```lean
ext i k
simp only [Category.assoc, biproduct.ι_desc_assoc, Category.id_comp]
simp only [biproduct.ι_π]
split_ifs with h1 h2 h3
· simp only [eqToHom_trans]  -- Both diagonal
· exfalso; apply h2; simp only [finSwapFront_symm, finSwapFront_apply_apply] at h1; exact h1
· exfalso; apply h1; simp only [finSwapFront_symm, finSwapFront_apply_apply]; exact h3
· simp only [eqToHom_comp_iff, comp_zero]  -- Both off-diagonal
```

**Simp lemma `biproductSwapFrontIso_hom_π_zero`:** Proved using same split_ifs technique.

**Lean file:** `Chapter1/KrullSchmidt/BiproductCancellation.lean`

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
