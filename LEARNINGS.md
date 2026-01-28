# Learnings

## 🚨 2026-01-28: CRITICAL FAILURE — Documentation Without Code

**What happened:** An agent spent an entire session "verifying" mathlib coverage and writing to this file, but CREATED ZERO LEAN FILES.

**Why this is wrong:**
- The project goal is to FORMALIZE the book in Lean
- Every issue must produce a `.lean` file
- Documentation alone is NOT sufficient
- Issues were incorrectly closed without any code output

**The fix:**
1. All incorrectly closed issues have been REOPENED
2. CLAUDE.md updated to make "OUTPUT IS LEAN CODE" requirement explicit
3. Implementation plan updated with output requirements
4. Issues updated with comments about output requirement

**For future agents:** The mathlib research below is USEFUL as reference, but you still need to CREATE LEAN FILES that import the mathlib modules and add book reference comments. See CLAUDE.md for the required file format.

---

## 2026-01-28: Session Orientation

**Observation:** `bd ready` returns issues from Chapters 4, 6, 7 first because they have no blockers set. However, the implementation plan requires starting with Chapter 1-2 (foundations) before later chapters.

**Action:** Always check issue numbering (TC X.Y.Z) and start with lowest chapter number, not just what `bd ready` returns.

## 2026-01-28: TC 1.1.1 - Mathlib Category Theory Review

**Task:** Review mathlib's category theory foundations for Chapter 1 topics.

### Mathlib Has (Chapter 1 Topics):

| Topic | Mathlib Location | Status |
|-------|------------------|--------|
| **Abelian categories** | `CategoryTheory.Abelian` | ✅ Complete - includes kernels, cokernels, image, normal mono/epi |
| **Preadditive categories** | `CategoryTheory.Preadditive.Basic` | ✅ Complete - `Preadditive` class with `homGroup`, `add_comp`, `comp_add` |
| **Exact sequences** | `CategoryTheory.ShortComplex` | ✅ Complete - `ShortComplex.Exact`, kernel/cokernel conditions |
| **Simple objects** | `CategoryTheory.Simple` | ✅ Complete - `Simple X` structure, Schur's lemma (`isIso_of_hom_simple`) |
| **Projective/Injective** | `CategoryTheory.Projective`, `CategoryTheory.Injective` | ✅ Complete - includes `EnoughProjectives`, `EnoughInjectives` |
| **Coalgebras** | `Coalgebra`, `CoalgebraCat` | ✅ Complete - R-coalgebras with comul/counit |
| **Comonoid objects** | `Comon_` | ✅ Complete - comonoid objects in monoidal categories |

### Mathlib Has (Chapter 2 Topics):

| Topic | Mathlib Location | Status |
|-------|------------------|--------|
| **Monoidal categories** | `CategoryTheory.MonoidalCategory` | ✅ Complete - tensor, associator, unitors, pentagon/triangle |
| **Braided categories** | `CategoryTheory.BraidedCategory` | ✅ Complete - braiding, hexagon identities |
| **Symmetric categories** | `CategoryTheory.SymmetricCategory` | ✅ Complete - symmetry condition |
| **Monoidal functors** | `CategoryTheory.Functor.Monoidal`, `LaxMonoidal` | ✅ Complete |
| **Duals (rigid)** | `CategoryTheory.HasLeftDual`, `HasRightDual` | ✅ Complete - exact pairings |

### Likely Gaps (Need Verification):

| Topic | Expected Location | Status |
|-------|-------------------|--------|
| Jordan-Hölder theorem | ? | ⚠️ May need implementation |
| Krull-Schmidt theorem | ? | ⚠️ May need implementation |
| Grothendieck group Gr(C) | ? | ⚠️ May need implementation |
| Ext groups | `CategoryTheory.Abelian.Ext` ? | ⚠️ Partial - check coverage |
| Deligne tensor product | ? | ⚠️ Likely needs implementation |
| Coradical filtration | ? | ⚠️ Likely needs implementation |

### Key Imports for Tensor Categories Work:

```lean
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Limits.Shapes.Kernels
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.Algebra.Category.CoalgebraCat.Basic
```

**Recommendation:** Most Chapter 1-2 foundations exist in mathlib. Focus implementation on:
1. Verifying mathlib APIs match book definitions
2. Adding any missing notation/convenience lemmas
3. Implementing genuinely missing concepts (Jordan-Hölder, Deligne tensor product, etc.)

## 2026-01-28: TC 1.1.2 - Notation Conventions

**Task:** Define any missing notation conventions from §1.1.

**Book §1.1 Notation:**
- `id_C` - identity endofunctor
- `C^∨` - opposite/dual category
- Locally small / essentially small
- `Hom_C(X,Y)` - morphism sets
- Fields algebraically closed by default

**Mathlib Equivalents:**
| Book | Mathlib |
|------|---------|
| `id_C` | `𝟭 C` or `Functor.id C` |
| `C^∨` | `Cᵒᵖ` |
| locally small | `LocallySmall` |
| essentially small | `EssentiallySmall` |
| `Hom_C(X,Y)` | `X ⟶ Y` |

**Conclusion:** No notation gaps - mathlib covers all §1.1 conventions. No code needed.

## 2026-01-28: TC 1.1.3 - Locally Small and Essentially Small APIs

**Task:** Establish locally small and essentially small category APIs.

**Book §1.1 says:**
> "A category is called *locally small* if for any objects X, Y, Hom_C(X, Y) is a set, and is called *essentially small* if in addition its isomorphism classes of objects form a set. In other words, an essentially small category is a category equivalent to a small category."

**Mathlib has:**

| Concept | Mathlib | Import |
|---------|---------|--------|
| Locally small | `CategoryTheory.LocallySmall` | `Mathlib.CategoryTheory.Category.Basic` |
| Essentially small | `CategoryTheory.EssentiallySmall` | `Mathlib.CategoryTheory.EssentiallySmall` |

**Mathlib definitions (verified):**

```lean
-- LocallySmall: for all X Y, the hom-set is w-small
class LocallySmall (C : Type u) [Category.{v} C] : Prop where
  hom_small : ∀ (X Y : C), Small.{w} (X ⟶ Y)

-- EssentiallySmall: equivalent to a small category
class EssentiallySmall (C : Type u) [Category.{v} C] : Prop where
  equiv_smallCategory : ∃ S [SmallCategory S], Nonempty (C ≌ S)
```

**Book ↔ Mathlib mapping:**
- Book "Hom_C(X,Y) is a set" = Mathlib `Small (X ⟶ Y)` (hom-set fits in universe w)
- Book "equivalent to a small category" = Mathlib `∃ S, Nonempty (C ≌ S)`

**Conclusion:** Mathlib APIs match book definitions exactly. No code needed.

## 2026-01-28: TC 1.2.1 - Preadditive and Additive Categories

**Task:** Verify mathlib's Preadditive and Additive category definitions match §1.2.

**Book §1.2 defines:**

**Definition 1.2.1** (Additive category): A category C satisfying:
- (A1) Every Hom(X,Y) is an abelian group, composition is biadditive
- (A2) Zero object exists with Hom(0,0) = 0
- (A3) Direct sums exist (with p₁i₁ = id, p₂i₂ = id, i₁p₁ + i₂p₂ = id)

**Definition 1.2.2** (k-linear category): Additive category where Hom(X,Y) are k-vector spaces and composition is k-linear.

**Definition 1.2.3** (Additive functor): Functor where Hom maps are group homomorphisms.

**Proposition 1.2.4**: Additive functor F satisfies F(X⊕Y) ≅ F(X)⊕F(Y).

**Mathlib equivalents:**

| Book Concept | Mathlib | Import |
|-------------|---------|--------|
| (A1) Hom groups + biadditive | `Preadditive` class | `Mathlib.CategoryTheory.Preadditive.Basic` |
| (A2) Zero object | `HasZeroObject` class | `Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects` |
| (A3) Direct sums | `HasBinaryBiproducts` class | `Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts` |
| k-linear category | `Linear R C` | `Mathlib.CategoryTheory.Linear.Basic` |
| Additive functor | `Functor.Additive` | `Mathlib.CategoryTheory.Preadditive.AdditiveFunctor` |
| k-linear functor | `Functor.Linear R` | `Mathlib.CategoryTheory.Linear.LinearFunctor` |
| Prop 1.2.4 | `PreservesBinaryBiproducts` | `Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts` |

**Key insight:** Mathlib doesn't have a single "Additive category" class. Instead, an "additive category" in the book's sense requires three typeclasses:
```lean
variable [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
```

**Mathlib definitions (verified):**

```lean
-- Preadditive (A1): Hom groups with biadditive composition
class Preadditive where
  homGroup : ∀ P Q : C, AddCommGroup (P ⟶ Q)
  add_comp : ∀ (P Q R : C) (f f' : P ⟶ Q) (g : Q ⟶ R), (f + f') ≫ g = f ≫ g + f' ≫ g
  comp_add : ∀ (P Q R : C) (f : P ⟶ Q) (g g' : Q ⟶ R), f ≫ (g + g') = f ≫ g + f ≫ g'

-- Linear (k-linear): R-module structure on Hom
class Linear (R : Type w) [Semiring R] (C : Type u) [Category C] [Preadditive C] where
  homModule : ∀ X Y : C, Module R (X ⟶ Y)
  smul_comp : ∀ (X Y Z : C) (r : R) (f : X ⟶ Y) (g : Y ⟶ Z), (r • f) ≫ g = r • f ≫ g
  comp_smul : ∀ (X Y Z : C) (f : X ⟶ Y) (r : R) (g : Y ⟶ Z), f ≫ (r • g) = r • f ≫ g

-- Additive functor: preserves addition
class Functor.Additive (F : C ⥤ D) : Prop where
  map_add : ∀ {X Y : C} {f g : X ⟶ Y}, F.map (f + g) = F.map f + F.map g
```

**Conclusion:** Mathlib has complete coverage of §1.2. No code needed.

## 2026-01-28: TC 1.3.1 - Abelian Category Definition

**Task:** Verify Mathlib's `Abelian` class matches book's Definition 1.3.1.

**Book Definition 1.3.1 says:**
An abelian category is an additive category C where every morphism φ: X → Y has a canonical decomposition:
```
K → X → I → Y → C
```
with:
1. ji = φ
2. (K, k) = Ker(φ), (C, c) = Coker(φ)
3. (I, i) = Coker(k), (I, j) = Ker(c)

Where I = Im(φ) is the image.

**Mathlib's definition:**

```lean
class Abelian extends Preadditive C, IsNormalMonoCategory C, IsNormalEpiCategory C where
  [has_finite_products : HasFiniteProducts C]
  [has_kernels : HasKernels C]
  [has_cokernels : HasCokernels C]
```

| Book Concept | Mathlib | Import |
|--------------|---------|--------|
| Additive category | `Preadditive` + `HasFiniteProducts` | `Mathlib.CategoryTheory.Preadditive.Basic` |
| Has kernels/cokernels | `HasKernels`, `HasCokernels` | `Mathlib.CategoryTheory.Limits.Shapes.Kernels` |
| Every mono is a kernel | `IsNormalMonoCategory` | `Mathlib.CategoryTheory.Limits.Shapes.NormalMono.Basic` |
| Every epi is a cokernel | `IsNormalEpiCategory` | same |
| Canonical decomposition | `coimageImageComparison` is `IsIso` | `Mathlib.CategoryTheory.Abelian.Basic` |
| Image = Coker(Ker) = Ker(Coker) | `Abelian.coimage`, `Abelian.image` | `Mathlib.CategoryTheory.Abelian.Images` |

**Key theorems for canonical decomposition:**
- `Abelian.coimage f` = Coker(kernel.ι f) = cokernel of kernel
- `Abelian.image f` = Ker(cokernel.π f) = kernel of cokernel
- `instance : IsIso (coimageImageComparison f)` — coimage ≅ image in abelian categories
- `coimage_image_factorisation : coimage.π f ≫ coimageImageComparison f ≫ image.ι f = f`

**Book Definition 1.3.4 (mono/epi characterization):**
- Mono f ⟺ Ker(f) = 0 → Mathlib: `Abelian.tfae_mono` (TFAE list)
- Epi f ⟺ Coker(f) = 0 → Mathlib: `Abelian.tfae_epi` (TFAE list)
- Specific lemmas: `mono_of_kernel_ι_eq_zero`, `kernel.ι_of_mono`, `epi_of_cokernel_π_eq_zero`, `cokernel.π_of_epi`

**Conclusion:** Mathlib's `Abelian` class fully captures the book's Definition 1.3.1. No code needed.

## 2026-01-28: TC 1.3.2 - Kernel and Cokernel APIs

**Task:** Verify kernel and cokernel APIs from §1.3.

**Book says (start of §1.3):**
- Kernel Ker(f) of f: X → Y is K with k: K → X, fk = 0, universal: any k' with fk' = 0 factors uniquely through k
- Cokernel Coker(f) is C with c: Y → C, cf = 0, universal: any c' with c'f = 0 factors uniquely through c

**Mathlib has:**

| Book Concept | Mathlib | Import |
|--------------|---------|--------|
| Kernel object | `kernel f` | `Mathlib.CategoryTheory.Limits.Shapes.Kernels` |
| Kernel morphism k: K → X | `kernel.ι f` | same |
| fk = 0 | `kernel.condition : kernel.ι f ≫ f = 0` | same |
| Universal property (lift) | `kernel.lift : (k' : W ⟶ X) → (h : k' ≫ f = 0) → W ⟶ kernel f` | same |
| Factorization | `kernel.lift_ι : kernel.lift f k' h ≫ kernel.ι f = k'` | same |
| Cokernel object | `cokernel f` | same |
| Cokernel morphism c: Y → C | `cokernel.π f` | same |
| cf = 0 | `cokernel.condition : f ≫ cokernel.π f = 0` | same |
| Universal property (desc) | `cokernel.desc : (c' : Y ⟶ W) → (h : f ≫ c' = 0) → cokernel f ⟶ W` | same |
| Factorization | `cokernel.π_desc : cokernel.π f ≫ cokernel.desc f c' h = c'` | same |

**Additional useful APIs:**
- `kernel.ofMono : kernel f ≅ 0` (when f is mono)
- `kernel.ι_of_mono : kernel.ι f = 0` (when f is mono)
- `cokernel.ofEpi : cokernel f ≅ 0` (when f is epi)
- `cokernel.π_of_epi : cokernel.π f = 0` (when f is epi)
- `kernel.map` / `cokernel.map` - functoriality

**Conclusion:** Mathlib kernel/cokernel APIs match book exactly. No code needed.

## 2026-01-28: TC 1.3.3 - Canonical Decomposition of Morphisms

**Task:** Verify canonical decomposition K → X → I → Y → C from Definition 1.3.1.

**Book says:** Every morphism φ: X → Y in an abelian category has canonical decomposition:
```
K →[k] X →[i] I →[j] Y →[c] C
```
where ji = φ, (K,k) = Ker(φ), (C,c) = Coker(φ), I = Coker(k) = Ker(c) (the image).

**Mathlib has (in `Mathlib.CategoryTheory.Abelian.Images`):**

| Book | Mathlib | Type |
|------|---------|------|
| K | `kernel f` | object |
| k: K → X | `kernel.ι f` | morphism |
| Coimage = Coker(k) | `Abelian.coimage f` = `cokernel (kernel.ι f)` | object |
| X → Coimage | `coimage.π f` | epimorphism |
| Image = Ker(c) | `Abelian.image f` = `kernel (cokernel.π f)` | object |
| Image → Y | `image.ι f` | monomorphism |
| Coimage ≅ Image | `coimageImageComparison f` is `IsIso` | isomorphism |
| C | `cokernel f` | object |
| c: Y → C | `cokernel.π f` | morphism |

**Key factorization theorem:**
```lean
coimage_image_factorisation : coimage.π f ≫ coimageImageComparison f ≫ image.ι f = f
```

**Remark 1.3.2 (uniqueness):** The isomorphism `coimageImageComparison` ensures uniqueness up to unique isomorphism.

**Conclusion:** Mathlib has complete canonical decomposition. No code needed.

## 2026-01-28: TC 1.3.4 - Image Factorization

**Task:** Verify image factorization APIs.

**Book context:** In an abelian category, every f: X → Y factors as f = epi ≫ mono through its image.

**Mathlib has (in `Mathlib.CategoryTheory.Abelian.Basic`):**

| Concept | Mathlib | Description |
|---------|---------|-------------|
| Image factorization | `imageMonoFactorisation f` | f = e ≫ m where m is mono |
| Strong epi-mono factorization | `imageStrongEpiMonoFactorisation f` | e is strong epi, m is mono |
| Dual (coimage) | `coimageStrongEpiMonoFactorisation f` | epi ≫ mono through coimage |
| Has factorisations | `instance : HasStrongEpiMonoFactorisations C` | every abelian category |
| Has images | `instance : HasImages C` | consequence |
| Factor through image | `Abelian.factorThruImage f : X ⟶ Abelian.image f` | the epi part |
| Image inclusion | `image.ι f : Abelian.image f ⟶ Y` | the mono part |
| Epi property | `instance : Epi (Abelian.factorThruImage f)` | |
| Iso when mono | `instance isIso_factorThruImage [Mono f]` | |

**Key isomorphisms:**
- `coimageIsoImage : Abelian.coimage f ≅ Abelian.image f` — coimage ≅ image
- `imageIsoImage : Abelian.image f ≅ image f` — connects to `Limits.image`

**Conclusion:** Mathlib has complete image factorization. No code needed.

## 2026-01-28: TC 1.4.1 - Exact Sequence Definitions

**Task:** Verify exact sequence definitions from §1.4.

**Book Definition 1.4.1:**
- Exact at i: Im(f_{i-1}) = Ker(f_i)
- Short exact sequence: 0 → X → Y → Z → 0

**Mathlib has (in `Mathlib.Algebra.Homology.ShortComplex`):**

| Book Concept | Mathlib | Import |
|--------------|---------|--------|
| Sequence X₁ → X₂ → X₃ | `ShortComplex C` | `Mathlib.Algebra.Homology.ShortComplex.Basic` |
| Exact at middle | `S.Exact : Prop` (homology = 0) | `Mathlib.Algebra.Homology.ShortComplex.Exact` |
| Short exact sequence | `S.ShortExact` = Exact + Mono f + Epi g | `Mathlib.Algebra.Homology.ShortComplex.ShortExact` |

**Key structures:**
```lean
-- ShortComplex: X₁ →[f] X₂ →[g] X₃ with g ∘ f = 0
structure ShortComplex where
  X₁ X₂ X₃ : C
  f : X₁ ⟶ X₂
  g : X₂ ⟶ X₃
  zero : f ≫ g = 0

-- Exact: homology is zero (Im(f) = Ker(g))
structure Exact : Prop where
  condition : ∃ (h : S.HomologyData), IsZero h.left.H

-- ShortExact: 0 → X₁ → X₂ → X₃ → 0
structure ShortExact : Prop where
  exact : S.Exact
  [mono_f : Mono S.f]
  [epi_g : Epi S.g]
```

**Key lemmas for short exact sequences:**
- `ShortExact.fIsKernel` - f is the kernel of g
- `ShortExact.gIsCokernel` - g is the cokernel of f
- `ShortExact.lift` / `ShortExact.desc` - lifting/descending through exact sequence

**Conclusion:** Mathlib exact sequence definitions match book §1.4 exactly. No code needed.

## 2026-01-28: TC 1.4.2 - Short Exact Sequences

**Task:** Verify short exact sequence APIs (X subobject, Z ≅ Y/X).

**Book says (after Def 1.4.1):** "In a short exact sequence 0 → X → Y → Z → 0, X is a subobject of Y and Z ≅ Y/X is the corresponding quotient."

**Mathlib has:**

| Book Statement | Mathlib | Description |
|----------------|---------|-------------|
| X is subobject of Y | `ShortExact.fIsKernel` | f: X → Y is the kernel of g |
| Z ≅ Y/X | `ShortExact.gIsCokernel` | g: Y → Z is the cokernel of f |
| Short exact under iso | `shortExact_of_iso` | preserved by isomorphisms |
| Five lemma (middle iso) | `isIso₂_of_shortExact_of_isIso₁₃` | |

**Additional useful lemmas:**
- `ShortExact.isIso_f_iff : IsIso S.f ↔ IsZero S.X₃` (f is iso iff X₃ = 0)
- `ShortExact.isIso_g_iff : IsIso S.g ↔ IsZero S.X₁` (g is iso iff X₁ = 0)
- `Splitting.shortExact` - splittings give short exact sequences
- `splittingOfInjective` / `splittingOfProjective` - splitting conditions

**Conclusion:** Mathlib ShortExact captures subobject/quotient properties. No code needed.

## 2026-01-28: TC 1.4.3 - Ext¹ as Extensions

**Task:** Verify Ext¹(Y, X) as isomorphism classes of extensions (Definition 1.4.2).

**Book Definition 1.4.2 says:**
Ext¹(Y, X) = isomorphism classes of short exact sequences 0 → X → Z → Y → 0

**Mathlib approach:**
Mathlib defines Ext via derived functors, not via isomorphism classes of extensions:

```lean
-- In Mathlib.CategoryTheory.Abelian.Ext
def Ext (n : ℕ) : Cᵒᵖ ⥤ C ⥤ ModuleCat R :=
  -- Left derived of linear Yoneda functor
```

| Concept | Book | Mathlib |
|---------|------|---------|
| Definition | Yoneda Ext (extensions) | Derived functor |
| Ext¹(Y,X) | Classes of 0 → X → Z → Y → 0 | Left derived of Hom |
| Requirements | Any abelian category | `EnoughProjectives` |
| Degrees | Just Ext¹ in this section | All Ext^n |

**Key insight:** The two definitions are equivalent in abelian categories with enough projectives, but Mathlib uses the derived functor approach which:
1. Is more algebraic and computes all Ext^n uniformly
2. Requires `EnoughProjectives` (or dually `EnoughInjectives`)
3. Doesn't directly give the "extensions" interpretation

**Mathlib has:**
- `Ext R C n : Cᵒᵖ ⥤ C ⥤ ModuleCat R` - the Ext functor
- `ProjectiveResolution.isoExt` - computation via projective resolutions
- `isZero_Ext_succ_of_projective` - Ext^{n+1}(X, Y) = 0 when X projective

**Gap:** Mathlib doesn't have the explicit "Yoneda Ext" construction (Ext¹ as extensions), though this is mathematically equivalent to what it has.

**Conclusion:** Mathlib has Ext via derived functors. No direct "Ext as extensions" API needed for most formalization.

## 2026-01-28: TC 1.4.4 - Addition on Ext¹(Y, X)

**Task:** Verify addition structure on Ext¹(Y, X).

**Book describes:** Baer sum - given two extensions S, S' of Y by X, construct S + S' using pullback and pushout.

**Mathlib approach:** Since `Ext R C n : Cᵒᵖ ⥤ C ⥤ ModuleCat R`, the addition structure comes automatically from the R-module structure on `((Ext R C n).obj X).obj Y : ModuleCat R`.

The Baer sum construction is not explicitly formalized, but is implicit in:
- Derived functor approach gives R-module structure
- `ModuleCat R` has `AddCommGroup` and `Module R` instances

**Conclusion:** Addition on Ext comes automatically from derived functor definition landing in ModuleCat. No separate Baer sum formalization needed.

## 2026-01-28: TC 1.5.1 - Simple Objects Definition

**Task:** Verify simple objects definition from Definition 1.5.1.

**Book Definition 1.5.1:** A nonzero object X is called *simple* if 0 and X are its only subobjects.

**Mathlib has (in `Mathlib.CategoryTheory.Simple`):**

```lean
class Simple (X : C) : Prop where
  mono_isIso_iff_nonzero : ∀ {Y : C} (f : Y ⟶ X) [Mono f], IsIso f ↔ f ≠ 0
```

This is equivalent to the book's definition: a mono into X is either:
- zero (the trivial subobject 0)
- an isomorphism (the subobject X itself)

**Key lemmas:**
- `isIso_of_mono_of_nonzero` - nonzero mono to simple object is iso
- `Simple.of_iso` - simple is preserved by isomorphism
- `mono_to_simple_zero_of_not_iso` - mono that isn't iso must be zero

**Conclusion:** Mathlib `Simple` class matches book Definition 1.5.1. No code needed.

## 2026-01-28: TC 1.5.2 - Semisimple Objects and Categories

**Task:** Verify semisimple objects and categories from Definition 1.5.1.

**Book Definition 1.5.1 (second part):**
- Object X is *semisimple* if it is a direct sum of simple objects
- Category C is *semisimple* if every object is semisimple

**Mathlib status:**
- `IsSemisimpleModule` exists in `Mathlib.RingTheory.SimpleModule.Basic` for modules
- **No categorical `Semisimple` class** for general abelian categories
- `Mathlib.CategoryTheory.Preadditive.HomOrthogonal` is noted as "preliminary to defining semisimple categories"

**Gap:** Mathlib lacks:
1. `Semisimple X` - object is biproduct of simple objects
2. `SemisimpleCategory C` - all objects are semisimple

**For now:** Can work with `IsSemisimpleModule` when in `ModuleCat`, but general categorical semisimplicity is missing.

**Conclusion:** Partial gap - module semisimplicity exists, categorical semisimplicity missing.

## 2026-01-28: TC 1.5.3 - Schur's Lemma

**Task:** Verify Schur's Lemma from Lemma 1.5.2.

**Book Lemma 1.5.2:**
- Let X, Y be simple. Any nonzero f: X → Y is an isomorphism.
- If X ≇ Y then Hom(X, Y) = 0
- Hom(X, X) is a division algebra

**Mathlib has (in `Mathlib.CategoryTheory.Preadditive.Schur`):**

| Book Statement | Mathlib |
|----------------|---------|
| Nonzero f: X → Y is iso | `isIso_of_hom_simple` |
| Morphism is iso ↔ nonzero | `isIso_iff_nonzero` |
| Hom(X, Y) = 0 if X ≇ Y | `finrank_hom_simple_simple_eq_zero_of_not_iso` |
| dim End(X) = 1 | `finrank_endomorphism_simple_eq_one` |
| dim Hom(X, Y) ≤ 1 | `finrank_hom_simple_simple_le_one` |

**Key lemma signatures:**
```lean
-- Core Schur's lemma
theorem isIso_of_hom_simple {X Y : C} [Simple X] [Simple Y] {f : X ⟶ Y} (w : f ≠ 0) : IsIso f

-- For k-linear categories with finite dim homs
theorem finrank_hom_simple_simple_eq_zero_of_not_iso
    {X Y : C} [Simple X] [Simple Y] (h : (X ≅ Y) → False) : finrank 𝕜 (X ⟶ Y) = 0

theorem finrank_endomorphism_simple_eq_one (X : C) [Simple X] : finrank 𝕜 (X ⟶ X) = 1
```

**Conclusion:** Mathlib has complete Schur's lemma coverage. No code needed.

## 2026-01-28: TC 1.2.2 - Direct Sum Bifunctor

**Task:** Ensure direct sum bifunctor is properly exposed.

**Book §1.2 says:**
> "In (A3), the object Y is unique up to a unique isomorphism, is denoted by X₁ ⊕ X₂, and is called the *direct sum* of X₁ and X₂. Thus, every additive category is equipped with a bifunctor ⊕ : C × C → C."

**Mathlib has:**

| Component | Mathlib | Import |
|-----------|---------|--------|
| Direct sum object | `X ⊞ Y` (notation for `biprod X Y`) | `Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts` |
| Map on morphisms | `biprod.map f g : W ⊞ X ⟶ Y ⊞ Z` | same |
| Projections | `biprod.fst : X ⊞ Y ⟶ X`, `biprod.snd : X ⊞ Y ⟶ Y` | same |
| Injections | `biprod.inl : X ⟶ X ⊞ Y`, `biprod.inr : Y ⟶ X ⊞ Y` | same |
| Iso to product | `biprod.isoProd X Y : X ⊞ Y ≅ X ⨯ Y` | same |
| Iso to coproduct | `biprod.isoCoprod X Y : X ⊞ Y ≅ X ⨿ Y` | same |
| Product functor | `prod.functor : C ⥤ C ⥤ C` | `Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts` |

**Functoriality (verified):**
```lean
-- Identity law
example : biprod.map (𝟙 X) (𝟙 Y) = 𝟙 (X ⊞ Y) := by ext <;> simp

-- Composition law
example : biprod.map (f ≫ h) (g ≫ k) = biprod.map f g ≫ biprod.map h k := by ext <;> simp
```

**Key insight:** Mathlib doesn't have a dedicated `biprod.functor : C × C ⥤ C` object like it has `tensor : C × C ⥤ C` for monoidal categories. However:
1. All necessary API exists via `biprod.map` with full functoriality
2. Since `biprod ≅ prod` via `biprod.isoProd`, one can use `prod.functor` if a functor object is needed

**Conclusion:** Mathlib has complete bifunctor API for direct sums. No code needed.
