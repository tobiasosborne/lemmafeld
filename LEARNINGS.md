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

## 2026-01-28: TC 1.3.1-1.3.4 - Abelian Categories (§1.3)

**Created:** `Chapter1/Abelian.lean`

**Book §1.3 covers:**
- Kernel/cokernel definitions
- Definition 1.3.1 (Abelian category via canonical decomposition)
- Definition 1.3.4 (Mono = Ker is 0, Epi = Coker is 0)
- Definition 1.3.5 (Subobjects and quotients)

**Mathlib mapping:**

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Kernel | `kernel f` | `kernel.ι f`, `kernel.condition f`, `kernel.lift` |
| Cokernel | `cokernel f` | `cokernel.π f`, `cokernel.condition f`, `cokernel.desc` |
| Abelian category | `Abelian C` | Combines Preadditive, HasKernels, HasCokernels, IsNormalMono/EpiCategory |
| Coimage = Coker(Ker) | `Abelian.coimage f` | `cokernel (kernel.ι f)` |
| Image = Ker(Coker) | `Abelian.image f` | `kernel (cokernel.π f)` |
| Canonical decomposition | `coimage_image_factorisation f` | `coimage.π f ≫ coimageImageComparison f ≫ image.ι f = f` |
| Coimage ≅ Image | `coimageImageComparison f` is `IsIso` | Key property of abelian categories |
| Mono ↔ Ker = 0 | `kernel.ι_of_mono`, `Preadditive.mono_of_kernel_zero` | |
| Epi ↔ Coker = 0 | `cokernel.π_of_epi`, `Preadditive.epi_of_cokernel_zero` | |
| Mono + Epi → Iso | `isIso_of_mono_of_epi f` | Key abelian property |

**API gotcha:** `mono_of_kernel_ι_eq_zero` in `CategoryTheory.Abelian` has section variable scoping that can cause issues. Use `Preadditive.mono_of_kernel_zero h` instead for clearer application. Similarly for `epi_of_cokernel_π_eq_zero`.

**Freyd-Mitchell embedding (Theorem 1.3.8):** ✅ **IS IN MATHLIB** at `Mathlib.CategoryTheory.Abelian.FreydMitchell`.
  - `FreydMitchell.EmbeddingRing C` — the ring into which we embed
  - `FreydMitchell.functor C` — the full faithful embedding functor C → R-Mod
  - `freyd_mitchell` — the main theorem (full, faithful, preserves finite limits/colimits)

  **CORRECTION (2026-01-28):** Previous agent incorrectly claimed this was not in mathlib. This was wrong.

## 2026-01-28: TC 1.5.2 - Semisimple Objects and Categories

**Task:** Define semisimple objects and semisimple categories (Definition 1.5.1 second part).

**Book Definition 1.5.1:**
- Object X is *semisimple* if it is a direct sum of simple objects
- Category C is *semisimple* if every object is semisimple

**Created:** `Chapter1/Semisimple.lean`

**Mathlib gap confirmed:** Mathlib does NOT have categorical semisimplicity:
- `IsSemisimpleModule R M` exists for modules
- `HomOrthogonal` exists (preliminary to semisimple categories)
- No `Semisimple X` or `SemisimpleCategory C` for general abelian categories

**Implementation:**

```lean
/-- An object X is semisimple if it is isomorphic to a finite biproduct of simple objects. -/
def IsSemisimple (X : C) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (S : ι → C), (∀ i, Simple (S i)) ∧ Nonempty (X ≅ ⨁ S)

/-- A category is semisimple if every object is semisimple. -/
class SemisimpleCategory (C : Type*) [Category C] [HasZeroMorphisms C]
    [HasFiniteBiproducts C] : Prop where
  isSemisimple : ∀ X : C, IsSemisimple X
```

**Key lemmas proved:**
- `Simple.isSemisimple` — simple objects are semisimple
- `IsSemisimple.of_iso` — semisimplicity preserved by isomorphism
- `homOrthogonal_of_simple` — simple objects form a hom orthogonal family

**API notes:**
- `biproductUniqueIso [Unique J] (f : J → C) : ⨁ f ≅ f default` — for single element biproduct
- No `biproduct.isoPEmpty` or `biproduct.isoUnit` exist
- Connecting `biprod X Y` to `biproduct (Sum.elim SX SY)` requires manual construction

**Future work needed:**
- Prove zero object is semisimple (empty biproduct)
- Prove biproduct of semisimple objects is semisimple
- Connect to `IsSemisimpleModule` for ModuleCat

## 2026-01-28: TC 1.5.4 - Finite Length Objects

**Task:** Formalize finite length objects (Definition 1.5.3).

**Book Definition 1.5.3:** An object X has finite length if there exists a filtration
0 = X₀ ⊂ X₁ ⊂ ··· ⊂ Xₙ = X such that Xᵢ₊₁/Xᵢ is simple (Jordan-Hölder series).

**Created:** `Chapter1/FiniteLength.lean`

**Mathlib has:**

| Concept | Mathlib | Import |
|---------|---------|--------|
| Artinian object | `IsArtinianObject X` | `Mathlib.CategoryTheory.Subobject.ArtinianObject` |
| Noetherian object | `IsNoetherianObject X` | `Mathlib.CategoryTheory.Subobject.NoetherianObject` |
| DCC on subobjects | `WellFoundedLT (Subobject X)` | same |
| ACC on subobjects | `WellFoundedGT (Subobject X)` | same |
| Module finite length | `IsFiniteLength R M` | `Mathlib.RingTheory.FiniteLength` |
| Composition series | `CompositionSeries` | `Mathlib.Order.JordanHolder` |
| Jordan-Hölder lattice | `JordanHolderLattice` | `Mathlib.Order.JordanHolder` |

**Key mathlib insight:** For modules, `IsFiniteLength R M ↔ IsNoetherian R M ∧ IsArtinian R M`.

**Implementation:**
- Defined `IsFiniteLengthObject X := IsArtinianObject X ∧ IsNoetherianObject X`
- Defined `FiniteLengthCategory C` class
- Proved: `Simple X → IsFiniteLengthObject X` via:
  - `Simple X → IsSimpleOrder (Subobject X)` (existing instance)
  - `IsSimpleOrder → Finite` (`IsSimpleOrder.instFinite`)
  - `Finite + Preorder → WellFoundedLT/GT` (`Finite.to_wellFoundedLT/GT`)

**Gaps (noted as "Future work" in mathlib):**
1. **Categorical Jordan-Hölder theorem** - mathlib has `JordanHolderLattice` for lattices but not `JordanHolderLattice (Subobject X)` for abelian categories
2. **Categorical length function** - no `length : C → ℕ` for objects of finite length

**API notes:**
- `ObjectProperty.is_of_prop P hX` converts `hX : P X` to `P.Is X` (typeclass)
- `Finite.to_wellFoundedLT` / `Finite.to_wellFoundedGT` give chain conditions for finite types

## 2026-01-28: TC 1.5.5 - Jordan-Hölder Series

**Task:** Formalize Jordan-Hölder series from Definition 1.5.3.

**Book Definition 1.5.3:** A Jordan-Hölder series is a filtration
0 = X₀ ⊂ X₁ ⊂ ··· ⊂ Xₙ = X where each quotient Xᵢ₊₁/Xᵢ is simple.
Multiplicity of a simple object Y is the number of quotients isomorphic to Y.

**Book Theorem 1.5.4:** Jordan-Hölder theorem - any two Jordan-Hölder series
of an object have the same length and multiplicities.

**Book Definition 1.5.5:** The length of X is the length of its Jordan-Hölder series.

**Created:** `Chapter1/JordanHolder.lean`

**Mathlib has (in `Mathlib.Order.JordanHolder`):**

| Concept | Mathlib | Notes |
|---------|---------|-------|
| Abstract framework | `JordanHolderLattice X` | Class for lattices |
| Composition series | `CompositionSeries X` | Series type |
| Series equivalence | `CompositionSeries.Equivalent` | Same length + iso factors |
| Jordan-Hölder theorem | `CompositionSeries.jordan_holder` | Main theorem for lattices |
| Length equality | `CompositionSeries.Equivalent.length_eq` | |

**Mathlib has (in `Mathlib.RingTheory.SimpleModule.Basic`):**

| Concept | Mathlib | Notes |
|---------|---------|-------|
| Module instance | `instJordanHolderLattice : JordanHolderLattice (Submodule R M)` | Full support for modules |

**Gap confirmed:** No `JordanHolderLattice (Subobject X)` for abelian categories.
Would require:
1. Define `IsMaximal` for subobjects (Y ⊂ X maximal ↔ X/Y is simple)
2. Define `Iso` for pairs (quotients isomorphic)
3. Prove second isomorphism theorem for subobjects

## 2026-01-28: TC 1.5.7 - Krull-Schmidt Theorem

**Task:** Formalize Krull-Schmidt theorem (Theorem 1.5.7).

**Book statement:** Any object of finite length admits a unique (up to isomorphism)
decomposition into a direct sum of indecomposable objects.

**Mathlib status:**
- `CategoryTheory.Indecomposable X` exists - definition only
- `indecomposable_of_simple` - simple ⟹ indecomposable
- **NO Krull-Schmidt theorem** in mathlib

**Created:** `Chapter1/KrullSchmidt.lean` with:
- `IndecomposableDecomposition C X` structure (n, components, indecomposable, iso)
- `DecompositionsEquivalent` - equivalence up to permutation and iso
- `KrullSchmidt_Existence` - statement that finite length implies decomposition exists
- `KrullSchmidt_Uniqueness` - statement that decompositions are unique
- `FittingLemma` - statement for indecomposable objects (nilpotent or unit)
- `EndomorphismRingIsLocal` - local ring property for End(X)

**Gap:** Full proof requires:
1. Fitting's Lemma (~50-100 LOC)
2. Local endomorphism ring property (~30-50 LOC)
3. Existence proof by induction on length (~50-100 LOC)
4. Uniqueness proof using exchange lemma (~100-150 LOC)

## 2026-01-28: TC 1.5.6 - Multiplicity Independence

**Task:** Formalize Jordan-Hölder theorem multiplicity independence (Theorem 1.5.4).

**Book Theorem 1.5.4:** "Any two Jordan-Hölder series of X contain any simple object with the same multiplicity."

**Updated:** `Chapter1/JordanHolder.lean`

**Mathlib insight:** The key is `CompositionSeries.Equivalent`:
```lean
def Equivalent s₁ s₂ := ∃ f : Fin s₁.length → Fin s₂.length,
  ∀ i, JordanHolderLattice.Iso (s₁[i], s₁[i+1]) (s₂[f i], s₂[f i + 1])
```

The bijection `f` between indices with `Iso`-respecting property means:
- Factor i of s₁ corresponds to factor f(i) of s₂ with Iso between them
- Since Iso is a relation on factors, equal multiplicities follow from the bijection

**Key lemmas:**
- `CompositionSeries.jordan_holder` — main theorem: same endpoints ⟹ Equivalent
- `CompositionSeries.Equivalent.length_eq` — equivalent series have same length

**Conclusion:** Multiplicity independence is captured by the bijection in `Equivalent`.

## 2026-01-28: Exercise 1.4.3(i) - Baer Sum and Abelian Group on Ext¹

**Task:** Formalize Exercise 1.4.3(i) showing Baer sum defines abelian group on Ext¹(Y, X).

**Created:** `Chapter1/BaerSum.lean`

**Book construction (1.5):**
- Given extensions S, S' of Y by X, form pullback Z̃'' = {(z,z') | π(z) = π'(z')}
- Then Z'' = Z̃''/X_antidiag where X_antidiag = Im((i, -i'))
- This gives S + S' : 0 → X → Z'' → Y → 0

**Mathlib approach:**
- `Ext X Y n` defined via derived category as `SmallShiftedHom`
- `AddCommGroup (Ext X Y n)` instance at line 239 of Ext/Basic.lean
- Abelian group structure comes from additive category structure

**Key mathlib APIs:**
| Book | Mathlib |
|------|---------|
| Ext¹(Y,X) | `Ext X Y 1` (args reversed) |
| Addition | From `AddCommGroup` instance |
| Extension class | `ShortExact.extClass` |

**Note:** Mathlib doesn't explicitly formalize Baer sums - uses derived category approach.

## 2026-01-28: Exercise 1.4.3(ii) - Ext¹ as Derivations

**Task:** Show Ext¹(Y, X) = Der(A, Hom_k(Y, X)) / InnerDer for A-modules.

**Created:** `Chapter1/ExtAsDerivations.lean`

**Book statement:** For A-mod over algebraically closed k:
- Der(A, M) = {D : A → M | D(ab) = aD(b) + D(a)b}
- InnerDer = {D_f : a ↦ [f, a] | f ∈ M}
- Ext¹(Y, X) ≅ Der(A, Hom_k(Y,X)) / InnerDer

**Mathlib has:**
- `Derivation R A M` - derivations with Leibniz rule
- `AddCommMonoid (Derivation R A M)` - additive structure
- `ModuleCat R`, `Abelian (ModuleCat R)`
- `Ext X Y n` for abelian categories

**Mathlib gaps (not formalized):**
1. ~~Inner derivations - no `InnerDerivation` type~~ **→ IMPLEMENTED in ExtAsDerivations.lean**
2. Hochschild cohomology H^n(A, M)
3. The isomorphism Ext¹_A(Y,X) ≅ H¹(A, Hom_k(Y,X))

**Progress (2026-01-28):**
- `InnerDerivation R A M` structure defined (element `f : M`, `toFun`, `toLinearMap`)
- Bimodule structure on Hom_k(Y,X): left via `SMulCommClass`, right via `HomRightSMul`
- ✅ `innerDerivationMap R A M : M →ₗ[R] (A →ₗ[R] M)` — R-linear map f ↦ D_f
- ✅ `InnerDerivations R A M : Submodule R (A →ₗ[R] M)` — range of innerDerivationMap

**Remaining work:** ~50-80 LOC to define quotient and construct explicit isomorphism.

## 2026-01-28: A-bimodule Structure on Hom_k(Y, X)

**Task:** Enhance `ExtAsDerivations.lean` with explicit A-module structures on Hom_k(Y, X).

**Book says:** For A-modules X and Y, Hom_k(Y, X) has an A-bimodule structure:
- Left action: (a · f)(y) = a · f(y)
- Right action: (f · a)(y) = f(a · y)

**Mathlib approach:**

1. **LEFT A-module structure:** Comes automatically from mathlib's `Module S (M →ₛₗ[σ₁₂] M₂)` instance
   - Requires `[SMulCommClass k A X]` for k and A actions to commute on X
   - Then `Module A (Y →ₗ[k] X)` is inferred, with `(a • f) y = a • f y`

2. **RIGHT A-module structure (Aᵐᵒᵖ action):** Defined via precomposition
   - Requires `[SMulCommClass A k Y]` for A and k actions to commute on Y
   - Use `DistribMulAction.toLinearMap k Y a : Y →ₗ[k] Y` for the k-linear map `y ↦ a • y`
   - Then `(f ⬝ a)(y) = f(a • y)` = `f.comp (DistribMulAction.toLinearMap k Y a)`

**Key mathlib APIs:**
- `DistribMulAction.toLinearMap R M s : M →ₗ[R] M` — given `[SMulCommClass S R M]`
- `Module S (M →ₛₗ[σ₁₂] M₂)` instance at `LinearMap/Defs.lean:938`

**Implementation note:** The right action is typically modeled as a left Aᵐᵒᵖ-action.
The function `HomRightSMul (op a) f = f.comp (DistribMulAction.toLinearMap k Y a)`
gives the expected behavior `HomRightSMul (op a) f y = f (a • y)`.

## 2026-01-28: Extension-to-Derivation Construction

**Task:** Given short exact sequence 0 → X → E → Y → 0 of A-modules and k-linear section s,
construct derivation D : A → Hom_k(Y, X) by D(a)(y) = a • s(y) - s(a • y).

**Created:** `Chapter1/ExtDerivationIso.lean`

**Key insight:** For D(a) to be k-linear in y, we need:
- `SMulCommClass A k E` — so `a • (r • e) = r • (a • e)` for r : k, a : A, e : E
- `SMulCommClass A k Y` — similarly for Y

Without these, the proof of `map_smul'` fails since `s(a • (r • y)) ≠ r • s(a • y)` in general.

**Construction:**
1. `extensionDerivationAux s a y = a • s y - s (a • y)` — lands in E
2. `extensionDerivationAux_mem_ker` — proves this is in ker π (using section property)
3. `extensionDerivationToKer` — k-linear map Y → ker π (using SMulCommClass)
4. `extensionDerivation` — compose with equiv.symm to land in X

**Properties proved:**
- `extensionDerivation_one` — D(1) = 0
- `extensionDerivation_add` — D(a+b) = D(a) + D(b)

**Remaining:** Prove Leibniz rule D(ab) = a·D(b) + D(a)·b (bimodule form).

## 2026-01-28: Hochschild H¹ as Quotient Module

**Task:** Define first Hochschild cohomology H¹(A, M) = Der(A, M) / InnerDer(A, M).

**Created:** Added to `Chapter1/ExtAsDerivations.lean`:

1. `HochschildH1 R A M := (A →ₗ[R] M) ⧸ InnerDerivations R A M` — the quotient module
2. `HochschildH1.mk` — quotient map (linear)
3. `HochschildH1.mk_eq_zero` — element is zero iff inner derivation
4. `HochschildH1.mk_eq_mk` — equality iff differ by inner derivation
5. `HochschildH1.eq_bot_iff` — H¹ = 0 iff all linear maps are inner

**Technical notes:**
- Requires `CommRing R` (not just `CommSemiring`) for `HasQuotient` instance
- Import `Mathlib.LinearAlgebra.Quotient.Basic` for `⧸` notation
- `Submodule.mkQ_surjective` useful for working with quotient elements
- `Submodule.Quotient.mk_eq_zero` for membership characterization

**Remaining work for Ex 1.4.3(ii):**
1. Define BimoduleDerivations (maps satisfying Leibniz) as submodule
2. Show InnerDerivations ⊆ BimoduleDerivations
3. ✅ Construct maps: derivations → extensions (SemidirectSMul)
4. Prove the isomorphism Ext¹(Y, X) ≅ H¹(A, Hom_k(Y, X))

## 2026-01-28: Derivation-to-Extension Construction

**Task:** Given derivation D : A → Hom_k(Y, X), construct extension 0 → X → E → Y → 0.

**Created:** Enhanced `Chapter1/ExtDerivationIso.lean`

**Book construction:**
- E = X × Y as k-vector spaces
- A-action: a · (x, y) = (a · x + D(a)(y), a · y)

**Key mathlib APIs:**
- `LinearMap.inl k X Y : X →ₗ[k] X × Y` — inclusion into first factor
- `LinearMap.inr k X Y : Y →ₗ[k] X × Y` — inclusion into second factor
- `LinearMap.fst k X Y : X × Y →ₗ[k] X` — first projection
- `LinearMap.snd k X Y : X × Y →ₗ[k] Y` — second projection
- Import: `Mathlib.LinearAlgebra.Prod`

**Module property proofs require:**
- `D(1) = 0` for `one_smul`
- `D(ab) = a • D(b) + D(a) ∘ (b • ·)` (bimodule Leibniz) for `mul_smul`
- `D(a + b) = D(a) + D(b)` for `add_smul`

**Proof techniques:**
- For `Prod.mk = Prod.mk` goals, use `Prod.mk.injEq` to split into components
- `Prod.mk_add_mk` useful for simplifying `(a, b) + (c, d) = (a + c, b + d)`
- After `simp ... [Prod.mk.injEq]`, goals may become `_ ∧ True` — use `trivial` not `rfl`
- Use `mul_smul` (unqualified) for module associativity `(a * b) • x = a • (b • x)`

## 2026-01-28: Ex 1.4.3(ii) Round-Trip Proof

**Task:** Prove the round-trip derivation → extension → derivation = id.

**Key insight:** Starting from derivation D : A → Hom_k(Y, X):
1. Build semi-direct product E = X × Y with action a • (x,y) = (a•x + D(a)(y), a•y)
2. Use canonical section s(y) = (0, y)
3. Extract D'(a)(y) = fst(a • s(y) - s(a • y))

Calculation shows D' = D exactly:
- s(y) = (0, y)
- a • s(y) = (a•0 + D(a)(y), a•y) = (D(a)(y), a•y)
- s(a • y) = (0, a•y)
- a • s(y) - s(a•y) = (D(a)(y), 0)
- fst gives D(a)(y) ✓

**Implementation:**
- `semidirectExtractDerivation` — extraction function
- `semidirectExtractDerivation_eq` — proves it equals D(a)(y)
- `derivation_roundtrip` — proves the full round-trip

**Completed:**
- ✅ Proved extension → derivation → extension gives k-linear equivalent extension (lemmafeld-85xg)

**Remaining for full isomorphism:**
- Show the k-linear equivalence is actually A-linear (requires D satisfying Leibniz)
- Show ExtensionEquiv from extensionSemidirectEquiv (commutes with maps)

## 2026-01-28: ExtensionEquiv Structure

**Purpose:** Define when two extensions 0 → X → E → Y → 0 and 0 → X → E' → Y → 0 represent
the same element of Ext¹(Y, X).

**Definition:** `ExtensionEquiv i π i' π'` consists of:
- `iso : E ≃ₗ[A] E'` — A-linear isomorphism
- `comm_incl : iso ∘ i = i'` — commutes with inclusions
- `comm_proj : π' ∘ iso = π` — commutes with projections

**Mathlib note:** Mathlib doesn't have a standard "extension equivalence" type. This is
specific to the Yoneda Ext interpretation (extensions as representing Ext¹ elements).

## 2026-01-28: Extension Round-Trip Proof

**Task:** Prove extension → derivation → extension gives equivalent extension.

**Key construction:**
Given extension 0 → X → E → Y → 0 with section s : Y →ₗ[k] E:
1. `extensionToSemidirect` : E →ₗ[k] X × Y via e ↦ (equiv⁻¹(e - s(π(e))), π(e))
2. `semidirectToExtension` : X × Y →ₗ[k] E via (x, y) ↦ equiv(x) + s(y)

**Helper lemma:**
- `diff_mem_ker` — proves e - s(π(e)) ∈ ker(π) using section property

**Key proofs:**
- `extensionToSemidirect_semidirectToExtension` — round-trip X × Y → E → X × Y = id
- `semidirectToExtension_extensionToSemidirect` — round-trip E → X × Y → E = id
- `extensionSemidirectEquiv` — k-linear equivalence E ≃ₗ[k] X × Y
- `extension_roundtrip` — existence theorem with properties

**Proof techniques:**
- For `map_add'` with submodule elements: prove helper `heq` showing elements equal
  after simplification, then `simp only [heq, map_add]`
- For `map_smul'`: need `RingHom.id_apply` to simplify `(RingHom.id k) r` to `r`
- Use `LinearMap.map_smul_of_tower` for k-smul through A-linear maps

**Note:** This proves k-linear equivalence. Full A-linear equivalence requires showing
the maps respect the A-action, which needs the derivation D to satisfy Leibniz rule.

## 2026-01-28: Ex 1.4.3(ii) A-Linearity Gap

**Task:** Complete the isomorphism Ext¹(Y, X) ≅ H¹(A, Hom_k(Y, X)).

**Status:** k-linear round-trips proved, but A-linearity gap remains.

**Gap identified:** The k-linear equivalence `extensionSemidirectEquiv : E ≃ₗ[k] X × Y` needs
to be shown A-linear (respecting semi-direct action) to get a true `ExtensionEquiv`.

**Key insight:** For A-linearity, the equivalence `X ≃ ker π` must be A-linear (not just k-linear):
- If `i : X →ₗ[A] E` is the A-linear inclusion with range = ker π
- Then `equiv : X ≃ₗ[A] ker π` induced by `i` is A-linear
- The decomposition `a • e - s(a • π(e)) = a • (e - s(π(e))) + (a • s(π(e)) - s(a • π(e)))`
  shows the first component transforms correctly under A-action

**API challenge:** Converting between A-linear and k-linear structures requires:
- `LinearMap.restrictScalars k : (M →ₗ[A] N) → (M →ₗ[k] N)` for scalar restriction
- `LinearMap.CompatibleSMul M N k A` for the instances to work together

**Created issue:** lemmafeld-5rat for the A-linearity proof (~50 LOC remaining)

## 2026-01-28: Ex 1.4.3(ii) A-Linearity Gap — RESOLVED

**Resolution:** The A-linearity gap has been closed in lemmafeld-5rat.

**Key techniques used:**
1. **IsScalarTower k A X**: Establishes k-scalars work through A-scalars
2. **apply_fun equiv using equiv.injective**: Move proofs to Subtype level
3. **smul_one_smul A r x**: Rewrite `r • x` as `(r • 1) • x` for A-algebra manipulation
4. **Explicit membership proofs**: Use `have hmem : _ ∈ ker π := ...` for subtype construction

**Pattern for k-scalar through A-linear equiv:**
```lean
-- When equiv : X ≃ₗ[A] ker π is A-linear, handle k-scalar as:
have h : equiv (r • equiv.symm ⟨...⟩) = r • ⟨...⟩ := by
  rw [← smul_one_smul A r (equiv.symm _), LinearEquiv.map_smul,
      LinearEquiv.apply_symm_apply, smul_one_smul]
```

**API gotchas:**
- `LinearEquiv.map_smul_of_tower` doesn't exist — use `smul_one_smul` rewriting instead
- Subtype equality proofs: use `ext` after `apply_fun` to access underlying element
- `abel` tactic works well after `simp only` on Submodule.coe operations

## 2026-01-29: Fitting's Lemma Chain Stabilization

**Task:** Prove Fitting's Lemma for abelian categories.

**Key discoveries:**

1. **End X multiplication is reversed**: In `End X`, multiplication is `x * y = y ≫ x`.
   So `f^m * f^k = f^k ≫ f^m` (not `f^m ≫ f^k`).

2. **Powers commute via `pow_mul_comm`**: `f^m * f^k = f^k * f^m` always holds for
   powers of the same element, so both orderings work.

3. **Chain monotonicity proofs:**
   - Kernel chain: Use `pow_add_eq_comp` form `f^(m+k) = f^m ≫ f^k` so kernel condition applies
   - Image chain: Use `pow_add_eq_comp'` form `f^(m+k) = f^k ≫ f^m` so imageSubobject_comp_le applies

**Implemented in `Chapter1/KrullSchmidt.lean`:**
- `pow_comp_comm` — powers of an endomorphism compose in either order
- `pow_add_eq_comp` — `f^(m+k) = f^m ≫ f^k`
- `pow_add_eq_comp'` — `f^(m+k) = f^k ≫ f^m`
- `kernelSubobject_le_of_le` — kernel chain is monotone
- `imageSubobject_le_of_ge` — image chain is antitone
- `fitting_lemma` — statement with sorry (full proof needs decomposition step)

**Gap remaining:** The decomposition `X = Ker(f^n) ⊕ Im(f^n)` at stabilization requires
showing that `f^n` restricts to an isomorphism on `Im(f^n)` when both chains stabilize.
This needs ~100 additional LOC to formalize properly.

## 2026-01-29: Chain Stabilization API in Mathlib

**Task:** Use mathlib's chain stabilization lemmas for Fitting's Lemma.

**Key mathlib lemmas found:**

1. `monotone_chain_condition_of_isNoetherianObject` — For `IsNoetherianObject X` and monotone
   `f : ℕ →o Subobject X`, gives `∃ n, ∀ m ≥ n, f n = f m`.

2. `antitone_chain_condition_of_isArtinianObject` — For `IsArtinianObject X` and monotone
   `f : ℕ →o (Subobject X)ᵒᵈ`, gives stabilization. (Requires wrapping antitone as monotone in dual.)

**Pattern for antitone chain stabilization:**
```lean
lemma imageSubobject_stabilizes [IsArtinianObject X] :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → imageSubobject (f ^ n) = imageSubobject (f ^ m) := by
  have hf : Antitone (fun n => imageSubobject (f ^ n)) := imageSubobject_antitone f
  have hf' : Monotone (fun n => OrderDual.toDual (imageSubobject (f ^ n))) := hf
  obtain ⟨n, hn⟩ := antitone_chain_condition_of_isArtinianObject ⟨_, hf'⟩
  refine ⟨n, fun m hm => ?_⟩
  have heq := hn m hm
  simp only [OrderHom.coe_mk, OrderDual.toDual_inj] at heq
  exact heq
```

**Key insight:** `OrderDual.toDual_inj` simplifies equality in the order dual to equality in
the original order. The `simp` lemma handles the unwrapping.

**API notes:**
- `IsNoetherianObject X` gives `WellFoundedGT (Subobject X)` (ACC)
- `IsArtinianObject X` gives `WellFoundedLT (Subobject X)` (DCC)
- `IsFiniteLengthObject X = IsArtinianObject X ∧ IsNoetherianObject X`

## 2026-01-29: Fitting Decomposition Proof Strategy

**Task:** Prove Ker(f^n) ⊓ Im(f^n) = ⊥ and Ker(f^n) ⊔ Im(f^n) = ⊤ at chain stabilization.

**Key helper lemma discovered:**
```lean
/-- If a subobject's arrow is zero, the subobject equals ⊥. -/
lemma subobject_eq_bot_of_arrow_eq_zero (A : Subobject X) (h : A.arrow = 0) : A = ⊥ := by
  apply Subobject.eq_of_comm (isoZeroOfMonoEqZero h ≪≫ Subobject.botCoeIsoZero.symm)
  calc _ ≫ (⊥ : Subobject X).arrow = _ ≫ 0 := by rw [Subobject.bot_arrow]
    _ = 0 := by simp
    _ = A.arrow := h.symm
```

**Proof strategy for inf = ⊥:**
1. Show `(K ⊓ I).arrow ≫ f^n = 0` (factors through kernel, kernel condition gives zero)
2. `(K ⊓ I).arrow` factors through `imageSubobject (f^n)` (from `inf_le_right`)
3. At stabilization, `f^n|_{Im(f^n)}` is an isomorphism (Im(f^n) = Im(f^(2n)) means surjective endo)
4. Composition with zero through an iso means the pre-composition is zero
5. Hence `(K ⊓ I).arrow = 0`, so `K ⊓ I = ⊥`

**Key API:**
- `inf_le_left : K ⊓ I ≤ K` → factorization through K
- `inf_le_right : K ⊓ I ≤ I` → factorization through I
- `Subobject.ofLE_arrow : (A ⊓ B).arrow = ofLE _ _ h ≫ A.arrow`
- `kernelSubobject_arrow_comp : K.arrow ≫ f^n = 0`
- `isoZeroOfMonoEqZero` — mono arrow = 0 implies source ≅ 0

**Gap:** Need to formalize "f^n restricted to Im(f^n) is an isomorphism at stabilization". This requires:
- Showing the restriction is surjective (from Im(f^n) = Im(f^(2n)))
- Showing surjective endo of finite length object is iso (or use direct argument)

**Proof strategy for sup = ⊤:**
1. Need to show `K ⊔ I = ⊤`, i.e., every element is sum of kernel and image parts
2. For any x, f^n(x) ∈ Im(f^n) = Im(f^(2n))
3. So f^n(x) = f^(2n)(y) for some y (from stabilization surjectivity)
4. Then x - f^n(y) ∈ Ker(f^n) (since f^n(x - f^n(y)) = f^n(x) - f^(2n)(y) = 0)
5. Thus x = (x - f^n(y)) + f^n(y) ∈ K + I

**Gap:** Need categorical formulation of "for y' in Im(f^n), exists z with f^n(z) = y'".

**Created issues:**
- lemmafeld-zy7n: Prove inf = ⊥ (~30 LOC)
- lemmafeld-c5gz: Prove sup = ⊤ (~30 LOC)
- Both block lemmafeld-txf9 (Fitting's Lemma completion)
