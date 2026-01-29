# Handoff: 2026-01-29

## Completed This Session (Current)

- **lemmafeld-zy7n (Prove Fitting decomposition: inf = ⊥) - BLOCKED**:
  - Investigated proof of `kernelSubobject_inf_imageSubobject_eq_bot`
  - **Key finding:** Classical module argument requires "finding preimages" under surjective maps
  - In categories, epi ≠ surjective in the element-wise sense
  - Attempted approach: show h = I.arrow ≫ factorThru(f^n) : I → I is iso
    - h is epi ✓ (from image stabilization)
    - h is mono ⟺ K ∩ I = 0 (circular!)
  - **Created research issue:** lemmafeld-hyvg (epi endo on Noetherian → mono)
  - **Blocker:** Need categorical lemma not in mathlib
  - See LEARNINGS.md "Fitting Decomposition Categorical Proof Gap" for full analysis

## Previous Session

- **lemmafeld-zy7n (Prove Fitting decomposition: inf = ⊥) - PARTIAL**:
  - Added `subobject_eq_bot_of_arrow_eq_zero` helper — PROVED
  - Added `inf_arrow_comp_pow_eq_zero` — PROVED: (K ⊓ I).arrow ≫ f^n = 0
  - Main lemma reduced to showing `(K ⊓ I).arrow = 0`
  - File at 172 LOC (under 200 limit), builds with sorry

## Previous Session

- **lemmafeld-txf9 (Fitting's Lemma Decomposition) - RESEARCH COMPLETE**:
  - Developed proof strategy for `kernelSubobject_inf_imageSubobject_eq_bot` and `_sup_..._eq_top`
  - Discovered key helper lemma: `subobject_eq_bot_of_arrow_eq_zero`
  - File at 198 LOC (at limit, cannot add proofs without exceeding)
  - **Created sub-issues:**
    - lemmafeld-zy7n: Prove inf = ⊥ (~30 LOC) — with detailed proof strategy
    - lemmafeld-c5gz: Prove sup = ⊤ (~30 LOC) — with detailed proof strategy
    - Both now block lemmafeld-txf9
  - **Key insight:** Proof requires showing f^n restricted to Im(f^n) is iso at stabilization
  - See LEARNINGS.md "Fitting Decomposition Proof Strategy" for full details

## Previous Session

- **lemmafeld-txf9 (Fitting's Lemma Decomposition) - PARTIAL**: Enhanced `Chapter1/FittingLemma.lean`
  - `kernelSubobject_stabilizes` — PROVED: kernel chain stabilizes (Noetherian)
  - `imageSubobject_stabilizes` — PROVED: image chain stabilizes (Artinian)
  - `kernelSubobject_stable`, `imageSubobject_stable` — helper lemmas
  - `kernelSubobject_inf_imageSubobject_eq_bot` — outlined with proof sketch (sorry)
  - `kernelSubobject_sup_imageSubobject_eq_top` — outlined with proof sketch (sorry)
  - File is 198 LOC (under 200 guideline)

## Previous Session

- **lemmafeld-hm49 (Hygiene: Split KrullSchmidt.lean) - COMPLETE**: Split 252 LOC file into 2 files
  - `Chapter1/KrullSchmidt.lean` (162 LOC): Indecomposable recap + Krull-Schmidt statements
  - `Chapter1/FittingLemma.lean` (126 LOC): Chain stabilization + Fitting's Lemma
  - Both files ≤200 LOC, all build successfully

## Previous Session

- **lemmafeld-32vi (Fitting's Lemma) - PARTIAL**: Enhanced `Chapter1/KrullSchmidt.lean`
  - `pow_comp_comm` — powers of an endomorphism compose in either order
  - `pow_add_eq_comp` — f^(m+k) = f^m ≫ f^k (for kernel chain)
  - `pow_add_eq_comp'` — f^(m+k) = f^k ≫ f^m (for image chain)
  - `kernelSubobject_le_of_le` — Ker(f^m) ≤ Ker(f^n) when m ≤ n (PROVED)
  - `kernelSubobject_mono` — kernel chain is monotone (PROVED)
  - `imageSubobject_le_of_ge` — Im(f^n) ≤ Im(f^m) when m ≤ n (PROVED)
  - `imageSubobject_antitone` — image chain is antitone (PROVED)
  - `fitting_lemma` — main theorem statement (sorry - needs decomposition step)
  - **Key insight**: End X multiplication is `x * y = y ≫ x` (reversed)

## Previous Session

- **lemmafeld-ehs6 (Hygiene: Split ExtDerivationIso) - COMPLETE**: Split 665 LOC file into 4 files
  - `SemidirectProduct.lean` (169 LOC): DerivationToExtension + D→E→D roundtrip
  - `ExtDerivationConstruction.lean` (187 LOC): ExtensionToDerivation + k-linear E→D→E roundtrip
  - `ExtALinear.lean` (106 LOC): A-linear compatibility theorems
  - `ExtDerivationIso.lean` (126 LOC): ExtensionEquiv + IsomorphismStatement
  - All files ≤200 LOC, all build successfully

## Previous Session

- **lemmafeld-izzr (Ex 1.4.3ii Isomorphism) - COMPLETE**: Finalized isomorphism theorem
  - `ext1_iso_hochschildH1_components` with documentation of Φ and Ψ maps
  - States: Φ∘Ψ = id via `derivation_roundtrip`, Ψ∘Φ ~ id via A-linearity lemmas

## Previous Session

- **lemmafeld-5rat (Ex 1.4.3ii A-Linear Equivalence) - COMPLETE**: Enhanced `Chapter1/ExtDerivationIso.lean`
  - Added `ALinearRoundTrip` section with A-linear compatibility theorems
  - `extensionToSemidirect_A_linear_aux` — core decomposition
  - `extensionToSemidirect_respects_action` — compatibility with semi-direct A-action
  - Key insight: A-linear equiv enables A-action compatibility

## Earlier Session

- **lemmafeld-izzr (Ex 1.4.3ii Isomorphism) - PARTIAL**: Earlier work
  - Created sub-issue lemmafeld-5rat for A-linearity proof
  - Created hygiene issue lemmafeld-ehs6 (file is >200 LOC guideline)

## Previous Session

- **lemmafeld-85xg (Ex 1.4.3ii Extension Round-Trip)**: Enhanced `Chapter1/ExtDerivationIso.lean`
  - `diff_mem_ker` — helper: e - s(π(e)) ∈ ker(π)
  - `extensionToSemidirect` — k-linear map E → X × Y via e ↦ (equiv⁻¹(e - s(π(e))), π(e))
  - `semidirectToExtension` — k-linear inverse X × Y → E via (x, y) ↦ equiv(x) + s(y)
  - `extensionToSemidirect_semidirectToExtension` — **PROVED**: round-trip is id
  - `semidirectToExtension_extensionToSemidirect` — **PROVED**: other round-trip is id
  - `extensionSemidirectEquiv` — k-linear equivalence E ≃ₗ[k] X × Y
  - `extension_roundtrip` — main theorem: equivalence exists with projection compatibility
  - File is now 476 LOC (hygiene issue lemmafeld-ehs6 still open)

## Previous Session

- **lemmafeld-izzr (Ex 1.4.3ii Isomorphism) - PARTIAL**: Enhanced `Chapter1/ExtDerivationIso.lean`
  - `semidirectExtractDerivation` — extraction function D'(a)(y) from semi-direct product
  - `derivation_roundtrip` — **PROVED**: D → E → D = D (one direction of isomorphism)
  - `ExtensionEquiv` — structure for equivalence of extensions
  - `ExtensionEquiv.refl` — reflexivity of extension equivalence
  - `ext1_iso_hochschildH1` — statement of main theorem (proof placeholder)
  - Created sub-issue lemmafeld-85xg for extension round-trip E→D→E ~ E
  - Created hygiene issue lemmafeld-ehs6 (file is 353 LOC > 200 guideline)

## Previous Session

- **lemmafeld-sqw7 (Ex 1.4.3ii Derivation → Extension)**: Enhanced `Chapter1/ExtDerivationIso.lean`
  - `SemidirectSMul D a p = (a • p.1 + D(a)(p.2), a • p.2)` — modified A-action from derivation
  - `SemidirectSMul.one_smul` — 1 acts as identity when D(1) = 0
  - `SemidirectSMul.mul_smul'` — associativity when D satisfies bimodule Leibniz rule
  - `SemidirectSMul.smul_add`, `SemidirectSMul.add_smul` — distributivity lemmas
  - `SemidirectInclusion`, `SemidirectProjection`, `SemidirectSection` — k-linear maps
  - `Semidirect_exact` — ker(projection) = range(inclusion)
  - Added import `Mathlib.LinearAlgebra.Prod` for `LinearMap.inl/inr/fst/snd`

## Earlier Session

- **lemmafeld-yqib (Ex 1.4.3ii Hochschild H¹)**: Enhanced `Chapter1/ExtAsDerivations.lean`
  - `HochschildH1 R A M := (A →ₗ[R] M) ⧸ InnerDerivations R A M` — quotient module
  - `HochschildH1.mk` — quotient linear map
  - `HochschildH1.mk_eq_zero`, `mk_eq_mk` — equality characterization lemmas
  - `HochschildH1.eq_bot_iff` — H¹ vanishes iff all maps are inner

## Earlier Session

- **lemmafeld-2vyn (Ex 1.4.3ii Extension → Derivation)**: Created `Chapter1/ExtDerivationIso.lean`
  - `extensionDerivationAux s a y = a • s(y) - s(a • y)` — auxiliary function
  - `extensionDerivationAux_mem_ker` — lands in ker π when s is section
  - `extensionDerivationToKer` — k-linear map Y → ker π for fixed a
  - `extensionDerivation` — full map A → (Y →ₗ[k] X)
  - `extensionDerivation_one`, `extensionDerivation_add` — basic properties
  - Requires `[SMulCommClass A k E]`, `[SMulCommClass A k Y]` for k-linearity

- **lemmafeld-oti7 (Ex 1.4.3ii InnerDerivations Submodule)**: Enhanced `Chapter1/ExtAsDerivations.lean`
  - `innerDerivationMap R A M : M →ₗ[R] (A →ₗ[R] M)` — R-linear map f ↦ D_f
  - `InnerDerivations R A M : Submodule R (A →ₗ[R] M)` — range of innerDerivationMap
  - `mem_innerDerivations`, `mem_innerDerivations_iff` — membership lemmas
  - Updated documentation to reflect completed implementation

## Previous Session

- **TC 1.5.7 Krull-Schmidt**: Created `Chapter1/KrullSchmidt.lean`
  - `IndecomposableDecomposition C X` structure for decomposition into indecomposables
  - `DecompositionsEquivalent` - equivalence up to permutation
  - `KrullSchmidt_Existence`, `KrullSchmidt_Uniqueness`, `KrullSchmidt_Theorem` statements
  - `FittingLemma`, `EndomorphismRingIsLocal` - key supporting statements

- **Ex 1.4.3(ii) InnerDerivation**: Added `InnerDerivation R A M` structure to `Chapter1/ExtAsDerivations.lean`
  - `toFun`: `a ↦ a • f - MulOpposite.op a • f`
  - `toLinearMap`: R-linear map with proper scalar tower conditions
  - CoeFun instance and simp lemmas

- **Ex 1.4.3(ii) BimoduleStructure**: Enhanced bimodule structure section
  - Left A-module structure on Hom_k(Y, X) using `[SMulCommClass k A X]`
  - Right Aᵐᵒᵖ-action via `HomRightSMul` using `DistribMulAction.toLinearMap`
  - Both actions verified with `rfl` proofs

## Earlier Session

- **lemmafeld-sxnt (Ex 1.4.3i)**: Created `Chapter1/BaerSum.lean` with Baer sum / AddCommGroup (Ext X Y 1)
- **lemmafeld-wut0 (Ex 1.4.3ii)**: Created `Chapter1/ExtAsDerivations.lean` with Ext¹ ≅ Der/InnerDer docs

## Previous Session

- **lemmafeld-bgj0 (TC 1.5.6)**: Updated `Chapter1/JordanHolder.lean` with multiplicity independence section

## Earlier Session

- **lemmafeld-i48r (TC 1.5.5)**: Created `Chapter1/JordanHolder.lean` with Jordan-Hölder series formalization

## Earlier Session

- **lemmafeld-g16j (TC 1.5.4)**: Created `Chapter1/FiniteLength.lean` with finite length object definitions

## Previous Session

- **lemmafeld-dy0 (TC 1.5.2)**: Created `Chapter1/Semisimple.lean` with semisimple object/category definitions

## Earlier Session

- **lemmafeld-457 (TC 1.5.1)**: Created `Chapter1/Simple.lean` with §1.5 simple objects
- **lemmafeld-vxvh (TC 1.5.3)**: Covered by Simple.lean (Schur's Lemma via isIso_of_hom_simple)

## Earlier Session

- **lemmafeld-ada (TC 1.4.1)**: Created `Chapter1/ExactSequences.lean` with §1.4 exact sequences
- **lemmafeld-011 (TC 1.4.2)**: Covered by ExactSequences.lean (short exact, fIsKernel, gIsCokernel)
- **lemmafeld-0ni (TC 1.4.3)**: Covered by ExactSequences.lean (Ext¹ via derived functors noted)
- **lemmafeld-ce1 (TC 1.4.4)**: Covered by ExactSequences.lean (addition from ModuleCat structure)

## Completed Previous Session

- **CORRECTION**: Fixed Abelian.lean to properly import and document Freyd-Mitchell embedding
- **CLAUDE.md**: Added "Escalation Failure Mode" section

## Earlier Sessions

- **lemmafeld-c8w (TC 1.1.1)**: Created `Chapter1/Basic.lean` documenting §1.1 categorical prerequisites.
- **lemmafeld-97w (TC 1.1.2)**: Created `Chapter1/Notation.lean` with notation conventions and examples.
- **lemmafeld-xow (TC 1.1.3)**: Created `Chapter1/SmallCategories.lean` with LocallySmall/EssentiallySmall APIs.
- **lemmafeld-uth (TC 1.2.1)**: Created `Chapter1/Additive.lean` with §1.2 additive/k-linear category mappings.
- **lemmafeld-8e7 (TC 1.2.2)**: Created `Chapter1/DirectSum.lean` with explicit direct sum bifunctor.
- **lemmafeld-zr5 (TC 1.2.3)**: Closed - covered by `Chapter1/Additive.lean` (Linear R C documentation).
- **lemmafeld-6aa (TC 1.3.1)**: Created `Chapter1/Abelian.lean` with §1.3 abelian category formalization.
- **lemmafeld-1ac (TC 1.3.2)**: Closed - covered by `Chapter1/Abelian.lean` (kernel/cokernel APIs).
- **lemmafeld-ua8 (TC 1.3.3)**: Closed - covered by `Chapter1/Abelian.lean` (canonical decomposition).
- **lemmafeld-uji (TC 1.3.4)**: Closed - covered by `Chapter1/Abelian.lean` (image factorization).

## Current State

- **Chapter1/Basic.lean** — §1.1 concepts (identity functor, equivalence, opposite category)
- **Chapter1/Notation.lean** — Notation comparison table + examples
- **Chapter1/SmallCategories.lean** — LocallySmall/EssentiallySmall API documentation
- **Chapter1/Additive.lean** — §1.2 Preadditive, HasZeroObject, HasBinaryBiproducts, Linear R C
- **Chapter1/DirectSum.lean** — §1.2 direct sum bifunctor ⊕ : C × C → C
- **Chapter1/Abelian.lean** — §1.3 Abelian categories (kernel, cokernel, canonical decomposition, mono/epi)
- **Chapter1/ExactSequences.lean** — §1.4 Exact sequences (ShortComplex, ShortExact, Ext¹ notes)
- **Chapter1/BaerSum.lean** — Ex 1.4.3(i) Baer sum, AddCommGroup (Ext X Y n)
- **Chapter1/ExtAsDerivations.lean** — Ex 1.4.3(ii) Ext¹ as derivations (InnerDerivation, HomRightSMul)
- **Chapter1/Simple.lean** — §1.5 Simple objects (Simple X, Schur's Lemma, Indecomposable)
- **Chapter1/Semisimple.lean** — §1.5 Semisimple objects (IsSemisimple X, SemisimpleCategory C)
- **Chapter1/FiniteLength.lean** — §1.5 Finite length (IsFiniteLengthObject, FiniteLengthCategory)
- **Chapter1/JordanHolder.lean** — §1.5 Jordan-Hölder series + multiplicity independence (§1.5.6)
- **Chapter1/KrullSchmidt.lean** — §1.5 Krull-Schmidt theorem (statements, gaps noted)
- All fourteen files build successfully

## Next Steps

1. TC 1.5.7-1.5.8: Krull-Schmidt theorem, Grothendieck group
2. TC 1.6.x: Projective and injective objects
3. Chapter 2: Monoidal categories foundations

## Known Issues / Gotchas

- **A-linearity gap in Ex 1.4.3(ii)**: RESOLVED in lemmafeld-5rat. Key insight: use `IsScalarTower k A X`
  and require `equiv : X ≃ₗ[A] ker π` (A-linear). Then scalar tower manipulation with
  `smul_one_smul` handles k-scalar through A-linear equiv.
- `bd ready` returns later chapter issues first - prioritize Chapter 1-2 foundations
- Avoid `abbrev X := @SomeClass` with universe polymorphism - use comments instead
- Universe variables need explicit `universe w` declaration in sections that use them
- Import `Mathlib.CategoryTheory.Skeletal` (not `Skeleton`) for Skeleton type
- `Linear.smul_comp` takes 6 arguments: `X Y Z r f g`
- `F.map_add` is a term (no explicit args), not a function to be applied
- `F.mapBiprod` requires `[PreservesBinaryBiproduct X Y F]` instance assumption
- For zero object notation `(0 : C)`, need `open scoped ZeroObject`
- `biprod.braiding_map_braiding` is for general maps; use `simp` for σ ∘ σ = id
- `mono_of_kernel_ι_eq_zero` in Abelian namespace conflicts with variable scoping - use `Preadditive.mono_of_kernel_zero` instead
- `epi_of_cokernel_π_eq_zero` similarly - use `Preadditive.epi_of_cokernel_zero` instead
- `ShortExact.isIso_f_iff` not `isIso_f` — returns `IsIso S.f ↔ IsZero S.X₃`
- `isIso_of_hom_simple` requires `[HasKernels C]` — add this or use `[Abelian C]`
- `biproductUniqueIso` gives `⨁ f ≅ f default` for unique index type (use with Unit)
- No `biproduct.isoPEmpty` or `biproduct.isoUnit` — use `biproductUniqueIso` for single element
- `IsArtinianObject X` is `ObjectProperty.Is isArtinianObject X` — use `ObjectProperty.is_of_prop` to construct from `WellFoundedLT (Subobject X)`
- `Finite.to_wellFoundedLT` / `Finite.to_wellFoundedGT` require explicit type annotation: `(inferInstance : WellFoundedLT _)`
- For left A-module on `(Y →ₗ[k] X)`: need `[SMulCommClass k A X]` (k, A commute on X)
- For right A-module on `(Y →ₗ[k] X)`: need `[SMulCommClass A k Y]` (A, k commute on Y) for `DistribMulAction.toLinearMap`

## Files Modified

- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/Basic.lean` — §1.1 formalization
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/Notation.lean` — Notation conventions
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/SmallCategories.lean` — Size conditions
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/Additive.lean` — §1.2 additive categories
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/DirectSum.lean` — §1.2 direct sum bifunctor
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/Abelian.lean` — §1.3 abelian categories
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/ExactSequences.lean` — §1.4 exact sequences
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/BaerSum.lean` — Ex 1.4.3(i) (NEW)
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/ExtAsDerivations.lean` — Ex 1.4.3(ii) (NEW)
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/Simple.lean` — §1.5 simple objects
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/Semisimple.lean` — §1.5 semisimple objects
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/FiniteLength.lean` — §1.5 finite length objects
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/JordanHolder.lean` — §1.5 Jordan-Hölder series (NEW)
