# Handoff: 2026-01-28

## Completed This Session (Current)

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
- All seven files build successfully

## Next Steps

1. TC 1.5.x: Simple objects, Jordan-Hölder theorem
2. TC 1.6.x: Projective and injective objects
3. TC 1.7.x: Higher Ext groups

## Known Issues / Gotchas

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

## Files Modified

- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/Basic.lean` — §1.1 formalization
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/Notation.lean` — Notation conventions
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/SmallCategories.lean` — Size conditions
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/Additive.lean` — §1.2 additive categories
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/DirectSum.lean` — §1.2 direct sum bifunctor
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/Abelian.lean` — §1.3 abelian categories
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/ExactSequences.lean` — §1.4 exact sequences (NEW)
