# Handoff: 2026-01-31 (TC 1.7.1 Complete)

## Completed This Session

- **lemmafeld-4rdp**: TC 1.7.1 - Explicit differential formulas d₁,d₂,d₃,d₄ — COMPLETE
  - Created `Chapter1/GroupCohomology.lean` with book ↔ mathlib correspondence
  - Key mathlib API: `inhomogeneousCochains.d_hom_apply` gives general formula
  - Documented the 4 explicit differential formulas from Example 1.7.1
  - References bar resolution `Rep.barResolution k G`

## Current State

**Build:** Passing (`lake build` succeeds)

**Chapter 1 §1.7 Coverage:**
- Example 1.7.1 (d₁-d₄ formulas): COMPLETE
- Example 1.7.2 (H⁰, H¹): Not started
- Remark 1.7.3 (non-abelian 1-cocycles): Not started
- Example 1.7.4 (ℤ/nℤ cohomology): Not started
- Exercise 1.7.5 (ring structure): Not started

## Next Steps (SECTION ORDER)

### 1. TC 1.7.2: H⁰ and H¹ for trivial action
- Issue: `lemmafeld-rm4u`
- Book says: H⁰(G,A) = A^G, H¹(G,A) = Hom(G,A) for trivial action

### 2. TC 1.7.3: Non-abelian 1-cocycles remark
- Issue: `lemmafeld-wlki`

### 3. TC 1.7.4: ℤ/nℤ cohomology computation
- Issue: `lemmafeld-j2mh`

### 4. TC 1.7.5: Ring structure on H*(ℤ/nℤ, ℤ)
- Issue: `lemmafeld-7jnu`

## Files Modified

- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/GroupCohomology.lean` — NEW (~100 LOC)
  - Explicit differential formulas d₁, d₂, d₃, d₄ for group cohomology
  - Book ↔ mathlib correspondence for inhomogeneous cochains
  - References to bar resolution and `groupCohomology` functor
- `docs/learnings/chapter1/derived_functors.md` — Updated with Example 1.7.1 section

## Notes

- Mathlib's `inhomogeneousCochains.d_hom_apply` gives the general formula
- Universe polymorphism: `Rep k G` requires k, G in same universe
- Low-degree group cohomology theorems in `GroupCohomology.LowDegree` module
