# Handoff: 2026-01-31 (§1.7 Group Cohomology Progress)

## Completed This Session

Three issues from §1.7 (Group Cohomology):

1. **lemmafeld-4rdp**: TC 1.7.1 - Explicit differential formulas d₁-d₄ — COMPLETE
   - Created `Chapter1/GroupCohomology.lean`
   - Documented `inhomogeneousCochains.d_hom_apply` correspondence

2. **lemmafeld-rm4u**: TC 1.7.2 - H⁰ and H¹ for trivial action — COMPLETE
   - `H0Iso`, `H0IsoOfIsTrivial`, `H1IsoOfIsTrivial`

3. **lemmafeld-wlki**: TC 1.7.3 - Non-abelian 1-cocycles — COMPLETE
   - `IsMulCocycle₁` with convention note (mathlib vs book order)

## Current State

**Build:** Passing (`lake build` succeeds)

**§1.7 Coverage:** 60% (3/5 items)
| Item | Status |
|------|--------|
| Example 1.7.1 (differentials) | ✓ |
| Example 1.7.2 (H⁰, H¹) | ✓ |
| Remark 1.7.3 (non-abelian) | ✓ |
| Example 1.7.4 (ℤ/nℤ) | Not started |
| Exercise 1.7.5 (ring structure) | Not started |

## Next Steps (SECTION ORDER)

### 1. TC 1.7.4: ℤ/nℤ cohomology computation
- Issue: `lemmafeld-j2mh`
- Book uses smaller resolution: ∂_i = (g-1) or Σg^k
- Result: H^{2j+1} = 0, H^{2j} = ℤ/nℤ for j > 0

### 2. TC 1.7.5: Ring structure on H*(ℤ/nℤ, ℤ)
- Issue: `lemmafeld-7jnu`
- H* = ℤ[x]/(nx) with x in degree 2

### 3. After §1.7: Check §1.8 gaps
- §1.8 at 42% coverage per learnings index

## Files Modified This Session

- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/GroupCohomology.lean` — NEW (~160 LOC)
  - Example 1.7.1: Explicit d₁-d₄ formulas
  - Example 1.7.2: H⁰ = invariants, H¹ = Hom for trivial
  - Remark 1.7.3: IsMulCocycle₁ for non-abelian
- `docs/learnings/chapter1/derived_functors.md` — Updated with all three items
- `docs/learnings/index.md` — Updated §1.7 coverage to 60%

## Key Learnings

1. **Universe polymorphism**: `Rep k G` requires k, G in same universe
2. **Cocycle conventions**: Mathlib uses `g•f(h)*f(g)`, book uses `f(g)*g•f(h)`
3. **Low-degree cohomology**: Rich API in `GroupCohomology.LowDegree`
4. **IsTrivial typeclass**: Marks representations with trivial G-action
