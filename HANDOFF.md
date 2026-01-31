# Handoff: 2026-01-31 (Inner Derivations Triviality)

## Completed This Session

- **lemmafeld-ff5z**: TC 1.4.3 — Closed as complete (part i) with gap tracked (part ii)
  - Part (i): Abelian group on Ext¹ is fully covered by `ExtAbelianGroup.lean`
  - Part (ii) gap tracked in lemmafeld-oybh
  - Updated `BaerSum.lean` with comprehensive summary

- **lemmafeld-oybh**: TC 1.4.3(ii) gap — Added key theorem
  - Added `innerDerivation_shear_intertwines` to `SemidirectProduct.lean`
  - Proves: inner derivations D_f give extensions isomorphic to trivial extension
  - The shearing map φ(x,y) = (x + f(y), y) intertwines D_f-action with diagonal action
  - This establishes ker(H¹ → Ext¹) = InnerDer, a key piece of the isomorphism

## Current State

**Build:** Passing (`lake build` succeeds)

**Chapter 1 Coverage:** Improved — §1.4.3 infrastructure strengthened

**Exercise 1.4.3(ii) Status:**
- ✓ derivation_roundtrip (Φ∘Ψ = id)
- ✓ extensionToSemidirect_respects_action (Ψ∘Φ ~ id)
- ✓ innerDerivation_shear_intertwines (InnerDer → trivial extension)
- Gap: Bundle into LinearEquiv between H¹ and Ext¹

## Next Steps (SECTION ORDER)

### 1. TC 1.4.3(ii) gap: Complete LinearEquiv (P2)
- Issue: lemmafeld-oybh
- Remaining: Bundle round-trips into LinearEquiv
- Estimated ~50 LOC

### 2. TC 1.5.10: Exercise - Block decomposition (P2)
- Issue: lemmafeld-0om5

### 3. TC 1.6.6: Definition - Projective cover (P2)
- Issue: lemmafeld-xoz1

## Files Modified

- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/SemidirectProduct.lean` — Added ~70 LOC
  - `innerDerivationShear`, `innerDerivationShearInv` — shearing maps
  - `innerDerivationShearEquiv` — k-linear equivalence
  - `innerDerivation_shear_intertwines` — KEY THEOREM
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/ExtDerivationIso.lean` — Updated docstring
- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/BaerSum.lean` — Added part (ii) summary
- `docs/learnings/chapter1/exact_sequences.md` — Updated with new theorem

## Notes

- The inner derivation triviality theorem is the "kernel" part of the Ext¹ ≅ H¹ isomorphism
- Full LinearEquiv requires relating InnerDerivations to extension equivalence classes
- Mathlib's Ext is via derived categories, so direct LinearEquiv would be to our H¹, not mathlib's Ext
