# Handoff: 2026-01-31

## Completed This Session

- **lemmafeld-8xv7**: TC 1.8.11: Corollary - Yoneda for left exact functors
  - Added `IsLeftExactCorepresentable` definition
  - Documented mathlib correspondence: `IsCorepresentable`, `PreservesFiniteLimits`, `coyoneda`
  - Added example for Remark 1.8.12 using `coyonedaEquiv`

- **lemmafeld-tgqo**: TC 1.8.13: Definition - Virtual projective objects K₀(C)⊗k
  - Added `IsIndecompProjective`, `IndecompProjectiveObject`, `IsoClassIndecompProjective`
  - Added `K0` (free abelian group on iso classes of indecomposable projectives)
  - Added `VirtualProjective` = K₀(C) ⊗_ℤ k

- **lemmafeld-296g**: TC 1.8.14: Definition - Cartan matrix [P(X):Y]
  - Added `CartanMatrixData` structure (simples, projective covers, multiplicities)
  - Added `CartanMatrixData.toMatrix` to `Matrix (Fin n) (Fin n) ℕ`

## Current State

**Chapter 1 Progress:**
- §1.8.11-1.8.14: Complete (corepresentability, virtual projectives, Cartan matrix)

## Next Steps (by section order)

1. **TC 1.8.15+**: Continue through §1.8 (Prop 1.8.15 onwards)
2. **TC 1.9.x**: Coalgebras section

## Known Issues / Gotchas

- `Indecomposable` requires `HasBinaryBiproducts C`
- K₀(C) vs Gr(C): different groups (projectives vs simples)
- CartanMatrixData requires HasMultiplicity (from GrothendieckGroup.lean)

## Files Modified

- `LemmaFeld/CategoryTheory/TensorCategories/Chapter1/RepresentableFunctors.lean` — Added §1.8.11-1.8.14
- `docs/learnings/chapter1/locally_finite.md` — Updated with §1.8.11-1.8.14 documentation
