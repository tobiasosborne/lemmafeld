# API Gotchas

Common API issues and their solutions.

## Abelian Category APIs

| Issue | Wrong | Right |
|-------|-------|-------|
| Mono from kernel=0 | `mono_of_kernel_ι_eq_zero` (scoping issues) | `Preadditive.mono_of_kernel_zero h` |
| Epi from cokernel=0 | `epi_of_cokernel_π_eq_zero` (scoping issues) | `Preadditive.epi_of_cokernel_zero h` |
| ShortExact.isIso_f | `ShortExact.isIso_f` (doesn't exist) | `ShortExact.isIso_f_iff : IsIso S.f ↔ IsZero S.X₃` |
| Zero object notation | `(0 : C)` (fails) | `open scoped ZeroObject` first |

## Simple Objects

| Issue | Solution |
|-------|----------|
| `isIso_of_hom_simple` fails | Add `[HasKernels C]` or use `[Abelian C]` |

## Biproducts

| Issue | Solution |
|-------|----------|
| Single element biproduct | `biproductUniqueIso [Unique J] (f : J → C) : ⨁ f ≅ f default` |
| No `biproduct.isoPEmpty` | Use empty biproduct API differently |
| No `biproduct.isoUnit` | Use `biproductUniqueIso` with Unit |

## Linear Categories

| Issue | Solution |
|-------|----------|
| `Linear.smul_comp` arguments | Takes 6 args: `X Y Z r f g` |
| `F.map_add` usage | It's a term, not a function to apply |
| `F.mapBiprod` | Requires `[PreservesBinaryBiproduct X Y F]` |

## Subobjects and Chain Conditions

| Issue | Solution |
|-------|----------|
| `IsArtinianObject X` construction | `ObjectProperty.is_of_prop isArtinianObject hX` |
| `Finite.to_wellFoundedLT/GT` | Need explicit type: `(inferInstance : WellFoundedLT _)` |

## Module Structures on Hom

| Goal | Requirement |
|------|-------------|
| Left A-module on `Y →ₗ[k] X` | `[SMulCommClass k A X]` |
| Right A-module (Aᵐᵒᵖ-action) on `Y →ₗ[k] X` | `[SMulCommClass A k Y]` for `DistribMulAction.toLinearMap` |

## Imports

| Need | Import |
|------|--------|
| `X ⊞ Y` notation | `Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts` |
| `Skeleton` type | `Mathlib.CategoryTheory.Skeletal` (NOT `Skeleton`) |
| `LinearMap.inl/inr/fst/snd` | `Mathlib.LinearAlgebra.Prod` |
| Quotient modules `⧸` | `Mathlib.LinearAlgebra.Quotient.Basic` |

## Universe Variables

Always declare explicitly: `universe w` in sections that use them. Don't use `abbrev X := @SomeClass` with universe polymorphism.

## Endomorphism Ring

**Critical:** In `End X`, multiplication is `x * y = y ≫ x` (reversed!). So `f^m * f^k = f^k ≫ f^m`.

Use `pow_mul_comm` for commutativity of powers.
