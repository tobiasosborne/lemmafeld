# Mathlib Mappings

Book ↔ mathlib correspondence tables for quick reference.

## Chapter 1 Topics

| Topic | Mathlib Location | Status |
|-------|------------------|--------|
| Abelian categories | `CategoryTheory.Abelian` | Complete |
| Preadditive categories | `CategoryTheory.Preadditive.Basic` | Complete |
| Exact sequences | `CategoryTheory.ShortComplex` | Complete |
| Simple objects | `CategoryTheory.Simple` | Complete |
| Projective/Injective | `CategoryTheory.Projective`, `CategoryTheory.Injective` | Complete |
| Coalgebras | `Coalgebra`, `CoalgebraCat` | Complete |
| Comonoid objects | `Comon_` | Complete |

## Chapter 2 Topics

| Topic | Mathlib Location | Status |
|-------|------------------|--------|
| Monoidal categories | `CategoryTheory.MonoidalCategory` | Complete |
| Braided categories | `CategoryTheory.BraidedCategory` | Complete |
| Symmetric categories | `CategoryTheory.SymmetricCategory` | Complete |
| Monoidal functors | `CategoryTheory.Functor.Monoidal`, `LaxMonoidal` | Complete |
| Duals (rigid) | `CategoryTheory.HasLeftDual`, `HasRightDual` | Complete |

## Known Gaps

| Topic | Status | Notes |
|-------|--------|-------|
| Jordan-Hölder (categorical) | GAP | Mathlib has `JordanHolderLattice` for lattices, NOT `Subobject X` |
| Krull-Schmidt | GAP | No theorem in mathlib |
| Grothendieck group Gr(C) | GAP | May need implementation |
| Deligne tensor product | GAP | Mathlib has `ExternalProduct` for diagrams, NOT category tensor |
| Coradical filtration | GAP | Needs implementation |
| Categorical semisimplicity | GAP | `IsSemisimpleModule` exists, not `SemisimpleCategory C` |

## Key Imports

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

## Notation Conventions

| Book | Mathlib |
|------|---------|
| `id_C` | `Functor.id C` or `𝟭 C` |
| `C^∨` | `Cᵒᵖ` |
| locally small | `LocallySmall` |
| essentially small | `EssentiallySmall` |
| `Hom_C(X,Y)` | `X ⟶ Y` |
| direct sum | `X ⊞ Y` (biprod) |
| Ext^n | `Ext X Y n` (args reversed from book) |
