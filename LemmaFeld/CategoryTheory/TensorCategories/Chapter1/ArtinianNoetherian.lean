/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Noetherian
import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Artinian and Noetherian Objects

This file documents the correspondence between Etingof et al. "Tensor Categories" §1.5
chain conditions and mathlib's Artinian/Noetherian object infrastructure.

## Book Reference

Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015), §1.5

## Mathlib Correspondence

| Book Concept | Mathlib | Notes |
|--------------|---------|-------|
| Artinian object | `IsArtinianObject X` | DCC on subobjects |
| Noetherian object | `IsNoetherianObject X` | ACC on subobjects |

## Definitions

- `IsArtinianObject X` = `WellFoundedLT (Subobject X)` (descending chains stabilize)
- `IsNoetherianObject X` = `WellFoundedGT (Subobject X)` (ascending chains stabilize)
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

/-! ## Artinian Objects

Book context: An object is Artinian if any descending chain of subobjects stabilizes.

Mathlib: `IsArtinianObject X` defined as `WellFoundedLT (Subobject X)` in
`Mathlib.CategoryTheory.Subobject.ArtinianObject`
-/

section ArtinianObjects

variable {C : Type*} [Category C]

-- Artinian objects have well-founded descending chains
example (X : C) [h : IsArtinianObject X] : WellFoundedLT (Subobject X) := inferInstance

-- Zero object is Artinian
example [HasZeroObject C] : IsArtinianObject (0 : C) :=
  isArtinianObject_of_isZero (isZero_zero C)

-- Artinian is closed under subobjects (mono)
example {X Y : C} (i : X ⟶ Y) [Mono i] [IsArtinianObject Y] : IsArtinianObject X :=
  isArtinianObject_of_mono i

end ArtinianObjects

/-! ## Noetherian Objects

Book context: An object is Noetherian if any ascending chain of subobjects stabilizes.

Mathlib: `IsNoetherianObject X` defined as `WellFoundedGT (Subobject X)` in
`Mathlib.CategoryTheory.Subobject.NoetherianObject`
-/

section NoetherianObjects

variable {C : Type*} [Category C]

-- Noetherian objects have well-founded ascending chains
example (X : C) [h : IsNoetherianObject X] : WellFoundedGT (Subobject X) := inferInstance

-- Zero object is Noetherian
example [HasZeroObject C] : IsNoetherianObject (0 : C) :=
  isNoetherianObject_of_isZero (isZero_zero C)

-- Noetherian is closed under subobjects (mono)
example {X Y : C} (i : X ⟶ Y) [Mono i] [IsNoetherianObject Y] : IsNoetherianObject X :=
  isNoetherianObject_of_mono i

end NoetherianObjects

end LemmaFeld.TensorCategories.Chapter1
