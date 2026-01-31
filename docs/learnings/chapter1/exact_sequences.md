# Chapter 1: Exact Sequences (§1.4)

## §1.4.1-1.4.2: Exact Sequences

**Book Definition 1.4.1:**
- Exact at i: Im(f_{i-1}) = Ker(f_i)
- Short exact: 0 → X → Y → Z → 0

**Mathlib (`Mathlib.Algebra.Homology.ShortComplex`):**

```lean
-- ShortComplex: X₁ →[f] X₂ →[g] X₃ with g ∘ f = 0
structure ShortComplex where
  X₁ X₂ X₃ : C
  f : X₁ ⟶ X₂
  g : X₂ ⟶ X₃
  zero : f ≫ g = 0

-- Exact: homology is zero
structure Exact : Prop where
  condition : ∃ (h : S.HomologyData), IsZero h.left.H

-- ShortExact: 0 → X₁ → X₂ → X₃ → 0
structure ShortExact : Prop where
  exact : S.Exact
  [mono_f : Mono S.f]
  [epi_g : Epi S.g]
```

**Key lemmas:**
- `ShortExact.fIsKernel` — f is the kernel of g
- `ShortExact.gIsCokernel` — g is the cokernel of f
- `isIso₂_of_shortExact_of_isIso₁₃` — Five lemma

**Lean file:** `Chapter1/ExactSequences.lean`

---

## §1.4.3: Ext Groups and Abelian Structure

**Book Definition 1.4.2:** Ext¹(Y, X) = isomorphism classes of extensions 0 → X → Z → Y → 0

**Mathlib approach:** Derived functors, NOT extension classes
- `Ext R C n : Cᵒᵖ ⥤ C ⥤ ModuleCat R`
- Requires `EnoughProjectives`
- `AddCommGroup (Ext X Y n)` comes automatically from ModuleCat

**Note:** No explicit "Yoneda Ext" (Ext as extensions) formalized in mathlib, though mathematically equivalent.

### Exercise 1.4.3(i): Abelian Group Structure — COMPLETE

**Lean files:** `Chapter1/BaerSum.lean`, `Chapter1/ExtAbelianGroup.lean`

The abelian group structure on Ext¹(Y, X) is demonstrated via:
- `AddCommGroup (Ext X Y 1)` instance from mathlib
- All abelian group axioms verified in `ExtAbelianGroup.lean`
- Composition distributes over addition (`Ext.add_comp`, `Ext.comp_add`)

### Exercise 1.4.3(ii): Ext¹ ≅ Der/InnerDer — COMPLETE

**Infrastructure files:**
- `InnerDerivations.lean`, `HochschildH1.lean`, `BimoduleDerivations.lean`
- `ExtAsDerivations.lean`, `SemidirectProduct.lean`, `ExtDerivationConstruction.lean`
- `ExtDerivationIso.lean`

**Completed:**
- Bimodule structure on Hom_k(Y, X)
- Derivation → Extension (semidirect product construction)
- Extension → Derivation (via k-linear section)
- Round-trip Φ∘Ψ = id (`derivation_roundtrip`)
- Inner derivation → trivial extension (`innerDerivation_shear_intertwines`)
- **Split extension ⟺ inner derivation** (`semidirect_split_iff_inner`)
  - Forward: A-linear section with g implies D = -D_g is inner
  - Backward: Inner derivation D_f has shearing isomorphism to trivial
- Main theorem: `ext1_iso_hochschildH1_components` packages all components

**Result:** ker(Der → Ext¹) = InnerDer, proving Ext¹(Y,X) ≅ Der(A,Hom_k(Y,X))/InnerDer = H¹

---

## Exercise 1.4.3(ii): Ext¹ as Derivations

**Book statement:** For A-mod over k: Ext¹(Y, X) ≅ Der(A, Hom_k(Y,X)) / InnerDer

### Bimodule Structure on Hom_k(Y, X)

- **Left A-action:** `(a · f)(y) = a · f(y)` — automatic from `Module A (Y →ₗ[k] X)` with `[SMulCommClass k A X]`
- **Right Aᵐᵒᵖ-action:** `(f · a)(y) = f(a · y)` — via `DistribMulAction.toLinearMap k Y a` with `[SMulCommClass A k Y]`

### Extension → Derivation Construction

Given 0 → X → E → Y → 0 with section s : Y →ₗ[k] E:
```
D(a)(y) = a • s(y) - s(a • y)
```
Requires `[SMulCommClass A k E]` and `[SMulCommClass A k Y]`.

### Derivation → Extension Construction

Given D : A → Hom_k(Y, X), build E = X × Y with action:
```
a · (x, y) = (a · x + D(a)(y), a · y)
```

### Round-Trip Proofs

- **D → E → D = id:** Proved via `derivation_roundtrip`
- **E → D → E ≃ E:** k-linear via `extensionSemidirectEquiv`

### A-Linearity Resolution

Key techniques:
1. `IsScalarTower k A X` — k-scalars work through A-scalars
2. `apply_fun equiv using equiv.injective` — move to Subtype level
3. `smul_one_smul A r x` — rewrite `r • x` as `(r • 1) • x`

### BimoduleDerivations

**Bimodule Leibniz:** `D(ab) = a • D(b) + (op b) • D(a)` (NOT mathlib's symmetric form)

**Inclusion:** `InnerDerivations ⊆ BimoduleDerivations` requires `SMulCommClass A Aᵐᵒᵖ M`

**Lean files:** `Chapter1/ExtAsDerivations.lean`, `Chapter1/ExtDerivationIso.lean`
