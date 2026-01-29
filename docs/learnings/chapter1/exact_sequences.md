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

## §1.4.3: Ext Groups

**Book Definition 1.4.2:** Ext¹(Y, X) = isomorphism classes of extensions 0 → X → Z → Y → 0

**Mathlib approach:** Derived functors, NOT extension classes
- `Ext R C n : Cᵒᵖ ⥤ C ⥤ ModuleCat R`
- Requires `EnoughProjectives`
- `AddCommGroup (Ext X Y n)` comes automatically from ModuleCat

**Gap:** No explicit "Yoneda Ext" (Ext as extensions) formalized, though mathematically equivalent.

**Lean file:** `Chapter1/BaerSum.lean`

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
