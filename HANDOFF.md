# Handoff: 2026-02-03

## Priority Focus: §1.5 Completion

All sessions should prioritize §1.5 (Length Objects) until fully formalized.

## §1.5 Status

### COMPLETE (0 sorries)

| Topic | File(s) | Key Theorems |
|-------|---------|-------------|
| §1.5.1 Simple objects | `Chapter1/Simple.lean` | Schur's lemma via mathlib |
| §1.5.2 Semisimple | `Chapter1/Semisimple.lean` | `IsSemisimple`, `SemisimpleCategory` |
| §1.5.3 Schur's Lemma | `Chapter1/Simple.lean` | mathlib coverage |
| §1.5.4-5 JH series/length | `Chapter1/JordanHolder.lean`, `FiniteLength.lean` | Module case complete |
| §1.5.7 Fitting's Lemma | `Chapter1/FittingLemma.lean` | `fitting_lemma` (0 sorries) |
| §1.5.7 End(X) local ring | `Chapter1/FittingLemma.lean` | `isLocalRing_end_of_indecomposable_finiteLength` |
| §1.5.7 KS Existence | `Chapter1/KrullSchmidt/Existence.lean` | `krullSchmidt_existence` (0 sorries) |
| §1.5.7 KS Uniqueness | `Chapter1/KrullSchmidt/Uniqueness.lean` | `krullSchmidt_uniqueness` (0 sorries) |
| §1.5.10(ii) Linking | `Chapter1/BlockDecomposition.lean` | `Linked`, `linked_equivalence` |
| §1.5.10(i) Defs | `Chapter1/BlockDecomposition.lean` | `IndecomposableCategory`, `TrivialCategory` |
| §1.5.8 Gr(C) generated | `Chapter1/GrothendieckGroup.lean` | `grothendieckGroup_generated_by_simples` (0 sorries) |

### REMAINING WORK (0 sorries + 6 open issues)

| # | Issue | What | LOC est | Blocked by |
|---|-------|------|---------|------------|
| 1 | lemmafeld-mfs8 | `JordanHolderLattice (Subobject X)` instance | ~50 | nothing (deep) |
| 3 | lemmafeld-k1y1 | `HasMultiplicity` concrete impl | ~30 | nothing |
| 4 | lemmafeld-awcn | `HasMultiplicity` from JHL instance | ~30 | mfs8 |
| 5 | lemmafeld-2hzv | `objectClass` map `[X] : Ob(C) → Gr(C)` | ~40 | awcn |
| 6 | lemmafeld-4jc6 | Example 1.5.9: `Vec_S` graded spaces | ~30 | nothing |
| 7 | lemmafeld-5bq2 | Exercise 1.5.10(iii): center characters | ~40 | nothing |
| 8 | — | Exercise 1.5.10(i): block decomposition proof | ~50 | nothing |
| 9 | — | Exercise 1.5.10(ii): indecomposable ⟺ linked proof | ~50 | nothing |

---

## §1.5 Completion Plan (10-50 LOC steps)

### Track A: Grothendieck Group Sorry — COMPLETE ✓

**A1 done:** 0 sorries confirmed, issue lemmafeld-nwka closed.

### Track B: JordanHolderLattice for Subobject (deep gap)

This is the root blocker for the multiplicity chain.

**Step B1: COMPLETE ✓** — `SubobjectIsMaximal` defined as `Covby` in `Chapter1/JordanHolderSubobject.lean`

**Step B2: COMPLETE ✓** — `SubobjectIso` defined using `cokernel` isomorphism of pairs, with `iso_symm`, `iso_trans`

**Step B3: COMPLETE ✓** — Second isomorphism theorem (0 sorries) — issue lemmafeld-ict0 CLOSED
- File: `Chapter1/JordanHolderSubobject.lean`
- `secondIsoMap`, `mono_secondIsoMap`, `epi_secondIsoMap`, `secondIso`, `subobject_second_iso` — all proved
- `epi_secondIsoMap` proved via kernel/subobject argument: lift A, B through kernel.ι, show kernel contains A⊔B via Subobject.mk_le_mk_of_comm + sup_le, conclude kernel.ι is iso via isoOfMkEqMk, then zero_of_epi_comp
- **Mathlib gap confirmed**: No categorical 2nd iso theorem (our contribution).

**Step B4: Build the `JordanHolderLattice (Subobject X)` instance** (~30 LOC) — issue lemmafeld-ehiv
- File: `Chapter1/JordanHolderSubobject.lean` (extend)
- `sup_eq_of_isMaximal`: use `WCovBy.sup_eq` (general lattice, works immediately)
- `isMaximal_inf_left_of_isMaximal_sup`: needs `IsWeakLowerModularLattice (Subobject X)`
  - NOT in mathlib — must prove from second iso theorem
  - `inf_covBy_of_covBy_sup_of_covBy_sup_left` is the lemma (requires the instance)
- `second_iso`: from Step B3
- Pattern: follows `JordanHolderModule.instJordanHolderLattice` in mathlib

### Track C: HasMultiplicity Instance (blocked by B4)

**Step C1: Count factors in composition series** (~30 LOC)
- File: `Chapter1/GrothendieckGroup.lean` (extend)
- Given JordanHolderLattice (Subobject X), define:
  `multiplicityCount (s : CompositionSeries (Subobject X)) (Y : C) [Simple Y] : ℕ`
- Count indices i where factor s[i]/s[i+1] ≅ Y

**Step C2: Prove well-definedness via JH theorem** (~20 LOC)
- Show count is independent of series choice
- Use `CompositionSeries.jordan_holder` + bijection from Equivalent

**Step C3: Build `HasMultiplicity C` instance** (~20 LOC)
- `multiplicity X Y := multiplicityCount (some_series X) Y`
- Prove axioms: zero for IsZero, self = 1, additivity for SES

### Track D: objectClass Map (blocked by C3)

**Step D1: Define `objectClass : C → GrothendieckGroup C`** (~30 LOC)
- File: `Chapter1/GrothendieckGroup.lean` (extend)
- Given `ObjectClassData` + `HasMultiplicity`:
  `objectClass (X : C) := ∑ i, (mult X (ocd.toObj i)) • simpleClass C ⟨ocd.toObj i, ocd.simple_inst i⟩`
- Use `Finset.sum` over the finite set of simple representatives

**Step D2: Prove `objectClass_ses`** (~20 LOC)
- If 0 → X → Y → Z → 0 exact, then [Y] = [X] + [Z]
- Direct from `HasMultiplicity.multiplicity_add`

### Track E: Exercise 1.5.10 Proofs (unblocked)

**Step E1: Block decomposition of objects** (~40 LOC)
- File: `Chapter1/BlockDecomposition.lean` (extend)
- For finite-length X: X ≅ ⨁ X_α where X_α are "block components"
- X_α = maximal subobject with all JH factors in class α
- Uses linked equivalence classes of simples

**Step E2: Indecomposable ⟹ all simples linked** (~30 LOC)
- If C indecomposable, any two simples X, Y are linked
- Contrapositive: if not linked, partition simples → decompose C

**Step E3: All simples linked ⟹ indecomposable** (~30 LOC)
- If all simples linked but C = D × E nontrivially,
  simples split between D and E, no Ext¹ between factors → contradiction

**Step E4: Exercise 1.5.10(iii) center characters** (~40 LOC)
- File: `Chapter1/BlockDecomposition.lean` (extend)
- For A-mod: blocks labeled by characters of Z(A)
- Uses `Algebra.center`, `AlgHom` to base field

### Track F: Example 1.5.9 (unblocked)

**Step F1: Vec_S graded spaces** (~30 LOC)
- File: NEW `Chapter1/GradedSpaces.lean`
- Define Vec_S as S-graded finite dimensional vector spaces
- Show Gr(Vec_S) ≅ ℤ^S = FreeAbelianGroup S
- Simples are 1-dimensional spaces concentrated in degree s

---

## Recommended Session Order

1. **B3** — Second iso theorem (hardest remaining step, unblocks B4)
2. **B4** — JordanHolderLattice instance (after B3)
3. **E1-E3** — Independent of B, completes Exercise 1.5.10
4. **C1-C3** → **D1-D2** — After B4, completes Grothendieck group
5. **F1** — Easy example
6. **E4** — Module-specific, lower priority

---

## Session Orientation

1. **Read this file** for §1.5 plan
2. **Read `docs/learnings/chapter1/length_objects.md`** for technical details
3. **Pick a step** from the plan above (prefer unblocked, lowest number)
4. **One step per session** — target ≤50 LOC
