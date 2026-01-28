# CLAUDE.md — LemmaFeld Lean Formalization Monorepo

## Project Overview

**LemmaFeld** is a Lean 4 monorepo for mathematical formalizations, organized by mathematical domain.

### Structure
```
LemmaFeld/
├── Analysis/
│   └── OperatorAlgebras/
│       ├── GNS/                 # GNS construction for C*-algebras
│       └── ArchimedeanClosure/  # Archimedean closure characterization
├── GroupTheory/
│   └── AF/                      # H = An or Sn for permutation groups
├── CategoryTheory/
│   └── TensorCategories/        # Etingof et al. tensor categories book
└── Examples/                    # Standalone proofs
```

### Key Files
- `lakefile.toml` — Lean 4 v4.26.0, mathlib v4.26.0
- `docs/plans/tensor_categories_implementation.md` — 397-step formalization plan
- `.beads/beads.db` — Issue tracking (397 tensor category issues)

---

## GOLDEN RULES

> **ERRORS are NOT failures.** Document learnings. That is success.
> **Incomplete work IS success.** STOP before "simplifying" or "optimizing."
> **Small deltas only.** Target ≤50 LOC changed per session.

---

## Session Protocol

### Phase 1: Orient

1. Run `bd ready` — select ONE unblocked issue (prefer P0 > P1 > P2)
2. Check existing code in relevant module
3. State before proceeding: issue ID, success criterion, files you'll touch

### Phase 2: Execute

**Constraints:**
- Delta: ≤50 LOC
- Max file size: 200 LOC
- Stuck >15 min on same error → go to Phase 3b

**Lean workflow:**
1. Search mathlib first: `lake exe loogle`, Zulip, docs
2. Make smallest change toward goal
3. Build: `lake build`
4. Green → continue. Red → diagnose or escalate.

### Phase 3: Outcome

#### 3a: Success
1. `bd close <id>`
2. Document discoveries
3. → Phase 4

#### 3b: Problem — CRITICAL

**DO NOT** thrash, secretly simplify, or delete failed code without documenting.

**DO:**
1. Create blocking/research issues as needed
2. Document what was learned
3. Proceed to Phase 4 — this is still success.

### Phase 4: Land the Plane
```bash
lake build                    # Must pass
bd sync                       # Sync issues
git add -A
git commit -m "Session: <summary>"
git push
```

---

## Issue Tracking (Beads)

```bash
bd ready                      # What can I work on?
bd list -l chapter-1          # Chapter 1 tensor cat issues
bd list -l tensor-categories  # All 397 tensor cat issues
bd show <id>                  # Issue details
bd update <id> -s in_progress # Start working
bd close <id>                 # Complete issue
bd sync                       # Sync with git
```

**Priorities:** P0 blocking, P1 high, P2 medium, P3 low

### Current Projects

| Project | Issues | Label |
|---------|--------|-------|
| Tensor Categories (Etingof) | 397 | `tensor-categories` |
| GNS Construction | — | — |
| Archimedean Closure | — | — |
| AF Permutation Groups | — | — |

---

## Tensor Categories Formalization

**Book:** Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015)
**Plan:** `docs/plans/tensor_categories_implementation.md`
**Location:** `LemmaFeld/CategoryTheory/TensorCategories/`

### Chapter Breakdown
| Ch | Topic | Issues | Label |
|----|-------|--------|-------|
| 1 | Abelian Categories | 53 | `chapter-1` |
| 2 | Monoidal Categories | 42 | `chapter-2` |
| 3 | Z₊-Rings | 23 | `chapter-3` |
| 4 | Tensor Categories | 44 | `chapter-4` |
| 5 | Hopf Algebras | 43 | `chapter-5` |
| 6 | Finite Tensor Categories | 17 | `chapter-6` |
| 7 | Module Categories | 62 | `chapter-7` |
| 8 | Braided Categories | 67 | `chapter-8` |
| 9 | Fusion Categories | 45 | `chapter-9` |

### Priority Order
1. **Phase 1**: Chapters 1-2 (foundations)
2. **Phase 2**: Chapters 3-4 (core theory)
3. **Phase 3**: Chapters 5-6 (Hopf algebras)
4. **Phase 4**: Chapter 7 (module categories)
5. **Phase 5**: Chapter 8 (braided/modular)
6. **Phase 6**: Chapter 9 (fusion categories)

### Mathlib Integration
Many concepts already exist:
- `CategoryTheory.Abelian`
- `CategoryTheory.Monoidal`
- `CategoryTheory.Braided`
- `CategoryTheory.Rigid`

Check mathlib before implementing anything.

---

## Build Commands

```bash
lake update           # Update dependencies
lake exe cache get    # Download mathlib oleans
lake build            # Build everything
lake build LemmaFeld  # Build main target
```

---

## File Naming Conventions

Follow mathlib style:
- `LemmaFeld/CategoryTheory/TensorCategories/Monoidal/Basic.lean`
- `LemmaFeld/CategoryTheory/TensorCategories/Braided/Center.lean`
- Use `PascalCase` for directories, `PascalCase.lean` for files
