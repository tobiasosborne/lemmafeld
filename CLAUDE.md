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

> **THE BOOK IS THE SOURCE OF TRUTH.** Read the section before coding.
> **ERRORS are NOT failures.** Document learnings. That is success.
> **Incomplete work IS success.** STOP before "simplifying" or "optimizing."
> **Small deltas only.** Target ≤50 LOC changed per session.
> **Documentation is deliverable.** Write what you learned, especially failures.
> **ALWAYS DOCUMENT MATHLIB MAPPINGS.** Even "nothing to do" saves future agents hours.

---

## Session Protocol

### Phase 1: Orient (Clean Context Start)

1. **Read HANDOFF.md** — Understand current state
2. **Read LEARNINGS.md** — Don't repeat known failures
3. **Check issue tracker** — `bd ready` or equivalent
4. **Select ONE issue** — Smallest unblocked P0/P1/P2

Do NOT proceed until you can state:
- What you're working on (issue ID)
- What the success criterion is
- What files you'll touch

### Phase 2: Execute (Bounded Work)

**Constraints:**
- Target: ≤50 LOC delta
- Max file size: 200 LOC (any file type)
- Time-box: If stuck >15 min on same error, STOP and go to Phase 3b

**Lean workflow:**
1. **Read the book section** for the current issue
2. Search mathlib: use `lean_leanfinder` (best), `lean_loogle`, `lean_local_search`
3. **Document findings** in LEARNINGS.md (even if mathlib has it!)
4. Make smallest change toward goal
5. Build: `lake build`
6. Green → continue. Red → diagnose or escalate.

### Phase 3: Outcome

#### 3a: Success Path
1. Update HANDOFF.md with completed work
2. Add any discoveries to LEARNINGS.md
3. Close issue in tracker
4. Proceed to Phase 4

#### 3b: Problem Path — THE CRITICAL PART

**DO NOT:**
- Thrash repeatedly on the same error
- "Simplify" the approach without documenting why
- Delete code that doesn't work without recording what you tried

**DO:**
1. **Document the failure** in LEARNINGS.md:
```markdown
   ## [Date] Attempted: <what>
   **Approach:** <what you tried>
   **Result:** <what happened>
   **Hypothesis:** <why it failed>
   **Recommendation:** <what to try next>
```

2. **Classify the blockage:**

   | Type | Symptom | Action |
   |------|---------|--------|
   | **Too Complex** | Multiple unknowns, unclear decomposition | Create RESEARCH issue |
   | **Slightly Too Big** | Clear path but >50 LOC | Create 2-3 atomic sub-issues |
   | **Missing Knowledge** | Need to read docs/papers/code | Create RESEARCH issue |
   | **Tooling Bug** | External tool broken | Create BUG issue, work around or skip |
   | **Design Flaw** | Current approach fundamentally wrong | Create DESIGN issue, document alternatives |

3. **Create follow-up issues:**
```bash
   bd create --title="Research: <topic>" --type=research --priority=2
   bd create --title="Subtask: <atomic step>" --type=task --priority=2
```

4. **Proceed to Phase 4** — This is still success!

### Phase 4: Hygiene Round

**Automated checks (run all):**
```bash
# LOC check 
find . -name "*.lean" -o -name "*.clj" -o -name "*.md" | xargs wc -l | awk '$1 > 200 {print "VIOLATION:", $2}'

# Stale documentation check
# (compare file mtimes, check for orphaned docs, etc.)
```

**Create issues for any violations:**
```bash
bd create --title="Hygiene: <file> exceeds 200 LOC" --type=task --priority=0
```

### Phase 5: Land the Plane

**Mandatory checklist:**

- [ ] LEARNINGS.md updated (even if "nothing learned" — note that!)
- [ ] HANDOFF.md updated with:
  - Completed this session
  - Current state  
  - Next steps
  - Known issues / gotchas
  - Files modified
- [ ] Issues updated (`bd close`, `bd sync`)
- [ ] Changes committed and pushed
- [ ] Build passing

**Handoff template:**
```markdown
# Handoff: [Date/Time]

## Completed This Session
- <issue-id>: <one-line summary>

## Current State
<What's working, what's not>

## Next Steps
1. <Highest priority next task>
2. <Second priority>

## Known Issues / Gotchas
- <Thing that will bite the next agent>

## Files Modified
- `path/to/file.ext` — <what changed>
```

---

## Research Round Protocol

When a RESEARCH issue is selected:

1. **Define the question** precisely (write it down)
2. **Time-box:** 20 minutes max
3. **Sources:** docs, papers, existing code, web search
4. **Output:** Update LEARNINGS.md with:
   - Question asked
   - Sources consulted
   - Answer found (or "inconclusive")
   - Implications for the blocked task

Research rounds do NOT produce code. They produce knowledge.

---

## Deviation Detection

**Red flags that you're going off-plan:**

- You're solving a problem not in the selected issue
- You're changing files not mentioned in your Phase 1 statement
- You're "refactoring" or "cleaning up" something unrelated
- You can't explain how your current edit advances the issue
- Your delta is approaching 50 LOC and you're not done
- You're introducing concepts/abstractions not in existing design docs

**If any apply:** STOP. Go to Phase 3b. This is not failure.

---

## Issue Tracking Integration

### Priority Levels
- **P0**: Blocking (build broken, critical violation)
- **P1**: High (core functionality incomplete)
- **P2**: Medium (improvements, non-critical bugs)
- **P3**: Low (documentation, style, nice-to-have)

### Issue Types
- **task**: Concrete implementation work
- **research**: Investigation, no code output expected
- **bug**: Something broken
- **design**: Architecture decision needed

---

### Current Projects

| Project | Issues | Label |
|---------|--------|-------|
| Tensor Categories (Etingof) | 397 | `tensor-categories` |
| GNS Construction | — | — |
| Archimedean Closure | — | — |
| AF Permutation Groups | — | — |

---

## Tensor Categories Formalization

> **THE BOOK IS THE GUIDE.** We are formalizing Etingof et al. section by section.
> Always read the relevant book section before working on any issue.

**Book (MARKDOWN):** `docs/books/etingof_tensor_categories.pdf-2015-etingof_tensor_categories/etingof_tensor_categories.pdf-2015-etingof_tensor_categories.md`
**Book (citation):** Etingof, Gelaki, Nikshych, Ostrik - "Tensor Categories" (AMS 2015)
**Plan:** `docs/plans/tensor_categories_implementation.md`
**Location:** `LemmaFeld/CategoryTheory/TensorCategories/`

### CRITICAL: Book-First Workflow

1. **Read the book section** before starting any TC issue
2. **Formalize what the book says** - not less, not much more
3. **If mathlib already has it:** Document the mapping in LEARNINGS.md AND add a comment in code
4. **Reference book sections** in all code comments (e.g., "-- §1.3 Definition 1.3.1")

### Documenting Mathlib Mappings

Even if mathlib covers a concept, **ALWAYS document it** so future agents don't waste time:

```lean
-- §1.1: Locally small categories
-- Book: "A category is called locally small if Hom_C(X,Y) is a set"
-- Mathlib: `CategoryTheory.LocallySmall` in Mathlib.CategoryTheory.Category.Basic
```

Update LEARNINGS.md with:
```markdown
## §X.Y: <Topic>
**Book says:** <definition/theorem statement>
**Mathlib has:** `Namespace.Name` in `Mathlib.Path.To.File`
**Mapping:** <any differences in naming/formulation>
```

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

> **ERRORS are NOT failures.** Document learnings. That is success.
> **FAILURE to report errors ARE THE WORST FAILURES.
> **Incomplete work IS success.** STOP before "simplifying" or "optimizing."
