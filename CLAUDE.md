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

## 🚨 CRITICAL: OUTPUT IS LEAN CODE 🚨

**THE DELIVERABLE IS LEAN FILES, NOT DOCUMENTATION.**

Every task issue MUST result in:
1. **A `.lean` file created or modified** in `LemmaFeld/CategoryTheory/TensorCategories/`
2. The Lean file must **compile without errors** (`lake build`)
3. Even if mathlib already has something, create a Lean file that:
   - Imports the relevant mathlib modules
   - Adds book reference comments (e.g., `-- §1.3 Definition 1.3.1`)
   - Provides aliases/abbrevs if book notation differs from mathlib
   - Documents the book ↔ mathlib correspondence IN THE CODE

**WRONG:** "Verified mathlib has X. Updated LEARNINGS.md. Closed issue."
**RIGHT:** "Created `Chapter1/Abelian.lean` with imports and book mappings. Builds. Closed issue."

If you close an issue without creating/modifying a Lean file, **YOU HAVE FAILED**.

---

## GOLDEN RULES

> **OUTPUT IS LEAN CODE.** Every issue = Lean file created/modified.
> **THE BOOK IS THE SOURCE OF TRUTH.** Read the section before coding.
> **ERRORS are NOT failures.** Document learnings. That is success.
> **Incomplete work IS success.** STOP before "simplifying" or "optimizing."
> **Small deltas only.** Target ≤50 LOC changed per session.
> **ALWAYS DOCUMENT MATHLIB MAPPINGS.** In the Lean file AND LEARNINGS.md.

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
3. **CREATE/MODIFY A LEAN FILE** in `LemmaFeld/CategoryTheory/TensorCategories/ChapterN/`
   - If mathlib has it: import + comment documenting book↔mathlib mapping
   - If mathlib lacks it: implement the definition/theorem
   - Add book references: `-- §X.Y Definition X.Y.Z`
4. Build: `lake build` — **MUST COMPILE**
5. Update LEARNINGS.md with findings
6. Green → continue. Red → diagnose or escalate.

**⚠️ NO LEAN FILE = NO COMPLETION. Documentation alone is NOT sufficient.**

### Phase 3: Outcome

#### 3a: Success Path
1. **VERIFY LEAN FILE EXISTS** — If no `.lean` file was created/modified, GO BACK
2. **VERIFY BUILD PASSES** — `lake build` must succeed
3. Update HANDOFF.md with completed work (include Lean file path!)
4. Add any discoveries to LEARNINGS.md
5. Close issue in tracker
6. Proceed to Phase 4

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

- [ ] **LEAN FILES CREATED/MODIFIED** — This is the primary deliverable!
- [ ] **BUILD PASSING** — `lake build` succeeds
- [ ] LEARNINGS.md updated (even if "nothing learned" — note that!)
- [ ] HANDOFF.md updated with:
  - Completed this session
  - Current state
  - Next steps
  - Known issues / gotchas
  - **Lean files modified** (REQUIRED)
- [ ] Issues updated (`bd close`, `bd sync`)
- [ ] Changes committed and pushed

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

## 🚨 ESCALATION FAILURE MODE 🚨

**This failure mode has occurred. Learn from it.**

### The Anti-Pattern

An agent identifies a significant gap, complex theorem, or major missing functionality. Instead of escalating to the issue tracker, they:
- Write a note in LEARNINGS.md ("Mitchell embedding not in mathlib - significant project")
- Move on
- **Never create an issue**

The information is now buried. Future agents won't see it in `bd ready`. The work is never tracked.

### Real Example (2026-01-28)

From LEARNINGS.md:
> **Mitchell embedding (Theorem 1.3.8):** Not in mathlib as of 2024 - would be a significant formalization project.

**What should have happened:** Create an issue:
```bash
bd create --title="Research: Mitchell embedding theorem (§1.3.8)" --type=research --priority=2
```

### The Rule

**If you write something in LEARNINGS.md that implies future work is needed, CREATE AN ISSUE.**

Triggers that require escalation:
- "Not in mathlib" + non-trivial to implement
- "Would be a significant project"
- "Needs investigation"
- "May need implementation"
- "Gap in coverage"
- "Partial - check coverage"
- Any TODO/FIXME sentiment

### Checklist Before Session End

- [ ] Grep LEARNINGS.md for "not in mathlib", "gap", "missing", "needs", "TODO"
- [ ] For each hit: Is there a corresponding issue? If not, create one.
- [ ] Verify: `bd list` shows any gaps you identified

**Documentation without escalation = lost work. Issues are the memory.**

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

### CRITICAL: Book-First Workflow — LEAN FILES REQUIRED

1. **Read the book section** before starting any TC issue
2. **CREATE A LEAN FILE** — Every issue produces a `.lean` file
3. **Formalize what the book says** in Lean code:
   - If mathlib has it: `import` + comments mapping book to mathlib
   - If mathlib lacks it: implement the definition/theorem/proof
4. **Reference book sections** in all code comments (e.g., `-- §1.3 Definition 1.3.1`)
5. **Build must pass**: `lake build`

**Example Lean file structure for mathlib-covered content:**
```lean
/-
  LemmaFeld/CategoryTheory/TensorCategories/Chapter1/Abelian.lean

  §1.3: Abelian Categories (Etingof et al.)

  This section is fully covered by mathlib. We document the correspondence.
-/
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Kernels

namespace LemmaFeld.TensorCategories.Chapter1

/-! ## §1.3 Definition 1.3.1: Abelian Category

Book: "An abelian category is an additive category C in which for every
morphism φ: X → Y there exists a canonical decomposition K → X → I → Y → C"

Mathlib: `CategoryTheory.Abelian` class in `Mathlib.CategoryTheory.Abelian.Basic`
-/

-- Re-export for convenience
abbrev Abelian := CategoryTheory.Abelian

end LemmaFeld.TensorCategories.Chapter1
```

### Documenting Mathlib Mappings — IN LEAN FILES

Even if mathlib covers a concept, **CREATE A LEAN FILE** that documents it:

**Step 1: Create the Lean file** (PRIMARY OUTPUT)
```lean
-- LemmaFeld/CategoryTheory/TensorCategories/Chapter1/LocallySmall.lean

/-! ## §1.1: Locally Small Categories

Book: "A category is called locally small if Hom_C(X,Y) is a set"
Mathlib: `CategoryTheory.LocallySmall` in `Mathlib.CategoryTheory.Category.Basic`
-/
import Mathlib.CategoryTheory.Category.Basic

namespace LemmaFeld.TensorCategories.Chapter1

-- Book §1.1 notation/definition mapped to mathlib
abbrev LocallySmall := CategoryTheory.LocallySmall

end LemmaFeld.TensorCategories.Chapter1
```

**Step 2: Also update LEARNINGS.md** (secondary)
```markdown
## §X.Y: <Topic>
**Lean file:** `LemmaFeld/CategoryTheory/TensorCategories/ChapterN/File.lean`
**Book says:** <definition/theorem statement>
**Mathlib has:** `Namespace.Name` in `Mathlib.Path.To.File`
```

**⚠️ The Lean file is REQUIRED. LEARNINGS.md alone is NOT sufficient.**

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
