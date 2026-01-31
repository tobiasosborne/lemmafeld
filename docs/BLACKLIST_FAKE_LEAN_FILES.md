# Blacklisted Lean Files - Documentation Only

**Created:** 2026-01-31
**Purpose:** These files contain only `#check` statements, `example` demonstrations, and documentation comments. They do NOT contain actual formalization (no `def`, `theorem`, `lemma`, `abbrev`, or `instance` declarations with real content).

These files MUST NOT be counted as formalization progress. They are documentation showing mathlib correspondence, not original work.

## Chapter 1 Fake Files (20 files)

| File | Content | Issue |
|------|---------|-------|
| `Chapter1/Basic.lean` | 1 trivial abbrev, rest docs | lemmafeld-0dej |
| `Chapter1/SmallCategories.lean` | 7 examples, 5 #checks | lemmafeld-tcxg |
| `Chapter1/Notation.lean` | 15 trivial examples | lemmafeld-dn5b |
| `Chapter1/ExactSequences.lean` | 11 examples | lemmafeld-cmpd |
| `Chapter1/Simple.lean` | 7 examples | lemmafeld-1wfd |
| `Chapter1/ExtGroups.lean` | 12 examples | lemmafeld-ctzt |
| `Chapter1/Abelian.lean` | 8 examples | lemmafeld-eg8l |
| `Chapter1/AbelianProperties.lean` | 10 examples, 2 #checks | lemmafeld-o0xb |
| `Chapter1/LinearCategory.lean` | 8 examples | lemmafeld-pyu3 |
| `Chapter1/Additive.lean` | 5 examples | lemmafeld-5yef |
| `Chapter1/ExtAbelianGroup.lean` | 13 examples | lemmafeld-t3fn |
| `Chapter1/ArtinianNoetherian.lean` | 6 examples | lemmafeld-yk6j |
| `Chapter1/ExactFunctors.lean` | 11 examples | lemmafeld-7f9v |
| `Chapter1/DerivedFunctors.lean` | 4 examples | lemmafeld-rm9z |
| `Chapter1/Resolutions.lean` | 8 examples | lemmafeld-rgnk |
| `Chapter1/JordanHolder.lean` | 9 examples | lemmafeld-rdzv |
| `Chapter1/BaerSum.lean` | examples only | lemmafeld-fglk |
| `Chapter1/GroupCohomology.lean` | 9 #checks | lemmafeld-uso6 |
| `Chapter1/CohomologyRing.lean` | 3 #checks, pseudo-code | lemmafeld-0h0f |
| `Chapter1/ExtAsDerivations.lean` | 1 def, 9 examples | lemmafeld-7d15 |

## What Makes a File "Fake"

A file is considered FAKE/documentation-only if it:
1. Contains primarily `#check` statements verifying mathlib has things
2. Contains primarily `example` statements demonstrating mathlib API
3. Has extensive documentation comments but no real definitions
4. Has pseudo-code in comments (like `-- def foo := ...`)
5. Total `def`/`theorem`/`lemma`/`abbrev`/`instance` count is 0-1

## What Real Formalization Looks Like

A file with REAL formalization has:
1. Multiple `def`, `theorem`, `lemma`, `abbrev`, or `instance` declarations
2. Proofs (even if they use `sorry` for hard subgoals)
3. New mathematical content not just re-exporting mathlib

## Audit Date

Last full audit: 2026-01-31

Chapter 1 Results:
- REAL CODE: 37 files (64%)
- FAKE: 20 files (34%)
- EMPTY: 1 file (2%)
