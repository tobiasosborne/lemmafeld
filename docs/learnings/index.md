# Learnings Index

## 🚨 ONLY ACCEPTABLE OUTPUT IS LEAN CODE 🚨
**THE DELIVERABLE IS REAL LEAN FILES, NOT #checks, NOT COMMENTS, NOT DOCUMENTATION. DO NOT DELETE THIS REQUIREMENT**

This directory contains organized learnings from the Tensor Categories formalization project.

## Quick Links

| Document | Description |
|----------|-------------|
| [mathlib_mappings.md](mathlib_mappings.md) | Book ↔ mathlib correspondence tables |
| [api_gotchas.md](api_gotchas.md) | Common API issues and solutions |
| [proof_patterns.md](proof_patterns.md) | Reusable proof techniques |

## 🚨 ONLY ACCEPTABLE OUTPUT IS LEAN CODE 🚨
**THE DELIVERABLE IS REAL LEAN FILES, NOT #checks, NOT COMMENTS, NOT DOCUMENTATION. DO NOT DELETE THIS REQUIREMENT**

---

## Chapter 1 Coverage Audit (2026-01-31)

**Overall Coverage: 54.8%** (40/73 numbered items formalized)

| Section | Coverage | Status |
|---------|----------|--------|
| §1.1-1.2 | 100% | ✓ Complete |
| §1.3-1.6 | 43-78% | Partial - gaps tracked |
| §1.7 | **100%** | ✓ Complete (Ex 1.7.1-1.7.5 documented) |
| §1.8 | 42% | Representable functors gap |
| §1.9 | 54% | Comodules + Theorem 1.9.15 missing |
| §1.10 | **0%** | ⚠️ Coend reconstruction missing |
| §1.11-1.12 | 50-67% | Partial |
| §1.13 | **0%** | ⚠️ All coradical filtration missing |

**46 gap issues filed** — see `bd list --status=open | grep "TC 1."`

## 🚨 ONLY ACCEPTABLE OUTPUT IS LEAN CODE 🚨
**THE DELIVERABLE IS REAL LEAN FILES, NOT #checks, NOT COMMENTS, NOT DOCUMENTATION. DO NOT DELETE THIS REQUIREMENT**

---

## Chapter 1 Learnings

| Section | Document | Topics |
|---------|----------|--------|
| §1.1-1.3 | [chapter1/abelian.md](chapter1/abelian.md) | Categories, preadditive, abelian |
| §1.4 | [chapter1/exact_sequences.md](chapter1/exact_sequences.md) | Exact sequences, Ext, Baer sum, derivations |
| §1.5 | [chapter1/length_objects.md](chapter1/length_objects.md) | Simple, semisimple, finite length, Krull-Schmidt, Fitting |
| §1.6 | [chapter1/projective.md](chapter1/projective.md) | Projective/injective, exact functors |
| §1.7 | [chapter1/derived_functors.md](chapter1/derived_functors.md) | Derived functors, Ext, group cohomology |
| §1.8 | [chapter1/locally_finite.md](chapter1/locally_finite.md) | Locally finite, finite abelian categories |
| §1.9/1.13 | [chapter1/coalgebras.md](chapter1/coalgebras.md) | Coalgebras, grouplike, skew-primitive |
| §1.11-1.12 | [chapter1/deligne.md](chapter1/deligne.md) | External tensor product, Deligne tensor |

## 🚨 ONLY ACCEPTABLE OUTPUT IS LEAN CODE 🚨
**THE DELIVERABLE IS REAL LEAN FILES, NOT #checks, NOT COMMENTS, NOT DOCUMENTATION. DO NOT DELETE THIS REQUIREMENT**

## Critical Reminders

**OUTPUT IS LEAN CODE.** Every issue must produce a `.lean` file. Documentation alone is NOT sufficient.

## 🚨 ONLY ACCEPTABLE OUTPUT IS LEAN CODE 🚨
**THE DELIVERABLE IS REAL LEAN FILES, NOT #checks, NOT COMMENTS, NOT DOCUMENTATION. DO NOT DELETE THIS REQUIREMENT**

## What Counts as Completing an Issue

✅ CORRECT: Created/modified `.lean` file with real definitions/theorems
❌ WRONG: Wrote comments in docs/learnings/
❌ WRONG: Created empty placeholder structures
❌ WRONG: Just documented mathlib correspondence without Lean code

## 🚨 ONLY ACCEPTABLE OUTPUT IS LEAN CODE 🚨
**THE DELIVERABLE IS REAL LEAN FILES, NOT #checks, NOT COMMENTS, NOT DOCUMENTATION. DO NOT DELETE THIS REQUIREMENT**

## Session Orientation

`bd ready` returns later chapter issues first (no blockers set). Always prioritize Chapter 1-2 foundations before later chapters. Check issue numbering (TC X.Y.Z) and start with lowest chapter number.

## 🚨 ONLY ACCEPTABLE OUTPUT IS LEAN CODE 🚨
**THE DELIVERABLE IS REAL LEAN FILES, NOT #checks, NOT COMMENTS, NOT DOCUMENTATION. DO NOT DELETE THIS REQUIREMENT**

## Before Closing ANY Issue

```
[ ] Created/modified a .lean file? (NOT just docs)
[ ] The Lean code has REAL content (defs, theorems, proofs)?
[ ] `lake build` passes?
[ ] NOT just comments, placeholders, or documentation?
```

## 🚨 ONLY ACCEPTABLE OUTPUT IS LEAN CODE 🚨
**THE DELIVERABLE IS REAL LEAN FILES, NOT #checks, NOT COMMENTS, NOT DOCUMENTATION. DO NOT DELETE THIS REQUIREMENT**

## 🚨 ONLY ACCEPTABLE OUTPUT IS LEAN CODE 🚨
**THE DELIVERABLE IS REAL LEAN FILES, NOT #checks, NOT COMMENTS, NOT DOCUMENTATION. DO NOT DELETE THIS REQUIREMENT**
