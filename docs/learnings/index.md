# Learnings Index

This directory contains organized learnings from the Tensor Categories formalization project.

## Quick Links

| Document | Description |
|----------|-------------|
| [mathlib_mappings.md](mathlib_mappings.md) | Book ↔ mathlib correspondence tables |
| [api_gotchas.md](api_gotchas.md) | Common API issues and solutions |
| [proof_patterns.md](proof_patterns.md) | Reusable proof techniques |

## Chapter 1 Learnings

| Section | Document | Topics |
|---------|----------|--------|
| §1.1-1.3 | [chapter1/abelian.md](chapter1/abelian.md) | Categories, preadditive, abelian |
| §1.4 | [chapter1/exact_sequences.md](chapter1/exact_sequences.md) | Exact sequences, Ext, Baer sum, derivations |
| §1.5 | [chapter1/length_objects.md](chapter1/length_objects.md) | Simple, semisimple, finite length, Krull-Schmidt, Fitting |
| §1.6 | [chapter1/projective.md](chapter1/projective.md) | Projective/injective, exact functors |
| §1.7 | [chapter1/derived_functors.md](chapter1/derived_functors.md) | Derived functors, Ext, group cohomology |
| §1.9/1.13 | [chapter1/coalgebras.md](chapter1/coalgebras.md) | Coalgebras, grouplike, skew-primitive |
| §1.11-1.12 | [chapter1/deligne.md](chapter1/deligne.md) | External tensor product, Deligne tensor |

## Critical Reminders

**OUTPUT IS LEAN CODE.** Every issue must produce a `.lean` file. Documentation alone is NOT sufficient. See the critical failure documented in [chapter1/abelian.md](chapter1/abelian.md).

## Session Orientation

`bd ready` returns later chapter issues first (no blockers set). Always prioritize Chapter 1-2 foundations before later chapters. Check issue numbering (TC X.Y.Z) and start with lowest chapter number.
