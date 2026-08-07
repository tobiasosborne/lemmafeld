import Ch04_Defs

/-!
# Ch04 distance-toolkit lemmas (MIP*=RE §4) — statements-only skeleton

Drafted per `campaign_ch04/DESIGN.md` (v1.2, frozen 2026-08-07) over the frozen
vocabulary in `Ch04_Defs.lean`. This file is **sorry-bodied only**: every
theorem below elaborates (type-checks its statement) but proves nothing.
Constants that are quantitatively uncertain are tagged `-- CONSTANT TO
VALIDATE` with the derivation reasoning inline; see the final report for a
consolidated list.

Sources read: `tex/fact_agreement.tex`, `tex/fact_add_a_proj.tex`,
`tex/fact_add_a_proj2.tex`, `tex/lem_cool_closeness_fact.tex`,
`tex/lem_commutation_analysis.tex`,
`tex/lem_close_strategies_have_close_values.tex`,
`tex/fact_data_processing.tex`, and the validated `af_triangle` proof tree
(nodes 1.1–1.3) for the exact quantitative form of fact:agreement part 1.

Per DESIGN.md v1.2 §J.2: the naive `δ+ε`-style triangle constant is
quantitatively FALSE; the honest bound from expanding a square is
`(√δ+√ε)² = 2(δ+ε)` in the worst case, or better with Cauchy–Schwarz
refinement. This file uses that honest form wherever a triangle-style
combination is needed (see `commutation_analysis`).
-/

set_option linter.unusedVariables false

open scoped Ch04 TensorProduct ComplexOrder
open TensorProduct (mapCLM)

namespace Ch04

/-!
## 8. `fact:data-processing` (Fact 4.26 of NW19)

Paper (`fact_data_processing.tex`, terse): `A^x_a ≈_δ B^x_a` (or `≃_δ`,
per the source's relation-agnostic `\abc` macro) implies
`A^x_{f⁻¹(b)} ≈_δ B^x_{f⁻¹(b)}` for outcome-coarsening
`M^x_{f⁻¹(b)} := ∑_{a : f(a)=b} M^x_a` along `f : Aalpha → Balpha`.

**CONSTANT VALIDATED (`|Aalpha|·δ`, NOT the same `δ`) — numerics verdict,
`data_processing` targets (see orchestrator's numerics adjudication):**
a 500-trial random sweep (d=2..4, |X|,|A|=2..4, |B|<|A| coarsening) shows
the naive same-`δ` claim (`delta_coarse ≤ delta`) is VIOLATED for arbitrary
(non-POVM) operator families in 247/500 trials (worst ratio
`delta_coarse/delta = 2.09`). Restricting to genuine (Ginibre-normalized)
POVM pairs for both `M` and `N` shrinks but does NOT eliminate the
violation (7/500 trials, max ratio 1.164) — so the fiber-size effect is
real even under POVM hypotheses, just smaller. In all 500 trials (both the
RAW and POVM sweeps) the `|Aalpha|·δ` bound below held with zero
violations, confirming it is the correct, non-overconservative constant to
keep — the Cauchy–Schwarz fiber-size factor is genuinely load-bearing and
not filler slack. No change to the statement is warranted. -/
theorem data_processing {X Aalpha Balpha H : Type*}
    [Fintype X] [Fintype Aalpha] [Fintype Balpha] [DecidableEq Balpha]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (μ : Distr X) (ψ : H) (M N : X → Aalpha → H →L[ℂ] H) (f : Aalpha → Balpha) (δ : ℝ)
    (h : Approx μ ψ M N δ) :
    Approx μ ψ
      (fun x b => ∑ a ∈ Finset.filter (fun a => f a = b) Finset.univ, M x a)
      (fun x b => ∑ a ∈ Finset.filter (fun a => f a = b) Finset.univ, N x a)
      (Fintype.card Aalpha * δ) := by
  classical
  simp [Approx, approxDist, E] at h ⊢
  let F : Balpha → Finset Aalpha := fun b => Finset.filter (fun a => f a = b) Finset.univ
  -- For each question x, bound the coarsened (fiberwise) sum by Cauchy-Schwarz:
  -- ‖∑ a∈f⁻¹(b) v_a‖² ≤ |f⁻¹(b)| · ∑ a∈f⁻¹(b) ‖v_a‖², summed over the fibers b.
  have hx (x : X) :
      (∑ b : Balpha, ‖(∑ a ∈ F b, (M x a) ψ) - (∑ a ∈ F b, (N x a) ψ)‖ ^ 2) ≤
      (Fintype.card Aalpha : ℝ) * (∑ a : Aalpha, ‖(M x a) ψ - (N x a) ψ‖ ^ 2) := by
    let v : Aalpha → H := fun a => (M x a) ψ - (N x a) ψ
    have hw (b : Balpha) : (∑ a ∈ F b, (M x a) ψ) - (∑ a ∈ F b, (N x a) ψ) = ∑ a ∈ F b, v a := by
      rw [← Finset.sum_sub_distrib]
    have hfib (b : Balpha) : ‖∑ a ∈ F b, v a‖ ^ 2 ≤ (F b).card * ∑ a ∈ F b, ‖v a‖ ^ 2 := by
      have hn : ‖∑ a ∈ F b, v a‖ ≤ ∑ a ∈ F b, ‖v a‖ := norm_sum_le (F b) v
      have hcs' := Finset.sum_mul_sq_le_sq_mul_sq (F b) (fun a => ‖v a‖) (fun _ => (1 : ℝ))
      have hcs : (∑ a ∈ F b, ‖v a‖) ^ 2 ≤ (F b).card * ∑ a ∈ F b, ‖v a‖ ^ 2 := by
        simpa [mul_comm] using hcs'
      exact le_trans ((sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg fun a _ => norm_nonneg _)).2 hn) hcs
    calc
      (∑ b : Balpha, ‖(∑ a ∈ F b, (M x a) ψ) - (∑ a ∈ F b, (N x a) ψ)‖ ^ 2)
          = ∑ b : Balpha, ‖∑ a ∈ F b, v a‖ ^ 2 := by
              apply Finset.sum_congr rfl
              intro b hb
              rw [hw b]
      _ ≤ ∑ b : Balpha, (F b).card * ∑ a ∈ F b, ‖v a‖ ^ 2 := by
              exact Finset.sum_le_sum (fun b _ => hfib b)
      _ ≤ ∑ b : Balpha, (Fintype.card Aalpha : ℝ) * ∑ a ∈ F b, ‖v a‖ ^ 2 := by
              refine Finset.sum_le_sum (fun b _ => ?_)
              exact mul_le_mul_of_nonneg_right
                (Nat.cast_le.mpr (Finset.card_le_card (Finset.subset_univ (F b))))
                (Finset.sum_nonneg fun a _ => sq_nonneg _)
      _ = (Fintype.card Aalpha : ℝ) * ∑ b : Balpha, ∑ a ∈ F b, ‖v a‖ ^ 2 := by
              rw [Finset.mul_sum]
      _ = (Fintype.card Aalpha : ℝ) * ∑ a : Aalpha, ‖v a‖ ^ 2 := by
              rw [Finset.sum_fiberwise Finset.univ f (fun a => ‖v a‖ ^ 2)]
  -- Weight by μ.p x and sum over x, then use the hypothesis h.
  calc
    (∑ x : X, μ.p x * (∑ b : Balpha, ‖(∑ a ∈ F b, (M x a) ψ) - (∑ a ∈ F b, (N x a) ψ)‖ ^ 2))
        ≤ ∑ x : X, μ.p x * ((Fintype.card Aalpha : ℝ) * (∑ a : Aalpha, ‖(M x a) ψ - (N x a) ψ‖ ^ 2)) := by
            refine Finset.sum_le_sum (fun x _ => ?_)
            exact mul_le_mul_of_nonneg_left (hx x) (μ.nonneg x)
    _ = (Fintype.card Aalpha : ℝ) * (∑ x : X, μ.p x * (∑ a : Aalpha, ‖(M x a) ψ - (N x a) ψ‖ ^ 2)) := by
            calc
              (∑ x : X, μ.p x * ((Fintype.card Aalpha : ℝ) * (∑ a : Aalpha, ‖(M x a) ψ - (N x a) ψ‖ ^ 2)))
                  = ∑ x : X, (Fintype.card Aalpha : ℝ) * (μ.p x * (∑ a : Aalpha, ‖(M x a) ψ - (N x a) ψ‖ ^ 2)) := by
                      apply Finset.sum_congr rfl
                      intro x hx
                      ring
              _ = (Fintype.card Aalpha : ℝ) * (∑ x : X, μ.p x * (∑ a : Aalpha, ‖(M x a) ψ - (N x a) ψ‖ ^ 2)) := by
                      exact (Finset.mul_sum Finset.univ (fun x : X => μ.p x * (∑ a : Aalpha, ‖(M x a) ψ - (N x a) ψ‖ ^ 2)) (Fintype.card Aalpha : ℝ)).symm
    _ ≤ (Fintype.card Aalpha : ℝ) * δ := by
            exact mul_le_mul_of_nonneg_left h (by positivity)

end Ch04
