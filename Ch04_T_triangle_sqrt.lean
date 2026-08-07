import Ch04_Defs

open scoped TensorProduct ComplexOrder
open Ch04
open TensorProduct (mapCLM)
noncomputable section

local notation "⟪" x ", " y "⟫" => inner ℂ x y

/-- **Triangle inequality, variant B: the quantitatively tight `(√δ + √ε)²`
form.** We believe this one is **TRUE** (and is the "honest" quantitative
reading of the paper's `O(δ+ε)` claim): viewing `a ↦ (M x a - N x a) ψ` as an
element of the product Hilbert space `H^A` for each `x`, the ordinary
triangle inequality gives `√(∑ a, ‖(M-O)ψ‖²) ≤ √(∑ a, ‖(M-N)ψ‖²) +
√(∑ a, ‖(N-O)ψ‖²)`; a *second* application of the triangle inequality, now
to the `μ`-weighted `L²(X)` (Minkowski's inequality for the weighted `ℓ²`
norm `x ↦ √(∑ a, ‖·‖²)`), gives `√(approxDist μ ψ M O) ≤
√(approxDist μ ψ M N) + √(approxDist μ ψ N O) ≤ √δ + √ε`; squaring both
(nonneg) sides gives the statement below. Not closed here: formalizing the
two-level Minkowski argument (inner over `A`, outer over `X` weighted by
`μ`) is more work than this drafting pass's budget, but unlike variant A
above we are not aware of any counterexample. -/
theorem triangle_sqrt {X A H : Type*} [Fintype X] [Fintype A]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (μ : Distr X) (ψ : H) (M N O : X → A → H →L[ℂ] H) (δ ε : ℝ) (hδ : 0 ≤ δ) (hε : 0 ≤ ε)
    (hMN : approxDist μ ψ M N ≤ δ) (hNO : approxDist μ ψ N O ≤ ε) :
    approxDist μ ψ M O ≤ (Real.sqrt δ + Real.sqrt ε) ^ 2 := by
  let f : X → ℝ := fun x => ∑ a, ‖(M x a - O x a) ψ‖ ^ 2
  let g : X → ℝ := fun x => ∑ a, ‖(M x a - N x a) ψ‖ ^ 2
  let h : X → ℝ := fun x => ∑ a, ‖(N x a - O x a) ψ‖ ^ 2
  change ∑ x, μ.p x * f x ≤ (Real.sqrt δ + Real.sqrt ε) ^ 2
  have hf_nonneg : ∀ x, 0 ≤ f x := by
    intro x; dsimp [f]; exact Finset.sum_nonneg fun a _ => sq_nonneg _
  have hg_nonneg : ∀ x, 0 ≤ g x := by
    intro x; dsimp [g]; exact Finset.sum_nonneg fun a _ => sq_nonneg _
  have hh_nonneg : ∀ x, 0 ≤ h x := by
    intro x; dsimp [h]; exact Finset.sum_nonneg fun a _ => sq_nonneg _
  -- Inner triangle inequality (over A), pointwise in x:
  -- √(f x) ≤ √(g x) + √(h x)
  have hinner : ∀ x, Real.sqrt (f x) ≤ Real.sqrt (g x) + Real.sqrt (h x) := by
    intro x
    have htri : ∀ a, ‖(M x a - O x a) ψ‖ ≤ ‖(M x a - N x a) ψ‖ + ‖(N x a - O x a) ψ‖ := by
      intro a
      calc
        ‖(M x a - O x a) ψ‖ = ‖(M x a - N x a) ψ + (N x a - O x a) ψ‖ := by
          congr 1
          rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
            ContinuousLinearMap.sub_apply]
          abel
        _ ≤ ‖(M x a - N x a) ψ‖ + ‖(N x a - O x a) ψ‖ := norm_add_le _ _
    have hsum : (∑ a, ‖(M x a - O x a) ψ‖ ^ 2) ≤
        (∑ a, (‖(M x a - N x a) ψ‖ + ‖(N x a - O x a) ψ‖) ^ 2) := by
      refine Finset.sum_le_sum fun a _ => ?_
      exact (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr (htri a)
    have hmink :
        Real.sqrt (∑ a, (‖(M x a - N x a) ψ‖ + ‖(N x a - O x a) ψ‖) ^ 2) ≤
          Real.sqrt (∑ a, ‖(M x a - N x a) ψ‖ ^ 2) + Real.sqrt (∑ a, ‖(N x a - O x a) ψ‖ ^ 2) := by
      let u : A → ℝ := fun a => ‖(M x a - N x a) ψ‖
      let v : A → ℝ := fun a => ‖(N x a - O x a) ψ‖
      have hu : ∀ a, 0 ≤ u a := fun a => norm_nonneg _
      have hv : ∀ a, 0 ≤ v a := fun a => norm_nonneg _
      have hm := Real.Lp_add_le (Finset.univ : Finset A) u v (by norm_num : (1 : ℝ) ≤ 2)
      rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hm
      simpa [Real.rpow_two, sq_abs, abs_of_nonneg, hu, hv, u, v] using hm
    calc
      Real.sqrt (f x) ≤ Real.sqrt (∑ a, (‖(M x a - N x a) ψ‖ + ‖(N x a - O x a) ψ‖) ^ 2) := by
        dsimp [f]
        exact Real.sqrt_le_sqrt hsum
      _ ≤ Real.sqrt (∑ a, ‖(M x a - N x a) ψ‖ ^ 2) + Real.sqrt (∑ a, ‖(N x a - O x a) ψ‖ ^ 2) := hmink
      _ = Real.sqrt (g x) + Real.sqrt (h x) := by simp [g, h]
  -- pointwise squared version: f x ≤ (√(g x) + √(h x))²
  have hinner_sq : ∀ x, f x ≤ (Real.sqrt (g x) + Real.sqrt (h x)) ^ 2 := by
    intro x
    calc
      f x = (Real.sqrt (f x)) ^ 2 := (Real.sq_sqrt (hf_nonneg x)).symm
      _ ≤ (Real.sqrt (g x) + Real.sqrt (h x)) ^ 2 := by
        exact (sq_le_sq₀ (Real.sqrt_nonneg _)
          (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr (hinner x)
  -- μ-weighted pointwise bound
  have hsum_f_le : (∑ x, μ.p x * f x) ≤ ∑ x, μ.p x * (Real.sqrt (g x) + Real.sqrt (h x)) ^ 2 := by
    refine Finset.sum_le_sum fun x _ => ?_
    exact mul_le_mul_of_nonneg_left (hinner_sq x) (μ.nonneg x)
  -- Outer Minkowski (weighted ℓ² over X):
  -- √(∑ x, μ.p x * (√(g x) + √(h x))²) ≤ √(∑ x, μ.p x * g x) + √(∑ x, μ.p x * h x)
  have houter :
      Real.sqrt (∑ x, μ.p x * (Real.sqrt (g x) + Real.sqrt (h x)) ^ 2) ≤
        Real.sqrt (∑ x, μ.p x * g x) + Real.sqrt (∑ x, μ.p x * h x) := by
    let u : X → ℝ := fun x => Real.sqrt (μ.p x) * Real.sqrt (g x)
    let v : X → ℝ := fun x => Real.sqrt (μ.p x) * Real.sqrt (h x)
    have hu : ∀ x, 0 ≤ u x := fun x => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hv : ∀ x, 0 ≤ v x := fun x => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hm := Real.Lp_add_le (Finset.univ : Finset X) u v (by norm_num : (1 : ℝ) ≤ 2)
    rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hm
    have hm' : Real.sqrt (∑ x, (u x + v x) ^ 2) ≤
        Real.sqrt (∑ x, u x ^ 2) + Real.sqrt (∑ x, v x ^ 2) := by
      simpa [Real.rpow_two, sq_abs, abs_of_nonneg, hu, hv] using hm
    have hsq1 : ∀ x, (u x + v x) ^ 2 = μ.p x * (Real.sqrt (g x) + Real.sqrt (h x)) ^ 2 := by
      intro x
      calc
        (u x + v x) ^ 2 = (Real.sqrt (μ.p x) * (Real.sqrt (g x) + Real.sqrt (h x))) ^ 2 := by
          congr 1
          simp [u, v, mul_add]
        _ = (Real.sqrt (μ.p x)) ^ 2 * (Real.sqrt (g x) + Real.sqrt (h x)) ^ 2 := by
          rw [mul_pow]
        _ = μ.p x * (Real.sqrt (g x) + Real.sqrt (h x)) ^ 2 := by
          rw [Real.sq_sqrt (μ.nonneg x)]
    have hsq2 : ∀ x, u x ^ 2 = μ.p x * g x := by
      intro x
      calc
        u x ^ 2 = (Real.sqrt (μ.p x)) ^ 2 * (Real.sqrt (g x)) ^ 2 := by
          simp [u, mul_pow]
        _ = μ.p x * (Real.sqrt (g x)) ^ 2 := by rw [Real.sq_sqrt (μ.nonneg x)]
        _ = μ.p x * g x := by rw [Real.sq_sqrt (hg_nonneg x)]
    have hsq3 : ∀ x, v x ^ 2 = μ.p x * h x := by
      intro x
      calc
        v x ^ 2 = (Real.sqrt (μ.p x)) ^ 2 * (Real.sqrt (h x)) ^ 2 := by
          simp [v, mul_pow]
        _ = μ.p x * (Real.sqrt (h x)) ^ 2 := by rw [Real.sq_sqrt (μ.nonneg x)]
        _ = μ.p x * h x := by rw [Real.sq_sqrt (hh_nonneg x)]
    simpa [hsq1, hsq2, hsq3] using hm'
  -- assemble: √(∑ x, μ.p x * f x) ≤ √δ + √ε
  have hsqrt_f_le :
      Real.sqrt (∑ x, μ.p x * f x) ≤
        Real.sqrt (∑ x, μ.p x * (Real.sqrt (g x) + Real.sqrt (h x)) ^ 2) := by
    exact Real.sqrt_le_sqrt hsum_f_le
  have hsqrt_total : Real.sqrt (∑ x, μ.p x * f x) ≤
      Real.sqrt (∑ x, μ.p x * g x) + Real.sqrt (∑ x, μ.p x * h x) := by
    exact le_trans hsqrt_f_le houter
  have hMN' : (∑ x, μ.p x * g x) ≤ δ := by
    simpa [approxDist, E, g] using hMN
  have hNO' : (∑ x, μ.p x * h x) ≤ ε := by
    simpa [approxDist, E, h] using hNO
  have hsqrt_MN : Real.sqrt (∑ x, μ.p x * g x) ≤ Real.sqrt δ := Real.sqrt_le_sqrt hMN'
  have hsqrt_NO : Real.sqrt (∑ x, μ.p x * h x) ≤ Real.sqrt ε := Real.sqrt_le_sqrt hNO'
  have hsqrt_total' : Real.sqrt (∑ x, μ.p x * f x) ≤ Real.sqrt δ + Real.sqrt ε := by
    exact le_trans hsqrt_total (add_le_add hsqrt_MN hsqrt_NO)
  -- square both (nonneg) sides
  have hsq_total : (Real.sqrt (∑ x, μ.p x * f x)) ^ 2 ≤ (Real.sqrt δ + Real.sqrt ε) ^ 2 := by
    exact (sq_le_sq₀ (Real.sqrt_nonneg _)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mpr hsqrt_total'
  have hf_sum_nonneg : 0 ≤ ∑ x, μ.p x * f x := by
    exact Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonneg x) (hf_nonneg x)
  rw [Real.sq_sqrt hf_sum_nonneg] at hsq_total
  exact hsq_total
