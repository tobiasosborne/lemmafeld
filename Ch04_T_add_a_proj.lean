import Ch04_Defs

set_option linter.unusedVariables false

open scoped Ch04 TensorProduct ComplexOrder
open TensorProduct (mapCLM)

namespace Ch04

local notation "⟪" x ", " y "⟫" => inner ℂ x y

theorem add_a_proj {X Y Aalpha Balpha Calpha H : Type*}
    [Fintype X] [Fintype Y] [Fintype Aalpha] [Fintype Balpha] [Fintype Calpha]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (μ : Distr (X × Y)) (ψ : H)
    (Afam Bfam : X → Aalpha → Balpha → H →L[ℂ] H)
    (Cfam : Y → Aalpha → Calpha → H →L[ℂ] H)
    (hC : ∀ y a, (∑ c, star (Cfam y a c) * Cfam y a c) ≤ (1 : H →L[ℂ] H))
    (δ : ℝ)
    (h : Approx μ.fst ψ (fun x (p : Aalpha × Balpha) => Afam x p.1 p.2)
      (fun x (p : Aalpha × Balpha) => Bfam x p.1 p.2) δ) :
    Approx μ ψ
      (fun (xy : X × Y) (t : Aalpha × Balpha × Calpha) =>
        Cfam xy.2 t.1 t.2.2 * Afam xy.1 t.1 t.2.1)
      (fun (xy : X × Y) (t : Aalpha × Balpha × Calpha) =>
        Cfam xy.2 t.1 t.2.2 * Bfam xy.1 t.1 t.2.1)
      δ := by
  simp [Approx, approxDist, E] at h ⊢
  -- Core quadratic-form bound: for fixed (y, a) and vector v,
  --   ∑ c ‖Cfam y a c v‖² ≤ ‖v‖²
  -- follows from the sub-isometry hypothesis ∑ c (Cfam y a c)† (Cfam y a c) ≤ 1.
  have hcore (y : Y) (a : Aalpha) (v : H) :
      (∑ c : Calpha, ‖Cfam y a c v‖ ^ 2) ≤ ‖v‖ ^ 2 := by
    let S : H →L[ℂ] H := ∑ c, star (Cfam y a c) * Cfam y a c
    have hpos : (1 - S).IsPositive := by
      simpa [S] using hC y a
    have hreS : RCLike.re ⟪v, S v⟫ ≤ ‖v‖ ^ 2 := by
      have hre : 0 ≤ RCLike.re ⟪v, (1 - S) v⟫ := hpos.re_inner_nonneg_right v
      have heq : RCLike.re ⟪v, (1 - S) v⟫ = ‖v‖ ^ 2 - RCLike.re ⟪v, S v⟫ := by
        calc
          RCLike.re ⟪v, (1 - S) v⟫ = RCLike.re ⟪v, v - S v⟫ := by
            simp [ContinuousLinearMap.sub_apply]
          _ = RCLike.re (⟪v, v⟫ - ⟪v, S v⟫) := by rw [inner_sub_right]
          _ = RCLike.re ⟪v, v⟫ - RCLike.re ⟪v, S v⟫ := by rw [map_sub]
          _ = ‖v‖ ^ 2 - RCLike.re ⟪v, S v⟫ := by rw [inner_self_eq_norm_sq]
      rw [heq] at hre
      exact sub_nonneg.mp hre
    have hsum_eq : RCLike.re ⟪v, S v⟫ = ∑ c : Calpha, ‖Cfam y a c v‖ ^ 2 := by
      calc
        RCLike.re ⟪v, S v⟫ = RCLike.re ⟪v, (∑ c, star (Cfam y a c) * Cfam y a c) v⟫ := by
          rfl
        _ = RCLike.re (∑ c, ⟪v, (star (Cfam y a c) * Cfam y a c) v⟫) := by
          rw [ContinuousLinearMap.sum_apply]
          congr 1
          rw [inner_sum]
        _ = ∑ c, RCLike.re ⟪v, (star (Cfam y a c) * Cfam y a c) v⟫ := by rw [map_sum]
        _ = ∑ c, ‖Cfam y a c v‖ ^ 2 := by
          refine Finset.sum_congr rfl (fun c _ => ?_)
          simpa [ContinuousLinearMap.mul_def, ContinuousLinearMap.star_eq_adjoint] using
            (ContinuousLinearMap.apply_norm_sq_eq_inner_adjoint_right (Cfam y a c) v).symm
    calc
      (∑ c : Calpha, ‖Cfam y a c v‖ ^ 2) = RCLike.re ⟪v, S v⟫ := by rw [hsum_eq]
      _ ≤ ‖v‖ ^ 2 := hreS
  -- Pointwise (over a, b, c) inequality for each question (x, y):
  --   ‖Cfam y a c (Afam x a b - Bfam x a b) ψ‖² ≤ ‖(Afam x a b - Bfam x a b) ψ‖²
  -- summed over a, b, c.
  have hxy (x : X) (y : Y) :
      (∑ t : Aalpha × Balpha × Calpha,
        ‖(Cfam y t.1 t.2.2 * Afam x t.1 t.2.1 - Cfam y t.1 t.2.2 * Bfam x t.1 t.2.1) ψ‖ ^ 2) ≤
      (∑ p : Aalpha × Balpha, ‖(Afam x p.1 p.2 - Bfam x p.1 p.2) ψ‖ ^ 2) := by
    simp only [Fintype.sum_prod_type]
    refine Finset.sum_le_sum (fun a _ => ?_)
    refine Finset.sum_le_sum (fun b _ => ?_)
    have key : ∑ c, ‖(Cfam y a c * Afam x a b - Cfam y a c * Bfam x a b) ψ‖ ^ 2 =
        ∑ c, ‖(Cfam y a c * (Afam x a b - Bfam x a b)) ψ‖ ^ 2 := by
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [mul_sub]
    rw [key]
    simp only [ContinuousLinearMap.mul_apply]
    exact hcore y a ((Afam x a b - Bfam x a b) ψ)
  -- Multiply by μ.p (xy) and sum over xy; the inner sums are bounded pointwise.
  have hstep :
      (∑ xy : X × Y, μ.p xy *
        (∑ t : Aalpha × Balpha × Calpha,
          ‖(Cfam xy.2 t.1 t.2.2 * Afam xy.1 t.1 t.2.1 - Cfam xy.2 t.1 t.2.2 * Bfam xy.1 t.1 t.2.1) ψ‖ ^ 2)) ≤
      (∑ xy : X × Y, μ.p xy *
        (∑ p : Aalpha × Balpha, ‖(Afam xy.1 p.1 p.2 - Bfam xy.1 p.1 p.2) ψ‖ ^ 2)) := by
    refine Finset.sum_le_sum (fun xy _ => ?_)
    exact mul_le_mul_of_nonneg_left (hxy xy.1 xy.2) (μ.nonneg xy)
  -- Re-index the xy-sum through the x-marginal: ∑ xy μ.p xy · S_{xy.1} = ∑ x μ.fst.p x · S_x.
  have hsum2 :
      (∑ xy : X × Y, μ.p xy *
        (∑ p : Aalpha × Balpha, ‖(Afam xy.1 p.1 p.2 - Bfam xy.1 p.1 p.2) ψ‖ ^ 2)) =
      (∑ x : X, μ.fst.p x *
        (∑ p : Aalpha × Balpha, ‖(Afam x p.1 p.2 - Bfam x p.1 p.2) ψ‖ ^ 2)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    simp [Distr.fst, Finset.sum_mul]
  calc
    (∑ xy : X × Y, μ.p xy *
        (∑ t : Aalpha × Balpha × Calpha,
          ‖(Cfam xy.2 t.1 t.2.2 * Afam xy.1 t.1 t.2.1 - Cfam xy.2 t.1 t.2.2 * Bfam xy.1 t.1 t.2.1) ψ‖ ^ 2)) ≤
      (∑ xy : X × Y, μ.p xy *
        (∑ p : Aalpha × Balpha, ‖(Afam xy.1 p.1 p.2 - Bfam xy.1 p.1 p.2) ψ‖ ^ 2)) := hstep
    _ = (∑ x : X, μ.fst.p x *
        (∑ p : Aalpha × Balpha, ‖(Afam x p.1 p.2 - Bfam x p.1 p.2) ψ‖ ^ 2)) := hsum2
    _ ≤ δ := h

end Ch04
