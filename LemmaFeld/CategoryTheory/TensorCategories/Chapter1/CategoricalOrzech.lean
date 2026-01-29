/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.IterateComap
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.FittingLemma

/-!
# Categorical Orzech Theorem

We prove that an epimorphic endomorphism on a Noetherian object is a monomorphism.
This is the categorical analog of `IsNoetherian.injective_of_surjective_endomorphism`
from `Mathlib.RingTheory.Noetherian.Orzech`.

## Main Results

* `mono_of_epi_endomorphism_noetherianObject`: An epi endomorphism on a Noetherian object is mono.
* `isIso_of_epi_endomorphism_noetherianObject`: An epi endomorphism on a Noetherian object is iso.

## References

* Djoković, *Epimorphisms of modules which must be isomorphisms* [djokovic1973]
* §1.5 of Etingof et al. "Tensor Categories" (AMS 2015)
-/

noncomputable section

namespace CategoryTheory

open CategoryTheory CategoryTheory.Limits Subobject
open LemmaFeld.TensorCategories.Chapter1

variable {C : Type*} [Category C] [Abelian C]

/-! ## Connection: iterateComap and kernelSubobject of powers -/

section IterateComapKernel

variable {X : C} (f : End X)

/-- The pullback of kernelSubobject g along f equals kernelSubobject (f ≫ g).
This is the categorical version of f⁻¹(ker g) = ker(g ∘ f). -/
theorem pullback_kernelSubobject_eq (g : End X) :
    (Subobject.pullback f).obj (kernelSubobject g) = kernelSubobject (f ≫ g) := by
  -- Construct the induced map kernel(f ≫ g) → kernel(g)
  let k : kernel (f ≫ g) ⟶ kernel g :=
    kernel.lift g (kernel.ι (f ≫ g) ≫ f) (by simp [kernel.condition])
  -- Show the square commutes: k ≫ kernel.ι g = kernel.ι (f ≫ g) ≫ f
  have hsq : k ≫ kernel.ι g = kernel.ι (f ≫ g) ≫ f := kernel.lift_ι _ _ _
  -- Build the IsPullback
  have hp : IsPullback k (kernel.ι (f ≫ g)) (kernel.ι g) f := by
    refine IsPullback.of_isLimit (c := PullbackCone.mk k (kernel.ι (f ≫ g)) hsq) ?_
    refine PullbackCone.isLimitAux' _ ?_
    intro s
    -- s.fst : W ⟶ kernel g, s.snd : W ⟶ X
    -- s.condition : s.fst ≫ kernel.ι g = s.snd ≫ f
    -- Need to show s.snd factors through kernel (f ≫ g)
    have hcond : s.snd ≫ (f ≫ g) = 0 := by
      rw [← Category.assoc, ← s.condition, Category.assoc, kernel.condition, comp_zero]
    let ℓ : s.pt ⟶ kernel (f ≫ g) := kernel.lift (f ≫ g) s.snd hcond
    refine ⟨ℓ, ?_, kernel.lift_ι _ _ _, ?_⟩
    -- First: ℓ ≫ k = s.fst (show by composing with kernel.ι g)
    · apply equalizer.hom_ext
      rw [PullbackCone.mk_fst, Category.assoc, hsq, ← Category.assoc, kernel.lift_ι, s.condition]
    -- Second: uniqueness
    · intro m _ hm2
      apply equalizer.hom_ext
      rw [kernel.lift_ι]
      exact hm2
  rw [kernelSubobject, kernelSubobject]
  exact pullback_obj_mk hp

/-- iterateComap f ⊥ n = kernelSubobject (f ^ n) for n ≥ 1.
This connects the pullback-based iterateComap with kernelSubobject of powers. -/
theorem iterateComap_bot_eq_kernelSubobject_pow (n : ℕ) (hn : 0 < n) :
    iterateComap f (⊥ : Subobject X) n = kernelSubobject (f ^ n) := by
  induction n with
  | zero => exact (Nat.not_lt_zero 0 hn).elim
  | succ n ih =>
    cases n with
    | zero =>
      rw [iterateComap_succ, iterateComap_zero]
      rw [pullback_bot_eq_kernelSubobject f]
      congr 1
      exact (pow_one f).symm
    | succ m =>
      rw [iterateComap_succ, ih (Nat.succ_pos m)]
      rw [pow_succ, End.mul_def]
      exact pullback_kernelSubobject_eq f (f ^ (m + 1))

end IterateComapKernel

/-! ## Helper: Epi nilpotent endomorphism implies zero object -/

section EpiNilpotent

variable {Y : C} (g : End Y) [hg : Epi g]

/-- An epi endomorphism that composes to zero implies the source is zero.
Key lemma: if g ^ n = 0 and g is epi, then g ^ (n-1) = 0, and by induction, Y is zero. -/
theorem isZero_of_epi_pow_eq_zero (n : ℕ) (hn : 0 < n) (heq : g ^ n = 0) : IsZero Y := by
  induction n with
  | zero => exact (Nat.not_lt_zero 0 hn).elim
  | succ m ih =>
    cases m with
    | zero =>
      -- g^1 = g = 0, and g is epi, so Y is zero
      rw [pow_one] at heq
      exact IsZero.of_epi_eq_zero g heq
    | succ k =>
      -- g^(k+2) = g^(k+1) * g = g ≫ g^(k+1) = 0
      -- Since g is epi, g^(k+1) = 0
      -- Note: End multiplication is x * y = y ≫ x, so g^(k+1) * g = g ≫ g^(k+1)
      have hpow : g^(k + 2) = g^(k + 1) * g := pow_succ g (k + 1)
      rw [hpow, End.mul_def] at heq
      -- Now heq : g ≫ g^(k+1) = 0
      have heq' : g^(k + 1) = 0 := by
        have h0 : g ≫ (0 : Y ⟶ Y) = 0 := comp_zero
        rw [← h0] at heq
        exact (cancel_epi g).mp heq
      exact ih (Nat.succ_pos k) heq'

end EpiNilpotent

/-! ## Main Theorem: Categorical Orzech -/

section CategoricalOrzech

variable {X : C} (f : End X)

open scoped ZeroObject in
/-- The kernel.ι of an isomorphism is zero. -/
theorem kernel_ι_eq_zero_of_isIso [IsIso f] : kernel.ι f = 0 := by
  -- kernel f ≅ 0 for iso (hence mono) f
  have hker : kernel f ≅ (0 : C) := kernel.ofMono f
  -- kernel.ι f : kernel f ⟶ X where kernel f ≅ 0
  have hzero : IsZero (kernel f) := hker.isZero_iff.mpr (isZero_zero C)
  exact hzero.eq_zero_of_src (kernel.ι f)

/-- The kernelSubobject of an isomorphism is ⊥. -/
theorem kernelSubobject_of_isIso [IsIso f] : kernelSubobject f = ⊥ := by
  rw [mk_eq_bot_iff_zero]
  exact kernel_ι_eq_zero_of_isIso f

variable [hf : Epi f] [IsNoetherianObject X]

/-- Key lemma: When f is epi and the kernel chain stabilizes, kernelSubobject f = ⊥.

The proof strategy (Djoković):
1. Chain stabilization means ker(f^n) = ker(f^(n+1)), i.e., ker(f^n) is f-saturated
2. When f is epi, the restriction of f to ker(f^n) is also epi
3. Since f^n kills ker(f^n), the restriction is nilpotent
4. Epi + nilpotent on ker(f^n) implies ker(f^n) = 0
5. Since kernelSubobject f ≤ ker(f^n) = 0, we get kernelSubobject f = 0 -/
theorem kernelSubobject_eq_bot_of_epi_noetherian : kernelSubobject f = ⊥ := by
  -- Get stabilization point from Noetherian property
  obtain ⟨n, hn⟩ := kernelSubobject_stabilizes f
  -- Case split on stabilization point
  by_cases hn0 : n = 0
  · -- Stabilizes at 0: kernelSubobject (f^0) = kernelSubobject (f^1) = kernelSubobject f
    subst hn0
    have h01 : kernelSubobject (f ^ 0) = kernelSubobject (f ^ 1) := hn 1 (Nat.zero_le 1)
    have hone : (f ^ (0 : ℕ) : End X) = 𝟙 X := by rw [pow_zero, End.one_def]
    have hiso : IsIso (f ^ (0 : ℕ) : End X) := by rw [hone]; infer_instance
    have h0 : kernelSubobject (f ^ (0 : ℕ)) = ⊥ := @kernelSubobject_of_isIso C _ _ X (f^0) hiso
    rw [pow_one] at h01
    rw [← h01, h0]
  · -- n ≥ 1 case: the full Orzech argument is needed
    push_neg at hn0
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    -- kernelSubobject f ≤ kernelSubobject (f^n) by monotonicity
    have hker_le : kernelSubobject f ≤ kernelSubobject (f ^ n) := by
      have h1 : kernelSubobject f = kernelSubobject (f ^ 1) := by rw [pow_one]
      rw [h1]
      exact kernelSubobject_le_of_le f (Nat.one_le_of_lt hn_pos)
    -- Step 1: Saturation - ker(f^n) = ker(f^(n+1))
    have hsat : kernelSubobject (f ^ n) = kernelSubobject (f ^ (n + 1)) :=
      hn (n + 1) (Nat.le_succ n)
    -- This means mk (kernel.ι (f^n)) = mk (kernel.ι (f^(n+1)))
    -- Step 2: Extract isomorphism from saturation
    let φ := Subobject.isoOfMkEqMk (kernel.ι (f ^ n)) (kernel.ι (f ^ (n + 1))) hsat
    -- φ.hom : kernel (f^n) → kernel (f^(n+1)) with φ.hom ≫ kernel.ι (f^(n+1)) = kernel.ι (f^n)
    have hφ : φ.hom ≫ kernel.ι (f ^ (n + 1)) = kernel.ι (f ^ n) := Subobject.ofMkLEMk_comp hsat.le
    -- Step 3: Construct induced map k : kernel (f^(n+1)) → kernel (f^n)
    -- from the pullback square
    -- Note: pow_succ gives f^(n+1) = f^n * f, and in End, x * y = y ≫ x
    -- So f^(n+1) = f^n * f = f ≫ f^n
    have hpow : (f ^ (n + 1) : End X) = f ≫ f ^ n := by rw [pow_succ, End.mul_def]
    let k : kernel (f ^ (n + 1)) ⟶ kernel (f ^ n) :=
      kernel.lift (f ^ n) (kernel.ι (f ^ (n + 1)) ≫ f) (by
        rw [Category.assoc, ← hpow, kernel.condition])
    have hk : k ≫ kernel.ι (f ^ n) = kernel.ι (f ^ (n + 1)) ≫ f := kernel.lift_ι _ _ _
    -- Step 4: k is epi (pullback stability in abelian category)
    have hk_epi : Epi k := by
      -- The square forms a pullback (from pullback_kernelSubobject_eq)
      -- Build the limit cone directly
      have hp : IsPullback k (kernel.ι (f ^ (n + 1))) (kernel.ι (f ^ n)) f := by
        refine IsPullback.of_isLimit (c := PullbackCone.mk k (kernel.ι (f ^ (n + 1))) hk) ?_
        refine PullbackCone.isLimitAux' _ ?_
        intro s
        -- s.condition : s.fst ≫ kernel.ι (f^n) = s.snd ≫ f
        have hcond : s.snd ≫ f ^ (n + 1) = 0 := by
          rw [hpow, ← Category.assoc, ← s.condition, Category.assoc, kernel.condition, comp_zero]
        let ℓ := kernel.lift (f ^ (n + 1)) s.snd hcond
        refine ⟨ℓ, ?_, kernel.lift_ι _ _ _, ?_⟩
        -- ℓ ≫ k = s.fst
        · apply equalizer.hom_ext
          rw [PullbackCone.mk_fst, Category.assoc, hk, ← Category.assoc, kernel.lift_ι, s.condition]
        -- Uniqueness
        · intro m' _ hm2
          apply equalizer.hom_ext
          rw [kernel.lift_ι]
          exact hm2
      -- f is epi, so by pullback stability, k is epi
      exact Abelian.epi_fst_of_isLimit _ f hp.isLimit
    -- Step 5: Define induced endomorphism g : kernel (f^n) → kernel (f^n)
    let g : End (kernel (f ^ n)) := φ.hom ≫ k
    -- g satisfies: g ≫ kernel.ι (f^n) = kernel.ι (f^n) ≫ f
    have hg : g ≫ kernel.ι (f ^ n) = kernel.ι (f ^ n) ≫ f := by
      calc g ≫ kernel.ι (f ^ n)
          = (φ.hom ≫ k) ≫ kernel.ι (f ^ n) := rfl
        _ = φ.hom ≫ (k ≫ kernel.ι (f ^ n)) := by rw [Category.assoc]
        _ = φ.hom ≫ (kernel.ι (f ^ (n + 1)) ≫ f) := by rw [hk]
        _ = (φ.hom ≫ kernel.ι (f ^ (n + 1))) ≫ f := by rw [← Category.assoc]
        _ = kernel.ι (f ^ n) ≫ f := by rw [hφ]
    -- Step 6: g is epi (composition of iso and epi)
    have hg_epi : Epi g := epi_comp φ.hom k
    -- Step 7: Show g^n = 0 (nilpotent)
    -- By induction: g^m ≫ kernel.ι (f^n) = kernel.ι (f^n) ≫ f^m
    have hgpow : ∀ m : ℕ, (g ^ m) ≫ kernel.ι (f ^ n) = kernel.ι (f ^ n) ≫ (f ^ m) := by
      intro m
      induction m with
      | zero => simp only [pow_zero, End.one_def, Category.id_comp, Category.comp_id]
      | succ m ih =>
        calc (g ^ (m + 1)) ≫ kernel.ι (f ^ n)
            = (g ^ m * g) ≫ kernel.ι (f ^ n) := by rw [pow_succ]
          _ = (g ≫ (g ^ m)) ≫ kernel.ι (f ^ n) := by rw [End.mul_def]
          _ = g ≫ ((g ^ m) ≫ kernel.ι (f ^ n)) := by rw [Category.assoc]
          _ = g ≫ (kernel.ι (f ^ n) ≫ (f ^ m)) := by rw [ih]
          _ = (g ≫ kernel.ι (f ^ n)) ≫ (f ^ m) := by rw [← Category.assoc]
          _ = (kernel.ι (f ^ n) ≫ f) ≫ (f ^ m) := by rw [hg]
          _ = kernel.ι (f ^ n) ≫ (f ≫ (f ^ m)) := by rw [Category.assoc]
          _ = kernel.ι (f ^ n) ≫ ((f ^ m) * f) := by rw [End.mul_def]
          _ = kernel.ι (f ^ n) ≫ (f ^ (m + 1)) := by rw [pow_succ]
    -- At m = n: g^n ≫ kernel.ι (f^n) = kernel.ι (f^n) ≫ f^n = 0
    have hgn : (g ^ n) ≫ kernel.ι (f ^ n) = 0 := by
      rw [hgpow n, kernel.condition]
    -- Since kernel.ι is mono, g^n = 0
    have hgn_zero : (g ^ n) = 0 := by
      rw [← cancel_mono (kernel.ι (f ^ n)), hgn, zero_comp]
    -- Step 8: Apply isZero_of_epi_pow_eq_zero
    have hKzero : IsZero (kernel (f ^ n)) :=
      @isZero_of_epi_pow_eq_zero C _ _ _ g hg_epi n hn_pos hgn_zero
    -- Step 9: Conclude
    rw [le_antisymm_iff]
    constructor
    · calc kernelSubobject f ≤ kernelSubobject (f ^ n) := hker_le
        _ = Subobject.mk (kernel.ι (f ^ n)) := rfl
        _ = ⊥ := mk_eq_bot_iff_zero.mpr (hKzero.eq_zero_of_src _)
    · exact bot_le

/-- Categorical Orzech: An epi endomorphism on a Noetherian object is mono. -/
theorem mono_of_epi_endomorphism_noetherianObject : Mono f := by
  have h : kernelSubobject f = ⊥ := kernelSubobject_eq_bot_of_epi_noetherian f
  -- kernelSubobject f = ⊥ implies kernel.ι f = 0
  have hι : kernel.ι f = 0 := by
    have harrow : (kernelSubobject f).arrow = 0 := by rw [h, Subobject.bot_arrow]
    rw [← kernelSubobject_arrow f] at harrow
    -- (kernelSubobjectIso f).hom ≫ kernel.ι f = 0
    -- Since (kernelSubobjectIso f).hom is an iso, it's epi, so kernel.ι f = 0
    exact zero_of_epi_comp (kernelSubobjectIso f).hom harrow
  exact Abelian.mono_of_kernel_ι_eq_zero f hι

/-- Corollary: An epi endomorphism on a Noetherian object is an isomorphism. -/
theorem isIso_of_epi_endomorphism_noetherianObject : IsIso f := by
  have : Mono f := mono_of_epi_endomorphism_noetherianObject f
  exact isIso_of_mono_of_epi f

end CategoricalOrzech

end CategoryTheory
