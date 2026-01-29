/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.CategoryTheory.Subobject.NoetherianObject
import Mathlib.RingTheory.Nilpotent.Defs
import LemmaFeld.CategoryTheory.TensorCategories.Chapter1.FiniteLength

/-!
# Fitting's Lemma

Fitting's Lemma for abelian categories: for an indecomposable object X of finite
length, any endomorphism f : X → X is either nilpotent or an isomorphism.

§1.5 of Etingof et al. "Tensor Categories" (AMS 2015)
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

/-! ## Chain Stabilization Lemmas

These lemmas establish the monotonicity of kernel and image chains for powers
of an endomorphism. Together with the Noetherian/Artinian properties of finite
length objects, they guarantee chain stabilization.
-/

section ChainStabilization

variable {C : Type*} [Category C] [Abelian C]
variable {X : C} (f : End X)

/-- Powers of an endomorphism can be composed in either order. -/
lemma pow_comp_comm (m k : ℕ) : (f ^ m) ≫ (f ^ k) = (f ^ k) ≫ (f ^ m) := by
  rw [← End.mul_def, ← End.mul_def, pow_mul_comm]

/-- f^(m+k) = f^m ≫ f^k (useful form for kernel chain proofs). -/
lemma pow_add_eq_comp (m k : ℕ) : f ^ (m + k) = (f ^ m) ≫ (f ^ k) := by
  rw [pow_add, End.mul_def, pow_comp_comm]

/-- Alternative form: f^(m+k) = f^k ≫ f^m (useful for image chains). -/
lemma pow_add_eq_comp' (m k : ℕ) : f ^ (m + k) = (f ^ k) ≫ (f ^ m) := by
  rw [pow_add, End.mul_def]

/-- The kernel chain Ker(f) ≤ Ker(f²) ≤ ... is monotone (ascending). -/
lemma kernelSubobject_le_of_le {m n : ℕ} (h : m ≤ n) :
    kernelSubobject (f ^ m) ≤ kernelSubobject (f ^ n) := by
  apply Subobject.mk_le_mk_of_comm (kernel.lift (f ^ n) (kernel.ι (f ^ m)) ?_)
  · exact kernel.lift_ι _ _ _
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [pow_add_eq_comp, ← Category.assoc, kernel.condition, zero_comp]

/-- The kernel chain is monotone. -/
lemma kernelSubobject_mono : Monotone (fun n => kernelSubobject (f ^ n)) :=
  fun _ _ h => kernelSubobject_le_of_le f h

/-- Im(f^n) ≤ Im(f^m) when m ≤ n. -/
lemma imageSubobject_le_of_ge {m n : ℕ} (h : m ≤ n) :
    imageSubobject (f ^ n) ≤ imageSubobject (f ^ m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [pow_add_eq_comp']
  exact imageSubobject_comp_le (f ^ k) (f ^ m)

/-- The image chain is antitone. -/
lemma imageSubobject_antitone : Antitone (fun n => imageSubobject (f ^ n)) :=
  fun _ _ h => imageSubobject_le_of_ge f h

/-- The kernel chain of f stabilizes: there exists n such that Ker(f^m) = Ker(f^n) for all m ≥ n. -/
lemma kernelSubobject_stabilizes [IsNoetherianObject X] :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → kernelSubobject (f ^ n) = kernelSubobject (f ^ m) := by
  have hf : Monotone (fun n => kernelSubobject (f ^ n)) := kernelSubobject_mono f
  exact monotone_chain_condition_of_isNoetherianObject ⟨_, hf⟩

/-- The image chain of f stabilizes: there exists n such that Im(f^m) = Im(f^n) for all m ≥ n. -/
lemma imageSubobject_stabilizes [IsArtinianObject X] :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → imageSubobject (f ^ n) = imageSubobject (f ^ m) := by
  have hf : Antitone (fun n => imageSubobject (f ^ n)) := imageSubobject_antitone f
  -- Antitone in α is monotone in αᵒᵈ
  have hf' : Monotone (fun n => OrderDual.toDual (imageSubobject (f ^ n))) := hf
  obtain ⟨n, hn⟩ := antitone_chain_condition_of_isArtinianObject ⟨_, hf'⟩
  refine ⟨n, fun m hm => ?_⟩
  have heq := hn m hm
  simp only [OrderHom.coe_mk, OrderDual.toDual_inj] at heq
  exact heq

/-- At chain stabilization, the image chain satisfies Im(f^(n+k)) = Im(f^n). -/
lemma imageSubobject_stable [IsArtinianObject X] {n : ℕ}
    (hn : ∀ m : ℕ, n ≤ m → imageSubobject (f ^ n) = imageSubobject (f ^ m)) (k : ℕ) :
    imageSubobject (f ^ (n + k)) = imageSubobject (f ^ n) :=
  (hn (n + k) (Nat.le_add_right n k)).symm

/-- At chain stabilization, the kernel chain satisfies Ker(f^(n+k)) = Ker(f^n). -/
lemma kernelSubobject_stable [IsNoetherianObject X] {n : ℕ}
    (hn : ∀ m : ℕ, n ≤ m → kernelSubobject (f ^ n) = kernelSubobject (f ^ m)) (k : ℕ) :
    kernelSubobject (f ^ (n + k)) = kernelSubobject (f ^ n) :=
  (hn (n + k) (Nat.le_add_right n k)).symm

end ChainStabilization

/-! ## Key Lemmas for Fitting Decomposition

At the stabilization point n, we have the key property:
- Ker(f^n) ∩ Im(f^n) = 0
- Ker(f^n) + Im(f^n) = X

These imply X ≅ Ker(f^n) ⊕ Im(f^n).
-/

section FittingDecomposition

variable {C : Type*} [Category C] [Abelian C]
variable {X : C} (f : End X)

open scoped ZeroObject in
/-- If a subobject's arrow is zero, the subobject equals ⊥. -/
lemma subobject_eq_bot_of_arrow_eq_zero (A : Subobject X) (h : A.arrow = 0) : A = ⊥ := by
  have hiso : Subobject.underlying.obj A ≅ (0 : C) := isoZeroOfMonoEqZero h
  apply Subobject.eq_of_comm (hiso ≪≫ Subobject.botCoeIsoZero.symm)
  simp only [Iso.trans_hom, Subobject.bot_arrow, comp_zero, h]

/-- The intersection of kernel and image, composed with f^n, is zero. -/
lemma inf_arrow_comp_pow_eq_zero {n : ℕ} :
    (kernelSubobject (f ^ n) ⊓ imageSubobject (f ^ n)).arrow ≫ f ^ n = 0 := by
  rw [← Subobject.ofLE_arrow (inf_le_left (a := kernelSubobject (f ^ n)))]
  rw [Category.assoc, kernelSubobject_arrow_comp, comp_zero]

/-! ### Helper: imageSubobject of composition with epi -/

/-- When h is epi, imageSubobject(h ≫ f) = imageSubobject(f). -/
lemma imageSubobject_comp_eq_of_epi {Y Z : C} (h : X ⟶ Y) [Epi h] (g : Y ⟶ Z) :
    imageSubobject (h ≫ g) = imageSubobject g := by
  have hle : imageSubobject (h ≫ g) ≤ imageSubobject g := imageSubobject_comp_le h g
  have hEpi : Epi ((imageSubobject (h ≫ g)).ofLE (imageSubobject g) hle) :=
    imageSubobject_comp_le_epi_of_epi h g
  have hIso : IsIso ((imageSubobject (h ≫ g)).ofLE (imageSubobject g) hle) :=
    isIso_of_mono_of_epi _
  exact le_antisymm hle (Subobject.le_of_comm
    (inv ((imageSubobject (h ≫ g)).ofLE _ hle)) (by simp [Subobject.ofLE_arrow]))

/-- imageSubobject(I.arrow ≫ f^n) = imageSubobject(f^(2n)) where I = imageSubobject(f^n). -/
lemma imageSubobject_arrow_comp_pow_eq {n : ℕ} :
    imageSubobject ((imageSubobject (f^n)).arrow ≫ (f^n)) = imageSubobject (f^(2*n)) := by
  have h2n : f^(2*n) = (f^n) ≫ (f^n) := by rw [two_mul, pow_add, End.mul_def]
  let I := imageSubobject (f^n)
  have hfac : factorThruImageSubobject (f^n) ≫ I.arrow = f^n := imageSubobject_arrow_comp (f^n)
  have key : (f^n) ≫ (f^n) = factorThruImageSubobject (f^n) ≫ (I.arrow ≫ f^n) := by
    conv_lhs => arg 1; rw [← hfac]
    rw [Category.assoc]
  rw [h2n, key]
  exact (imageSubobject_comp_eq_of_epi (factorThruImageSubobject (f^n)) (I.arrow ≫ f^n)).symm

/-- At image stabilization, imageSubobject(I.arrow ≫ f^n) = I. -/
lemma imageSubobject_arrow_comp_eq_self {n : ℕ}
    (him : ∀ m : ℕ, n ≤ m → imageSubobject (f ^ n) = imageSubobject (f ^ m)) :
    imageSubobject ((imageSubobject (f^n)).arrow ≫ (f^n)) = imageSubobject (f^n) := by
  have him2n : imageSubobject (f^n) = imageSubobject (f^(2*n)) :=
    him (2*n) (Nat.le_mul_of_pos_left n (by omega))
  rw [imageSubobject_arrow_comp_pow_eq f, him2n.symm]

/-- g factors through imageSubobject g. -/
lemma factors_imageSubobject {Y : C} (g : X ⟶ Y) : (imageSubobject g).Factors g := by
  have h := imageSubobject_factors_comp_self g (𝟙 X)
  simp only [Category.id_comp] at h
  exact h

/-! ### Categorical Orzech (local version)

For the Fitting decomposition, we need: an epi endomorphism on a Noetherian object is mono.
This is proved in CategoricalOrzech.lean, but we include a local version here to avoid
circular imports. -/

/-- An epi nilpotent endomorphism implies the object is zero. -/
private theorem isZero_of_epi_pow_eq_zero' {Y : C} (g : End Y) [hg : Epi g]
    (n : ℕ) (hn : 0 < n) (heq : g ^ n = 0) : IsZero Y := by
  induction n with
  | zero => exact (Nat.not_lt_zero 0 hn).elim
  | succ m ih =>
    cases m with
    | zero =>
      rw [pow_one] at heq
      exact IsZero.of_epi_eq_zero g heq
    | succ k =>
      have hpow : g^(k + 2) = g^(k + 1) * g := pow_succ g (k + 1)
      rw [hpow, End.mul_def] at heq
      have heq' : g^(k + 1) = 0 := by
        have h0 : g ≫ (0 : Y ⟶ Y) = 0 := comp_zero
        rw [← h0] at heq
        exact (cancel_epi g).mp heq
      exact ih (Nat.succ_pos k) heq'

/-- An epi endomorphism on a Noetherian object is mono. (Local copy for Fitting decomposition) -/
private theorem mono_of_epi_endomorphism_noetherianObject' {Y : C}
    (g : End Y) [hg : Epi g] [IsNoetherianObject Y] : Mono g := by
  -- Get stabilization of kernel chain
  obtain ⟨n, hn⟩ := kernelSubobject_stabilizes g
  by_cases hn0 : n = 0
  · -- Stabilizes at 0: kernelSubobject g = kernelSubobject (g^0) = kernelSubobject (𝟙 Y) = ⊥
    subst hn0
    have h01 : kernelSubobject (g ^ 0) = kernelSubobject (g ^ 1) := hn 1 (Nat.zero_le 1)
    have hone : (g ^ (0 : ℕ) : End Y) = 𝟙 Y := by rw [pow_zero, End.one_def]
    open scoped ZeroObject in
    have hker0 : kernelSubobject (g ^ (0 : ℕ)) = ⊥ := by
      rw [hone, kernelSubobject]
      have : kernel.ι (𝟙 Y) = 0 := by
        -- kernel of identity is zero (since 𝟙 is mono, kernel is initial)
        have hk : kernel (𝟙 Y) ≅ (0 : C) := kernel.ofMono (𝟙 Y)
        have hzero : IsZero (kernel (𝟙 Y)) := hk.isZero_iff.mpr (isZero_zero C)
        exact hzero.eq_zero_of_src _
      exact Subobject.mk_eq_bot_iff_zero.mpr this
    rw [pow_one] at h01
    have hker_g : kernelSubobject g = ⊥ := by rw [← h01, hker0]
    have hι : kernel.ι g = 0 := by
      have harrow : (kernelSubobject g).arrow = 0 := by rw [hker_g, Subobject.bot_arrow]
      rw [← kernelSubobject_arrow g] at harrow
      exact zero_of_epi_comp (kernelSubobjectIso g).hom harrow
    exact Abelian.mono_of_kernel_ι_eq_zero g hι
  · -- n ≥ 1 case: use Djoković's argument
    push_neg at hn0
    have hn_pos : 0 < n := Nat.pos_of_ne_zero hn0
    have hker_le : kernelSubobject g ≤ kernelSubobject (g ^ n) := by
      have h1 : kernelSubobject g = kernelSubobject (g ^ 1) := by rw [pow_one]
      rw [h1]
      exact kernelSubobject_le_of_le g (Nat.one_le_of_lt hn_pos)
    -- Saturation: ker(g^n) = ker(g^(n+1))
    have hsat : kernelSubobject (g ^ n) = kernelSubobject (g ^ (n + 1)) := hn (n + 1) (Nat.le_succ n)
    -- Construct iso from saturation
    let φ := Subobject.isoOfMkEqMk (kernel.ι (g ^ n)) (kernel.ι (g ^ (n + 1))) hsat
    have hφ : φ.hom ≫ kernel.ι (g ^ (n + 1)) = kernel.ι (g ^ n) := Subobject.ofMkLEMk_comp hsat.le
    -- Construct k : kernel(g^(n+1)) → kernel(g^n)
    have hpow : (g ^ (n + 1) : End Y) = g ≫ g ^ n := by rw [pow_succ, End.mul_def]
    let k : kernel (g ^ (n + 1)) ⟶ kernel (g ^ n) :=
      kernel.lift (g ^ n) (kernel.ι (g ^ (n + 1)) ≫ g) (by
        rw [Category.assoc, ← hpow, kernel.condition])
    have hk : k ≫ kernel.ι (g ^ n) = kernel.ι (g ^ (n + 1)) ≫ g := kernel.lift_ι _ _ _
    -- k is epi (pullback stability)
    have hk_epi : Epi k := by
      have hp : IsPullback k (kernel.ι (g ^ (n + 1))) (kernel.ι (g ^ n)) g := by
        refine IsPullback.of_isLimit (c := PullbackCone.mk k (kernel.ι (g ^ (n + 1))) hk) ?_
        refine PullbackCone.isLimitAux' _ ?_
        intro s
        have hcond : s.snd ≫ g ^ (n + 1) = 0 := by
          rw [hpow, ← Category.assoc, ← s.condition, Category.assoc, kernel.condition, comp_zero]
        let ℓ := kernel.lift (g ^ (n + 1)) s.snd hcond
        refine ⟨ℓ, ?_, kernel.lift_ι _ _ _, ?_⟩
        · apply equalizer.hom_ext
          rw [PullbackCone.mk_fst, Category.assoc, hk, ← Category.assoc, kernel.lift_ι, s.condition]
        · intro m' _ hm2; apply equalizer.hom_ext; rw [kernel.lift_ι]; exact hm2
      exact Abelian.epi_fst_of_isLimit _ g hp.isLimit
    -- Define endomorphism h on kernel(g^n)
    let h : End (kernel (g ^ n)) := φ.hom ≫ k
    have hh : h ≫ kernel.ι (g ^ n) = kernel.ι (g ^ n) ≫ g := by
      calc h ≫ kernel.ι (g ^ n)
          = (φ.hom ≫ k) ≫ kernel.ι (g ^ n) := rfl
        _ = φ.hom ≫ (k ≫ kernel.ι (g ^ n)) := by rw [Category.assoc]
        _ = φ.hom ≫ (kernel.ι (g ^ (n + 1)) ≫ g) := by rw [hk]
        _ = (φ.hom ≫ kernel.ι (g ^ (n + 1))) ≫ g := by rw [← Category.assoc]
        _ = kernel.ι (g ^ n) ≫ g := by rw [hφ]
    have h_epi : Epi h := epi_comp φ.hom k
    -- h^n = 0 (nilpotent)
    have hhpow : ∀ m : ℕ, (h ^ m) ≫ kernel.ι (g ^ n) = kernel.ι (g ^ n) ≫ (g ^ m) := by
      intro m
      induction m with
      | zero => simp only [pow_zero, End.one_def, Category.id_comp, Category.comp_id]
      | succ m ihm =>
        calc (h ^ (m + 1)) ≫ kernel.ι (g ^ n)
            = (h ^ m * h) ≫ kernel.ι (g ^ n) := by rw [pow_succ]
          _ = (h ≫ (h ^ m)) ≫ kernel.ι (g ^ n) := by rw [End.mul_def]
          _ = h ≫ ((h ^ m) ≫ kernel.ι (g ^ n)) := by rw [Category.assoc]
          _ = h ≫ (kernel.ι (g ^ n) ≫ (g ^ m)) := by rw [ihm]
          _ = (h ≫ kernel.ι (g ^ n)) ≫ (g ^ m) := by rw [← Category.assoc]
          _ = (kernel.ι (g ^ n) ≫ g) ≫ (g ^ m) := by rw [hh]
          _ = kernel.ι (g ^ n) ≫ (g ≫ (g ^ m)) := by rw [Category.assoc]
          _ = kernel.ι (g ^ n) ≫ ((g ^ m) * g) := by rw [End.mul_def]
          _ = kernel.ι (g ^ n) ≫ (g ^ (m + 1)) := by rw [pow_succ]
    have hhn : (h ^ n) ≫ kernel.ι (g ^ n) = 0 := by rw [hhpow n, kernel.condition]
    have hhn_zero : (h ^ n) = 0 := by rw [← cancel_mono (kernel.ι (g ^ n)), hhn, zero_comp]
    -- kernel(g^n) is zero
    have hKzero : IsZero (kernel (g ^ n)) :=
      @isZero_of_epi_pow_eq_zero' C _ _ _ h h_epi n hn_pos hhn_zero
    -- Conclude
    have hker_n_bot : kernelSubobject (g ^ n) = ⊥ := Subobject.mk_eq_bot_iff_zero.mpr
      (hKzero.eq_zero_of_src _)
    have hker_g_bot : kernelSubobject g = ⊥ := le_antisymm (hker_le.trans (le_of_eq hker_n_bot)) bot_le
    have hι : kernel.ι g = 0 := by
      have harrow : (kernelSubobject g).arrow = 0 := by rw [hker_g_bot, Subobject.bot_arrow]
      rw [← kernelSubobject_arrow g] at harrow
      exact zero_of_epi_comp (kernelSubobjectIso g).hom harrow
    exact Abelian.mono_of_kernel_ι_eq_zero g hι

/-- At stabilization, Ker(f^n) ∩ Im(f^n) = 0. Key: f^n|_{Im(f^n)} is iso at stabilization.
    Note: Requires IsNoetherianObject X to deduce that underlying(Im(f^n)) is Noetherian. -/
lemma kernelSubobject_inf_imageSubobject_eq_bot [IsNoetherianObject X] {n : ℕ}
    (hker : ∀ m : ℕ, n ≤ m → kernelSubobject (f ^ n) = kernelSubobject (f ^ m))
    (him : ∀ m : ℕ, n ≤ m → imageSubobject (f ^ n) = imageSubobject (f ^ m)) :
    kernelSubobject (f ^ n) ⊓ imageSubobject (f ^ n) = ⊥ := by
  apply subobject_eq_bot_of_arrow_eq_zero
  -- Let K = ker(f^n), I = im(f^n)
  let K := kernelSubobject (f ^ n)
  let I := imageSubobject (f ^ n)
  -- Key fact: imageSubobject(I.arrow ≫ f^n) = I by image stabilization
  have himArrow : imageSubobject (I.arrow ≫ f^n) = I := imageSubobject_arrow_comp_eq_self f him
  -- So I.arrow ≫ f^n factors through I (since its image = I)
  -- Proof: imageSubobject(I.arrow ≫ f^n) = I by himArrow, so g factors through I
  -- TODO: API challenge with Subobject.Factors quotient representation
  have hfac : I.Factors (I.arrow ≫ f^n) := by
    have h1 := imageSubobject_factors_comp_self (f^n) I.arrow
    -- h1 : (imageSubobject (f^n)).Factors (I.arrow ≫ f^n)
    -- I = imageSubobject (f^n), so this is exactly what we need
    convert h1
  -- Define restriction h : underlying(I) → underlying(I)
  let h : End (Subobject.underlying.obj I) := I.factorThru (I.arrow ≫ f^n) hfac
  have hh : h ≫ I.arrow = I.arrow ≫ f^n := Subobject.factorThru_arrow _ _ _
  -- h is epi: since imageSubobject(I.arrow ≫ f^n) = I, the factorization is surjective
  -- Proof structure: h = factorThruImageSubobject ≫ isoOfEq.hom, both are epi
  have h_epi : Epi h := by
    -- h = factorThruImageSubobject (I.arrow ≫ f^n) ≫ isoOfEq.hom
    -- Since himArrow : imageSubobject(I.arrow ≫ f^n) = I, we have an iso
    let φ := Subobject.isoOfEq _ _ himArrow
    -- Show h = factorThruImageSubobject ≫ φ.hom by mono of I.arrow
    have heq : h = factorThruImageSubobject (I.arrow ≫ f^n) ≫ φ.hom := by
      rw [← cancel_mono I.arrow, Category.assoc]
      -- RHS: factorThruImageSubobject _ ≫ φ.hom ≫ I.arrow
      --    = factorThruImageSubobject _ ≫ (imageSubobject _).arrow  (since φ.hom = ofLE)
      --    = I.arrow ≫ f^n  (by imageSubobject_arrow_comp)
      have hφ : φ.hom ≫ I.arrow = (imageSubobject (I.arrow ≫ f^n)).arrow :=
        Subobject.ofLE_arrow himArrow.le
      rw [hφ, imageSubobject_arrow_comp]
      -- LHS: h ≫ I.arrow = I.arrow ≫ f^n by hh
      exact hh
    rw [heq]
    exact epi_comp _ _
  -- underlying(I) is Noetherian (subobject of Noetherian X)
  have hNoeth : IsNoetherianObject (Subobject.underlying.obj I) :=
    isNoetherianObject_of_mono I.arrow
  -- By categorical Orzech, h is mono (hence iso)
  have h_iso : IsIso h := by
    have h_mono : Mono h := @mono_of_epi_endomorphism_noetherianObject'
      C _ _ _ h h_epi hNoeth
    exact isIso_of_mono_of_epi h
  -- Now conclude: (K ⊓ I).arrow = 0
  -- We have (K ⊓ I) ≤ I, so (K ⊓ I).arrow = ofLE ≫ I.arrow
  have hKI_le_I : K ⊓ I ≤ I := inf_le_right
  -- ofLE ≫ I.arrow ≫ f^n = (K ⊓ I).arrow ≫ f^n = 0
  have hzero : (K ⊓ I).arrow ≫ f^n = 0 := inf_arrow_comp_pow_eq_zero f
  -- (K ⊓ I).arrow = ofLE ≫ I.arrow
  have harrow : (K ⊓ I).arrow = (K ⊓ I).ofLE I hKI_le_I ≫ I.arrow := (Subobject.ofLE_arrow _).symm
  -- So ofLE ≫ I.arrow ≫ f^n = 0, i.e., ofLE ≫ (h ≫ I.arrow) = 0
  have h1 : (K ⊓ I).ofLE I hKI_le_I ≫ h ≫ I.arrow = 0 := by
    -- Rewrite h ≫ I.arrow to I.arrow ≫ f^n
    rw [hh]
    -- Now: ofLE ≫ I.arrow ≫ f^n = 0
    rw [← Category.assoc, Subobject.ofLE_arrow]
    -- Now: (K ⊓ I).arrow ≫ f^n = 0
    exact hzero
  -- Since I.arrow is mono, ofLE ≫ h = 0
  have h2 : (K ⊓ I).ofLE I hKI_le_I ≫ h = 0 := by
    rw [← cancel_mono I.arrow, Category.assoc, h1, zero_comp]
  -- Since h is iso, ofLE = 0
  have h3 : (K ⊓ I).ofLE I hKI_le_I = 0 := by
    calc (K ⊓ I).ofLE I hKI_le_I
        = ((K ⊓ I).ofLE I hKI_le_I ≫ h) ≫ inv h := by simp
      _ = 0 ≫ inv h := by rw [h2]
      _ = 0 := zero_comp
  -- Finally, (K ⊓ I).arrow = ofLE ≫ I.arrow = 0 ≫ I.arrow = 0
  rw [harrow, h3, zero_comp]

/-- At stabilization, Ker(f^n) + Im(f^n) = X. For any x, f^n(x) ∈ Im(f^(2n)) = Im(f^n).

**Proof approach**: We need to show that the coprojection K ⊕ I → X is epi.
1. From kernelSubobject_inf_imageSubobject_eq_bot, we have h : End(underlying(I)) is an iso.
2. The splitting map s : X → underlying(I) is factorThruImageSubobject(f^n) ≫ inv(h).
3. Define projection π : X → X by π = s ≫ I.arrow (maps to image component).
4. Then (𝟙 X - π) maps to kernel component since f^n ≫ (𝟙 X - π) = 0.
5. The map [kernel_lift, s] : X → K ⊕ I is a section of [K.arrow, I.arrow].
6. This shows biprod.desc K.arrow I.arrow is epi, hence K ⊔ I = ⊤.
-/
lemma kernelSubobject_sup_imageSubobject_eq_top [IsNoetherianObject X] {n : ℕ}
    (hker : ∀ m : ℕ, n ≤ m → kernelSubobject (f ^ n) = kernelSubobject (f ^ m))
    (him : ∀ m : ℕ, n ≤ m → imageSubobject (f ^ n) = imageSubobject (f ^ m)) :
    kernelSubobject (f ^ n) ⊔ imageSubobject (f ^ n) = ⊤ := by
  -- Setup: Let K = ker(f^n), I = im(f^n)
  let K := kernelSubobject (f ^ n)
  let I := imageSubobject (f ^ n)
  -- Construct h : End(underlying(I)) with h ≫ I.arrow = I.arrow ≫ f^n
  have himArrow : imageSubobject (I.arrow ≫ f ^ n) = I := imageSubobject_arrow_comp_eq_self f him
  have hfac : I.Factors (I.arrow ≫ f ^ n) := by
    have h1 := imageSubobject_factors_comp_self (f ^ n) I.arrow
    convert h1
  let h : End (Subobject.underlying.obj I) := I.factorThru (I.arrow ≫ f ^ n) hfac
  have hh : h ≫ I.arrow = I.arrow ≫ f ^ n := Subobject.factorThru_arrow _ _ _
  -- h is epi (factorization through image with same image)
  have h_epi : Epi h := by
    let φ := Subobject.isoOfEq _ _ himArrow
    have heq : h = factorThruImageSubobject (I.arrow ≫ f ^ n) ≫ φ.hom := by
      rw [← cancel_mono I.arrow, Category.assoc]
      have hφ : φ.hom ≫ I.arrow = (imageSubobject (I.arrow ≫ f ^ n)).arrow :=
        Subobject.ofLE_arrow himArrow.le
      rw [hφ, imageSubobject_arrow_comp, hh]
    rw [heq]
    exact epi_comp _ _
  -- underlying(I) is Noetherian (subobject of Noetherian X)
  have hNoeth : IsNoetherianObject (Subobject.underlying.obj I) :=
    isNoetherianObject_of_mono I.arrow
  -- By categorical Orzech, h is iso
  have h_mono : Mono h := @mono_of_epi_endomorphism_noetherianObject' C _ _ _ h h_epi hNoeth
  have h_iso : IsIso h := isIso_of_mono_of_epi h
  -- Construct section s_I : X → underlying(I)
  let s_I := factorThruImageSubobject (f ^ n) ≫ inv h
  -- Key: s_I is a section of I.arrow (I.arrow ≫ s_I = id)
  have s_section : I.arrow ≫ s_I = 𝟙 _ := by
    -- I.arrow ≫ factorThru(f^n) = h (by mono property)
    have harrow_factor : I.arrow ≫ factorThruImageSubobject (f ^ n) = h := by
      rw [← cancel_mono I.arrow, Category.assoc, imageSubobject_arrow_comp, hh]
    calc I.arrow ≫ s_I
        = I.arrow ≫ factorThruImageSubobject (f ^ n) ≫ inv h := rfl
      _ = (I.arrow ≫ factorThruImageSubobject (f ^ n)) ≫ inv h := by rw [← Category.assoc]
      _ = h ≫ inv h := by rw [harrow_factor]
      _ = 𝟙 _ := @IsIso.hom_inv_id _ _ _ _ h h_iso
  -- Construct projection p_I : X → X
  let p_I := s_I ≫ I.arrow
  -- Key calculation: p_I ≫ f^n = f^n
  have p_comp_fn : p_I ≫ f ^ n = f ^ n := by
    have key : inv h ≫ I.arrow ≫ f ^ n = I.arrow := by
      calc inv h ≫ I.arrow ≫ f ^ n
          = inv h ≫ (h ≫ I.arrow) := by rw [← hh]
        _ = (inv h ≫ h) ≫ I.arrow := by rw [Category.assoc]
        _ = 𝟙 _ ≫ I.arrow := by rw [@IsIso.inv_hom_id _ _ _ _ h h_iso]
        _ = I.arrow := Category.id_comp _
    show (s_I ≫ I.arrow) ≫ f ^ n = f ^ n
    rw [Category.assoc]
    show s_I ≫ I.arrow ≫ f ^ n = f ^ n
    show (factorThruImageSubobject (f ^ n) ≫ inv h) ≫ I.arrow ≫ f ^ n = f ^ n
    rw [Category.assoc]
    show factorThruImageSubobject (f ^ n) ≫ inv h ≫ I.arrow ≫ f ^ n = f ^ n
    rw [key]
    exact imageSubobject_arrow_comp _
  -- (𝟙 X - p_I) ≫ f^n = 0, so it factors through K
  have one_minus_p_comp_fn : (𝟙 X - p_I) ≫ f ^ n = 0 := by
    rw [Preadditive.sub_comp, Category.id_comp, p_comp_fn, sub_self]
  -- Factor (𝟙 X - p_I) through K
  have hfac_K : K.Factors (𝟙 X - p_I) := by
    rw [kernelSubobject_factors_iff]
    exact one_minus_p_comp_fn
  let q_K := K.factorThru (𝟙 X - p_I) hfac_K
  have hqK : q_K ≫ K.arrow = 𝟙 X - p_I := Subobject.factorThru_arrow _ _ _
  -- Show that K.arrow + I.arrow is epi (equivalently, show 𝟙 X factors through K + I)
  -- We have: 𝟙 X = (𝟙 X - p_I) + p_I = q_K ≫ K.arrow + s_I ≫ I.arrow
  have id_decomp : 𝟙 X = q_K ≫ K.arrow + s_I ≫ I.arrow := by
    -- hqK: q_K ≫ K.arrow = 𝟙 X - p_I
    -- So: 𝟙 X = q_K ≫ K.arrow + p_I = q_K ≫ K.arrow + s_I ≫ I.arrow
    calc 𝟙 X = (𝟙 X - p_I) + p_I := by rw [sub_add_cancel]
      _ = q_K ≫ K.arrow + p_I := by rw [← hqK]
      _ = q_K ≫ K.arrow + s_I ≫ I.arrow := rfl
  -- This means K ⊔ I = ⊤ in the subobject lattice
  -- Goal: K ⊔ I = ⊤, i.e., the identity factors through K ⊔ I
  -- The sup K ⊔ I is the image of the coprod map
  -- Since 𝟙 X = q_K ≫ K.arrow + s_I ≫ I.arrow, and both K.arrow, I.arrow factor through K ⊔ I,
  -- we have 𝟙 X factors through K ⊔ I
  have hKle : K ≤ K ⊔ I := le_sup_left
  have hIle : I ≤ K ⊔ I := le_sup_right
  have hK_fac : (K ⊔ I).Factors K.arrow := Subobject.factors_of_le K.arrow hKle (Subobject.factors_self K)
  have hI_fac : (K ⊔ I).Factors I.arrow := Subobject.factors_of_le I.arrow hIle (Subobject.factors_self I)
  -- factorThru gives us the factorizations
  have hK_eq : (K ⊔ I).factorThru K.arrow hK_fac ≫ (K ⊔ I).arrow = K.arrow :=
    Subobject.factorThru_arrow _ _ _
  have hI_eq : (K ⊔ I).factorThru I.arrow hI_fac ≫ (K ⊔ I).arrow = I.arrow :=
    Subobject.factorThru_arrow _ _ _
  -- Construct factorization of 𝟙 X through K ⊔ I
  let factor_id := q_K ≫ (K ⊔ I).factorThru K.arrow hK_fac +
                   s_I ≫ (K ⊔ I).factorThru I.arrow hI_fac
  have hfactor : factor_id ≫ (K ⊔ I).arrow = 𝟙 X := by
    -- factor_id = q_K ≫ factorThru(K.arrow) + s_I ≫ factorThru(I.arrow)
    -- factor_id ≫ (K ⊔ I).arrow = (q_K ≫ factorThru(K.arrow) + s_I ≫ factorThru(I.arrow)) ≫ (K ⊔ I).arrow
    --                          = q_K ≫ factorThru(K.arrow) ≫ (K ⊔ I).arrow + s_I ≫ factorThru(I.arrow) ≫ (K ⊔ I).arrow
    --                          = q_K ≫ K.arrow + s_I ≫ I.arrow  (by hK_eq, hI_eq)
    --                          = 𝟙 X  (by id_decomp)
    calc factor_id ≫ (K ⊔ I).arrow
        = (q_K ≫ (K ⊔ I).factorThru K.arrow hK_fac + s_I ≫ (K ⊔ I).factorThru I.arrow hI_fac) ≫
            (K ⊔ I).arrow := rfl
      _ = q_K ≫ (K ⊔ I).factorThru K.arrow hK_fac ≫ (K ⊔ I).arrow +
          s_I ≫ (K ⊔ I).factorThru I.arrow hI_fac ≫ (K ⊔ I).arrow := by
          rw [Preadditive.add_comp, Category.assoc, Category.assoc]
      _ = q_K ≫ K.arrow + s_I ≫ I.arrow := by rw [hK_eq, hI_eq]
      _ = 𝟙 X := id_decomp.symm
  -- Since factor_id ≫ (K ⊔ I).arrow = 𝟙, (K ⊔ I).arrow is epi
  have arrow_epi : Epi (K ⊔ I).arrow := by
    constructor
    intro Z g h hgh
    calc g = 𝟙 X ≫ g := (Category.id_comp g).symm
      _ = (factor_id ≫ (K ⊔ I).arrow) ≫ g := by rw [hfactor]
      _ = factor_id ≫ (K ⊔ I).arrow ≫ g := by rw [Category.assoc]
      _ = factor_id ≫ (K ⊔ I).arrow ≫ h := by rw [hgh]
      _ = (factor_id ≫ (K ⊔ I).arrow) ≫ h := by rw [← Category.assoc]
      _ = 𝟙 X ≫ h := by rw [hfactor]
      _ = h := Category.id_comp h
  -- In a balanced category (abelian), mono + epi = iso
  have arrow_iso : IsIso (K ⊔ I).arrow := isIso_of_mono_of_epi _
  exact Subobject.eq_top_of_isIso_arrow _

end FittingDecomposition

/-! ## Fitting's Lemma -/

section FittingLemma

variable {C : Type*} [Category C] [Abelian C] [HasFiniteBiproducts C]
variable {X : C}

/-- **Fitting's Lemma**: For indecomposable X of finite length, f ∈ End(X) is nilpotent or unit.

**Proof outline**:
1. Get stabilization n from IsNoetherianObject (finite length → Noetherian).
2. At stabilization: Ker(f^n) ⊓ Im(f^n) = ⊥ and Ker(f^n) ⊔ Im(f^n) = ⊤.
3. This gives X ≅ Ker(f^n) ⊕ Im(f^n) (direct sum decomposition in abelian category).
4. Since X is indecomposable, one summand must be 0:
   - If Im(f^n) = 0: f is nilpotent (f^n = 0).
   - If Ker(f^n) = 0: f^n (hence f) is mono, and f is epi on finite length objects,
     so f is an isomorphism (unit).
-/
theorem fitting_lemma (f : End X) (hX : Indecomposable X) (hfl : IsFiniteLengthObject X) :
    IsNilpotent f ∨ IsUnit f := by
  -- TODO: Complete after kernelSubobject_sup_imageSubobject_eq_top is proved.
  sorry

/-- Local ring property: non-units form a two-sided ideal. Follows from Fitting's Lemma. -/
def EndomorphismRingIsLocal (X : C) : Prop :=
  ∀ f g : X ⟶ X, IsIso (f + g) → IsIso f ∨ IsIso g

end FittingLemma

end LemmaFeld.TensorCategories.Chapter1
