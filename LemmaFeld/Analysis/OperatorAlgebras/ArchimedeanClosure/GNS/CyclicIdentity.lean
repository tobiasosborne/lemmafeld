/-
Copyright (c) 2026 AF-Tests Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AF-Tests Contributors
-/
import LemmaFeld.Analysis.OperatorAlgebras.ArchimedeanClosure.GNS.Star

/-! # Cyclic Vector Identity for GNS

This file proves the key cyclic vector identity: φ(a) = Re⟨Ω, π(a)Ω⟩.

## Main results

* `gnsRep_cyclicVector` - π(a)(Ω) = coe'([a]) in the real Hilbert space
* `gnsRep_inner_cyclicVector` - ⟨Ω, π(a)Ω⟩_ℝ = φ(a)

## Mathematical Background

The GNS construction produces:
- Cyclic vector Ω = [1] (the image of 1 in the quotient, embedded in completion)
- Representation π(a)[b] = [ab]

The cyclic vector identity:
  φ(a) = ⟨Ω, π(a)Ω⟩ = ⟨[1], [a*1]⟩ = ⟨[1], [a]⟩ = φ(star 1 * a) = φ(a)
-/

namespace FreeStarAlgebra

namespace MPositiveState

variable {n : ℕ} [IsArchimedean n] (φ : MPositiveState n)

/-! ### Cyclic Vector Identity in Real Hilbert Space -/

/-- The GNS representation maps the cyclic vector to coe'([a]).

This is π(a)(Ω) = coe'([a*1]) = coe'([a]). -/
theorem gnsRep_cyclicVector (a : FreeStarAlgebra n) :
    φ.gnsRep a φ.gnsCyclicVector =
    @UniformSpace.Completion.coe' φ.gnsQuotient φ.gnsQuotientNormedAddCommGroup.toUniformSpace
      (Submodule.Quotient.mk a) := by
  letI : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  -- gnsCyclicVector = coe'([1])
  unfold gnsCyclicVector
  -- Use gnsRep_coe: gnsRep a (coe' x) = coe' (gnsBoundedPreRep a x)
  rw [gnsRep_coe]
  -- gnsBoundedPreRep a [1] = gnsPreRep a [1] = [a*1] = [a]
  congr 1
  simp only [gnsBoundedPreRep_eq_gnsPreRep, gnsPreRep_mk, mul_one]

/-- The GNS inner product identity: ⟨Ω, π(a)Ω⟩_ℝ = φ(a).

This is the key identity relating the state to the GNS representation. -/
theorem gnsRep_inner_cyclicVector (a : FreeStarAlgebra n) :
    @inner ℝ φ.gnsHilbertSpaceReal _ φ.gnsCyclicVector (φ.gnsRep a φ.gnsCyclicVector) = φ a := by
  letI seminorm : SeminormedAddCommGroup φ.gnsQuotient :=
    φ.gnsQuotientNormedAddCommGroup.toSeminormedAddCommGroup
  letI ips : InnerProductSpace ℝ φ.gnsQuotient :=
    @InnerProductSpace.ofCore ℝ _ _ _ _ φ.gnsInnerProductCore.toCore
  -- Use the explicit formula for π(a)Ω
  rw [gnsRep_cyclicVector]
  -- Both sides are embedded quotient elements
  unfold gnsCyclicVector
  -- Inner product of coe' elements equals inner product of quotient elements
  rw [@UniformSpace.Completion.inner_coe ℝ φ.gnsQuotient _ seminorm ips]
  -- The quotient inner product is gnsInner
  rw [inner_eq_gnsInner]
  -- gnsInner [1] [a] = φ(star a * 1) by gnsInner_mk
  -- = φ(star 1 * a) by sesqForm_symm
  -- = φ(1 * a) = φ(a) by star_one and one_mul
  rw [gnsInner_mk, sesqForm_symm, star_one, one_mul]

/-! ### Cyclic Vector Identity in Complex Hilbert Space -/

open ArchimedeanClosure

/-- The complexified representation on embedded vectors acts componentwise.

π_ℂ(a)(x, 0) = (π(a)x, π(a)0) = (π(a)x, 0) = embed(π(a)x). -/
theorem gnsRepComplex_embed (a : FreeStarAlgebra n) (x : φ.gnsHilbertSpaceReal) :
    φ.gnsRepComplex a (Complexification.embed x) =
    Complexification.embed (φ.gnsRep a x) := by
  ext
  · simp only [Complexification.embed_fst]
    rfl
  · simp only [Complexification.embed_snd]
    change φ.gnsRep a 0 = 0
    exact map_zero (φ.gnsRep a)

/-- The complex cyclic vector identity: Re⟨Ω_ℂ, π_ℂ(a)Ω_ℂ⟩ = φ(a).

This extends the real identity to the complexified space. -/
theorem gnsRepComplex_inner_cyclicVectorComplex (a : FreeStarAlgebra n) :
    (@inner ℂ _ Complexification.instInnerComplex
      φ.gnsCyclicVectorComplex
      (φ.gnsRepComplex a φ.gnsCyclicVectorComplex)).re = φ a := by
  -- Expand gnsCyclicVectorComplex = embed gnsCyclicVector
  unfold gnsCyclicVectorComplex
  -- Use gnsRepComplex_embed
  rw [gnsRepComplex_embed]
  -- Now have Re⟨embed Ω, embed (π(a)Ω)⟩
  simp only [Complexification.inner_re, Complexification.embed_fst, Complexification.embed_snd,
             inner_zero_right, add_zero]
  -- Reduces to the real identity
  exact gnsRep_inner_cyclicVector φ a

end MPositiveState

end FreeStarAlgebra
