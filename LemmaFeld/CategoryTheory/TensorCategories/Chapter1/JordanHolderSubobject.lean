/-
Copyright (c) 2026 LemmaFeld Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LemmaFeld Contributors
-/
import Mathlib.CategoryTheory.Subobject.Lattice
import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.CategoryTheory.Abelian.Exact
import Mathlib.Order.JordanHolder
import Mathlib.CategoryTheory.Simple

/-!
# Jordan-Hölder Lattice for Subobjects

§1.5 Theorem 1.5.4 (Etingof et al.): Jordan-Hölder theorem for abelian categories.

Mathlib provides `JordanHolderLattice (Submodule R M)` for modules but not for
`Subobject X` in abelian categories. This file builds toward that instance.

## Definitions

- `SubobjectIsMaximal A B`: the covering relation `A ⋖ B` on `Subobject X`
- `SubobjectQuotient h`: the quotient object `B/A` as `cokernel (A.ofLE B h)`
- `SubobjectIso p q`: isomorphism of quotient objects for pairs of subobjects
-/

noncomputable section

namespace LemmaFeld.TensorCategories.Chapter1

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C] {X : C}

/-! ## IsMaximal: Covering relation on subobjects

Following the module case (`JordanHolderModule`), we define `IsMaximal` as the
covering relation `⋖` (Covby). For subobjects of an object in an abelian category,
`A ⋖ B` means `A < B` and there is no `C` with `A < C < B`, which is equivalent
to B/A being simple.
-/

/-- `IsMaximal A B` means `A` is a maximal proper subobject of `B`,
i.e., the covering relation `A ⋖ B`. -/
def SubobjectIsMaximal (A B : Subobject X) : Prop := A ⋖ B

omit [Abelian C] in
theorem subobjectIsMaximal_lt {A B : Subobject X} (h : SubobjectIsMaximal A B) :
    A < B :=
  h.lt

/-! ## Quotient object B/A

For `A ≤ B` as subobjects of `X`, the quotient `B/A` is the cokernel of the
inclusion `A.ofLE B h : underlying A ⟶ underlying B`.
-/

/-- The quotient object `B/A` for subobjects `A ≤ B`, defined as the cokernel
of the inclusion morphism. -/
def SubobjectQuotient {A B : Subobject X} (h : A ≤ B) : C :=
  cokernel (A.ofLE B h)

/-! ## Iso: Isomorphism of quotient pairs

For pairs `(A₁, B₁)` and `(A₂, B₂)` of subobjects, `SubobjectIso` holds when the
quotients `B₁/(A₁ ⊓ B₁) ≅ B₂/(A₂ ⊓ B₂)` are isomorphic as objects.

Using `A ⊓ B` ensures the definition is well-typed for arbitrary pairs (since
`A ⊓ B ≤ B` always holds). When `A ≤ B`, we have `A ⊓ B = A`, so this
reduces to the standard quotient `B/A`.
-/

/-- Two pairs of subobjects are `SubobjectIso` when their quotient objects
are isomorphic. Uses `A ⊓ B` to handle arbitrary pairs. -/
def SubobjectIso (p q : Subobject X × Subobject X) : Prop :=
  Nonempty (cokernel ((p.1 ⊓ p.2).ofLE p.2 inf_le_right) ≅
            cokernel ((q.1 ⊓ q.2).ofLE q.2 inf_le_right))

theorem subobjectIso_symm {p q : Subobject X × Subobject X}
    (h : SubobjectIso p q) : SubobjectIso q p :=
  h.map Iso.symm

theorem subobjectIso_trans {p q r : Subobject X × Subobject X}
    (h₁ : SubobjectIso p q) (h₂ : SubobjectIso q r) : SubobjectIso p r :=
  ⟨h₁.some ≪≫ h₂.some⟩

/-! ## Second Isomorphism Theorem for Subobjects

§1.5: For subobjects A, B of X in an abelian category:
  cokernel(A → A⊔B) ≅ cokernel((A⊓B) → B)

This is the categorical second isomorphism theorem: (A⊔B)/A ≅ B/(A⊓B).

Strategy: construct forward map via cokernel.desc, prove mono+epi → iso
in the balanced (abelian) category.
-/

/-- The forward map for the second isomorphism theorem:
    B/(A⊓B) → (A⊔B)/A, induced by the inclusion B → A⊔B. -/
def secondIsoMap (A B : Subobject X) :
    cokernel ((A ⊓ B).ofLE B inf_le_right) ⟶ cokernel (A.ofLE (A ⊔ B) le_sup_left) :=
  cokernel.desc _ (B.ofLE (A ⊔ B) le_sup_right ≫ cokernel.π (A.ofLE (A ⊔ B) le_sup_left)) (by
    rw [← Category.assoc, Subobject.ofLE_comp_ofLE]
    have : (A ⊓ B).ofLE (A ⊔ B) (inf_le_left.trans le_sup_left) =
      (A ⊓ B).ofLE A inf_le_left ≫ A.ofLE (A ⊔ B) le_sup_left :=
      (Subobject.ofLE_comp_ofLE _ _ _ _ _).symm
    rw [this, Category.assoc, cokernel.condition, comp_zero])

@[simp] lemma cokernel_π_comp_secondIsoMap (A B : Subobject X) :
    cokernel.π ((A ⊓ B).ofLE B inf_le_right) ≫ secondIsoMap A B =
    B.ofLE (A ⊔ B) le_sup_right ≫ cokernel.π (A.ofLE (A ⊔ B) le_sup_left) := by
  simp [secondIsoMap]

instance mono_secondIsoMap (A B : Subobject X) : Mono (secondIsoMap A B) := by
  apply Preadditive.mono_of_cancel_zero
  intro T g hg
  obtain ⟨T', π, hπ, f, hf⟩ := surjective_up_to_refinements_of_epi
    (cokernel.π ((A ⊓ B).ofLE B inf_le_right)) g
  have h2 : f ≫ B.ofLE (A ⊔ B) le_sup_right ≫ cokernel.π (A.ofLE (A ⊔ B) le_sup_left) = 0 := by
    have key : f ≫ (cokernel.π ((A ⊓ B).ofLE B inf_le_right) ≫ secondIsoMap A B) = 0 := by
      rw [← Category.assoc, ← hf, Category.assoc, hg, comp_zero]
    rwa [cokernel_π_comp_secondIsoMap] at key
  have hexact := ShortComplex.exact_cokernel (A.ofLE (A ⊔ B) le_sup_left)
  obtain ⟨T'', π', hπ', h, hh⟩ := hexact.exact_up_to_refinements
    (f ≫ B.ofLE (A ⊔ B) le_sup_right) (by rw [Category.assoc]; exact h2)
  have h4 : (π' ≫ f) ≫ B.arrow = h ≫ A.arrow := by
    have := congr_arg (· ≫ (A ⊔ B).arrow) hh
    simp only [Category.assoc, Subobject.ofLE_arrow] at this
    rw [← Category.assoc] at this; exact this
  have hAf : A.Factors ((π' ≫ f) ≫ B.arrow) := by rw [h4]; exact Subobject.factors_comp_arrow h
  have hBf : B.Factors ((π' ≫ f) ≫ B.arrow) := Subobject.factors_comp_arrow (π' ≫ f)
  have hinf : (A ⊓ B).Factors ((π' ≫ f) ≫ B.arrow) := (Subobject.inf_factors _).mpr ⟨hAf, hBf⟩
  let k := (A ⊓ B).factorThru _ hinf
  have hk := (A ⊓ B).factorThru_arrow _ hinf
  have h7 : k ≫ (A ⊓ B).ofLE B inf_le_right = π' ≫ f :=
    (cancel_mono B.arrow).mp (by rw [Category.assoc, Subobject.ofLE_arrow]; exact hk)
  have h8 : (π' ≫ f) ≫ cokernel.π ((A ⊓ B).ofLE B inf_le_right) = 0 := by
    rw [← h7, Category.assoc, cokernel.condition, comp_zero]
  have h9 : π' ≫ π ≫ g = 0 := by rw [hf, ← Category.assoc, h8]
  haveI : Epi (π' ≫ π) := epi_comp π' π
  exact zero_of_epi_comp _ (by rw [Category.assoc]; exact h9)

instance epi_secondIsoMap (A B : Subobject X) : Epi (secondIsoMap A B) := by
  apply Preadditive.epi_of_cancel_zero
  intro Z g hg
  suffices hπg : cokernel.π (A.ofLE (A ⊔ B) le_sup_left) ≫ g = 0 from
    zero_of_epi_comp (cokernel.π _) hπg
  have hA : A.ofLE (A ⊔ B) le_sup_left ≫ (cokernel.π (A.ofLE (A ⊔ B) le_sup_left) ≫ g) = 0 := by
    rw [← Category.assoc, cokernel.condition, zero_comp]
  have hB : B.ofLE (A ⊔ B) le_sup_right ≫ (cokernel.π (A.ofLE (A ⊔ B) le_sup_left) ≫ g) = 0 := by
    have : cokernel.π ((A ⊓ B).ofLE B inf_le_right) ≫ (secondIsoMap A B ≫ g) = 0 := by
      rw [hg, comp_zero]
    rwa [← Category.assoc, cokernel_π_comp_secondIsoMap, Category.assoc] at this
  -- Kernel/subobject argument: both A and B land in kernel, so kernel.ι is iso
  set f := cokernel.π (A.ofLE (A ⊔ B) le_sup_left) ≫ g with hf_def
  haveI : Mono (kernel.ι f ≫ (A ⊔ B).arrow) := mono_comp _ _
  have hA_le : A ≤ Subobject.mk (kernel.ι f ≫ (A ⊔ B).arrow) := by
    conv_lhs => rw [← Subobject.mk_arrow A]
    exact Subobject.mk_le_mk_of_comm (kernel.lift f (A.ofLE (A ⊔ B) le_sup_left) hA)
      (by rw [← Category.assoc, kernel.lift_ι, Subobject.ofLE_arrow])
  have hB_le : B ≤ Subobject.mk (kernel.ι f ≫ (A ⊔ B).arrow) := by
    conv_lhs => rw [← Subobject.mk_arrow B]
    exact Subobject.mk_le_mk_of_comm (kernel.lift f (B.ofLE (A ⊔ B) le_sup_right) hB)
      (by rw [← Category.assoc, kernel.lift_ι, Subobject.ofLE_arrow])
  have heq : Subobject.mk (kernel.ι f ≫ (A ⊔ B).arrow) = Subobject.mk (A ⊔ B).arrow :=
    le_antisymm (Subobject.mk_le_mk_of_comm (kernel.ι f) rfl)
      (by rw [Subobject.mk_arrow]; exact sup_le hA_le hB_le)
  have hφ : (Subobject.isoOfMkEqMk _ _ heq).hom = kernel.ι f :=
    (cancel_mono (A ⊔ B).arrow).mp (Subobject.ofMkLEMk_comp heq.le)
  haveI : IsIso (kernel.ι f) := hφ ▸ inferInstance
  exact zero_of_epi_comp (kernel.ι f) (kernel.condition f)

/-- The second isomorphism theorem: cokernel(A⊓B → B) ≅ cokernel(A → A⊔B).
    The forward map secondIsoMap is mono and epi, hence iso in abelian category. -/
def secondIso (A B : Subobject X) :
    cokernel ((A ⊓ B).ofLE B inf_le_right) ≅ cokernel (A.ofLE (A ⊔ B) le_sup_left) := by
  haveI := mono_secondIsoMap A B
  haveI := epi_secondIsoMap A B
  haveI : IsIso (secondIsoMap A B) := isIso_of_mono_of_epi _
  exact asIso (secondIsoMap A B)

/-- Convert cokernel using A ⊓ (A ⊔ B) = A (inf_sup_self). -/
def cokernelIsoOfEq_sup (A B : Subobject X) :
    cokernel ((A ⊓ (A ⊔ B)).ofLE (A ⊔ B) inf_le_right) ≅
    cokernel (A.ofLE (A ⊔ B) le_sup_left) :=
  cokernel.mapIso _ _ (Subobject.isoOfEq _ _ inf_sup_self) (Iso.refl _) (by
    simp [Subobject.isoOfEq_hom, Subobject.ofLE_comp_ofLE])

/-- Convert cokernel using (A ⊓ B) ⊓ B = A ⊓ B. -/
def cokernelIsoOfEq_inf (A B : Subobject X) :
    cokernel (((A ⊓ B) ⊓ B).ofLE B inf_le_right) ≅
    cokernel ((A ⊓ B).ofLE B inf_le_right) :=
  cokernel.mapIso _ _ (Subobject.isoOfEq _ _ (inf_eq_left.mpr inf_le_right)) (Iso.refl _) (by
    simp [Subobject.isoOfEq_hom, Subobject.ofLE_comp_ofLE])

/-- The second isomorphism theorem adapted to SubobjectIso format:
    SubobjectIso (A, A ⊔ B) (A ⊓ B, B).

    Uses isoOfEq conversions to handle A ⊓ (A ⊔ B) = A and (A ⊓ B) ⊓ B = A ⊓ B,
    then applies the core secondIso. -/
theorem subobject_second_iso (A B : Subobject X) :
    SubobjectIso (A, A ⊔ B) (A ⊓ B, B) :=
  ⟨cokernelIsoOfEq_sup A B ≪≫ (secondIso A B).symm ≪≫ (cokernelIsoOfEq_inf A B).symm⟩

/-! ## JordanHolderLattice instance for Subobject X

§1.5 Theorem 1.5.4 (Etingof et al.): The lattice of subobjects of an object
in an abelian category satisfies the Jordan-Hölder axioms.
-/

instance jordanHolderLattice_subobject :
    JordanHolderLattice (Subobject X) where
  IsMaximal := SubobjectIsMaximal
  lt_of_isMaximal := CovBy.lt
  sup_eq_of_isMaximal := fun h1 h2 hne => WCovBy.sup_eq h1.wcovBy h2.wcovBy hne
  isMaximal_inf_left_of_isMaximal_sup := fun {x y} hx hy => by
    -- x ⋖ x⊔y and y ⋖ x⊔y → x⊓y ⋖ x
    -- Use second iso theorem: cokernel(y → y⊔x) ≅ cokernel(y⊓x → x)
    -- Transfer CovBy from y ⋖ y⊔x (= x⊔y) to y⊓x ⋖ x (= x⊓y ⋖ x)
    sorry
  Iso := SubobjectIso
  iso_symm := subobjectIso_symm
  iso_trans := subobjectIso_trans
  second_iso := fun {x y} _ => subobject_second_iso x y

end LemmaFeld.TensorCategories.Chapter1
