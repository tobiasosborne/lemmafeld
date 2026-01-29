# Proof Patterns

Reusable proof techniques discovered during formalization.

## Subobject Equality from Zero Arrow

```lean
/-- If a subobject's arrow is zero, the subobject equals ⊥. -/
lemma subobject_eq_bot_of_arrow_eq_zero (A : Subobject X) (h : A.arrow = 0) : A = ⊥ := by
  apply Subobject.eq_of_comm (isoZeroOfMonoEqZero h ≪≫ Subobject.botCoeIsoZero.symm)
  calc _ ≫ (⊥ : Subobject X).arrow = _ ≫ 0 := by rw [Subobject.bot_arrow]
    _ = 0 := by simp
    _ = A.arrow := h.symm
```

## Antitone Chain Stabilization

For antitone chains on Artinian objects:

```lean
lemma imageSubobject_stabilizes [IsArtinianObject X] :
    ∃ n : ℕ, ∀ m : ℕ, n ≤ m → imageSubobject (f ^ n) = imageSubobject (f ^ m) := by
  have hf : Antitone (fun n => imageSubobject (f ^ n)) := imageSubobject_antitone f
  have hf' : Monotone (fun n => OrderDual.toDual (imageSubobject (f ^ n))) := hf
  obtain ⟨n, hn⟩ := antitone_chain_condition_of_isArtinianObject ⟨_, hf'⟩
  refine ⟨n, fun m hm => ?_⟩
  have heq := hn m hm
  simp only [OrderHom.coe_mk, OrderDual.toDual_inj] at heq
  exact heq
```

Key: `OrderDual.toDual_inj` unwraps equality in order dual.

## k-Scalar Through A-Linear Equiv

When `equiv : X ≃ₗ[A] ker π` is A-linear, handle k-scalar as:

```lean
have h : equiv (r • equiv.symm ⟨...⟩) = r • ⟨...⟩ := by
  rw [← smul_one_smul A r (equiv.symm _), LinearEquiv.map_smul,
      LinearEquiv.apply_symm_apply, smul_one_smul]
```

## D(1) = 0 from Leibniz Rule

For derivation-like D with D(ab) = a•D(b) + D(a)•b:

```lean
-- From h : D 1 = D 1 + D 1
have : (0 : M) = D 1 := by
  calc (0 : M) = D 1 - D 1 := (sub_self (D 1)).symm
       _ = (D 1 + D 1) - D 1 := by rw [← h]
       _ = D 1 := add_sub_cancel_right (D 1) (D 1)
exact this.symm
```

## Prod.mk Equality

For `Prod.mk = Prod.mk` goals:
- Use `Prod.mk.injEq` to split into components
- After `simp ... [Prod.mk.injEq]`, goals may become `_ ∧ True` — use `trivial` not `rfl`
- `Prod.mk_add_mk` for `(a, b) + (c, d) = (a + c, b + d)`

## Quotient Module Membership

```lean
-- Element is zero in quotient iff in submodule
Submodule.Quotient.mk_eq_zero : Submodule.Quotient.mk x = 0 ↔ x ∈ S

-- Surjectivity for existence arguments
Submodule.mkQ_surjective : Function.Surjective S.mkQ
```

## Tactic Selection for Algebraic Goals

| Goal Type | Tactic |
|-----------|--------|
| Additive module equations | `abel` |
| Ring equations | `ring` |
| Linear inequalities (numbers) | `linarith` |
| Module subtraction | `sub_self x`, `add_sub_cancel_right x y` |
| Module associativity | `mul_smul` (unqualified) |

**Note:** `ring` and `linarith` don't work on module elements!
