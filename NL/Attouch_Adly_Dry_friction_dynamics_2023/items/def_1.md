## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/def_1.lean`

## Lean statement
```lean
def IsDryFrictionPotential {H : Type*} [NormedAddCommGroup H] (φ : H → ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ x, φ x = r * ‖x‖
```

## Statement explanation
`H` is a type variable (a type in an arbitrary universe). The typeclass `[NormedAddCommGroup H]` means `H` carries the structure of a normed additive commutative group, so it has an addition, negation, zero, and a norm `‖·‖ : H → ℝ` satisfying the usual normed-group axioms. The term `φ : H → ℝ` is a function assigning a real number to every element of `H`. The declaration `IsDryFrictionPotential φ` is a proposition defined to mean:
`∃ r : ℝ, 0 < r ∧ ∀ x, φ x = r * ‖x‖`.
Thus `IsDryFrictionPotential φ` states that there exists a real number `r` such that `r` is strictly positive, and for every element `x` in `H`, the value `φ x` equals `r` multiplied by the norm of `x`. In symbols, `φ` is a real scalar multiple of the norm function, with positive scalar.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
This is a `def`, not a theorem with a proof. The declaration simply defines the predicate `IsDryFrictionPotential` by giving the right-hand side `∃ r : ℝ, 0 < r ∧ ∀ x, φ x = r * ‖x‖`. There is no separate proof part, and indeed the source contains only a comment saying that there is no separate proof. No Lean proof commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` are used, because nothing is being proved: the statement itself is the defining definitional content of the named proposition.

