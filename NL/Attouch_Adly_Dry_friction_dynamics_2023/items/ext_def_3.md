## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/ext_def_3.lean`

## Lean statement
```lean
def IsFrictionBallProjection {H : Type*} [PseudoMetricSpace H] [Zero H]
    (r : ℝ) (x p : H) : Prop := p ∈ frictionBallProjector r x
```

## Statement explanation
The declaration defines a predicate named `IsFrictionBallProjection`. The underlying type is `H`, which is arbitrary but must have two typeclass structures: `[PseudoMetricSpace H]`, meaning `H` is equipped with a pseudo-metric, and `[Zero H]`, meaning `H` has a distinguished zero element. The declaration has explicit parameters `(r : ℝ)`, so `r` is a real number, and `(x p : H)`, so both `x` and `p` are elements of `H`. The conclusion is the proposition `IsFrictionBallProjection r x p`, defined to be the statement `p ∈ frictionBallProjector r x`. Thus it asserts that the element `p` belongs to the set denoted by `frictionBallProjector r x`, which is a friction-ball projection set depending on the real radius `r` and the point `x`.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. This declaration is a `def`, not a theorem, so it does not claim that any point is or is not in `frictionBallProjector r x`; instead, it introduces an abbreviation. The right-hand side, `p ∈ frictionBallProjector r x`, is itself the proposition that defines `IsFrictionBallProjection r x p`. Consequently, no proof commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` appear, because no mathematical fact is being proved.

