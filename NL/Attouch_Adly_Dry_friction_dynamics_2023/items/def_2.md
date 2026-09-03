## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/def_2.lean`

## Lean statement
```lean
def IsDrygradTrajectory {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (r : ℝ) (hr : 0 < r) (f : H → ℝ) (hf : Differentiable ℝ f)
    (z dz : ℝ → H) (t₀ : ℝ) : Prop :=
  let _ := hr
  let _ := hf
  ∀ t ∈ Set.Ici t₀, HasDerivAt z (dz t) t ∧
    ∃ u : H,
      (∀ y : H,
        (dryFrictionPotential (H := H) r (dz t) : EReal) +
            (inner ℝ u (y - dz t) : EReal) ≤
          (dryFrictionPotential (H := H) r y : EReal)) ∧
        dz t + u + gradient f (z t) = 0
```

## Statement explanation
The declaration defines a predicate named `IsDrygradTrajectory`; it is a definition, not a theorem asserting existence of such a trajectory. Its inputs are:

- An implicit type `H` together with typeclass hypotheses: `H` is a normed additive commutative group, it has a real inner product space structure over `ℝ`, and it is complete. Thus `H` is a real Hilbert-type space.
- `r : ℝ`, a real parameter, and `hr : 0 < r`, a hypothesis that `r` is positive.
- `f : H → ℝ`, a real-valued function on `H`, and `hf : Differentiable ℝ f`, a hypothesis that `f` is differentiable.
- `z dz : ℝ → H`, two functions from real time to vectors in `H`.
- `t₀ : ℝ`, a real initial time.

The predicate says:

For every real time `t` with `t₀ ≤ t`, written `t ∈ Set.Ici t₀`, the following two conditions hold.

First, `HasDerivAt z (dz t) t`: the function `z` has derivative `dz t` at time `t`.

Second, there exists a vector `u : H` such that:

1. For every vector `y : H`,
   \[
   \operatorname{dryFrictionPotential}(H:=H, r, dz t) + \langle u, y - dz t\rangle
   \le
   \operatorname{dryFrictionPotential}(H:=H, r, y)
   \]
   in the extended real line `EReal`.
   Here `dryFrictionPotential` is an existing previously defined function whose values are extended real numbers. The real inner product term `inner ℝ u (y - dz t)` is coerced to `EReal` so that the addition and comparison take place in `EReal`. This inequality says that `u` satisfies the subgradient inequality for the dry-friction potential at the point `dz t`.

2. The vector equation
   \[
   dz t + u + \operatorname{gradient} f (z t) = 0
   \]
   holds in `H`, where `gradient f (z t)` is the gradient vector of `f` at `z t`.

Because the existential quantifier over `u` appears inside the universal quantifier over `t`, the vector `u` may depend on the time `t`. The argument `hr : 0 < r` and `hf : Differentiable ℝ f` are bound inside the definition using dummy `let _ := hr` and `let _ := hf`, so they are type-validity requirements but are not otherwise used in the formula.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part in the source. The proof slot after the declaration contains only the comment “No separate proof part.” Therefore there are no proof steps and no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` to explain.

The declaration itself is a definitional proposition. Its body begins with the two dummy let-bindings `let _ := hr` and `let _ := hf`, which bind the assumptions `hr` and `hf` to anonymous names and discard them. This does not add any mathematical condition. The remaining content is the formula described above: for every `t` with `t₀ ≤ t`, require differentiability of `z` at `t`, and the existence of a vector `u` satisfying the subgradient-type inequality for the dry-friction potential and the equality involving velocity, friction, and gradient of `f`.

