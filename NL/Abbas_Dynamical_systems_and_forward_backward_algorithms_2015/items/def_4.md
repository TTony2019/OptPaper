## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/def_4.lean`

## Lean statement
```lean
structure GradientProjectionDynamics {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Psi : H → ℝ) (C : Set H) (tangentCone : H → Set H)
    (projection : H → Set H → H) where
  closed_convex : IsClosed C ∧ Convex ℝ C
  x : ℝ → H
  path_in_constraint : ∀ t, 0 ≤ t → x t ∈ C
  tangent_cone_at_path : ∀ t, 0 ≤ t → tangentCone (x t) = tangentConeAt ℝ C (x t)
  projection_mem : ∀ t, 0 ≤ t →
    projection (-(∇ Psi (x t))) (tangentCone (x t)) ∈ tangentCone (x t)
  projection_min_dist : ∀ t, 0 ≤ t → ∀ z ∈ tangentCone (x t),
    ‖-(∇ Psi (x t)) - projection (-(∇ Psi (x t))) (tangentCone (x t))‖ ≤
      ‖-(∇ Psi (x t)) - z‖
  differential_equation : ∀ t, 0 ≤ t →
    deriv x t = projection (-(∇ Psi (x t))) (tangentCone (x t))
```

## Statement explanation
The declaration introduces a structure named `GradientProjectionDynamics`. Its ambient data are a type $H$ equipped with a normed additive commutative group structure, a real inner product space structure, and a completeness assumption. Thus $H$ is a real Hilbert space. The structure is parameterized by a function $\Psi : H \to \mathbb{R}$, which is a scalar potential or objective; a set $C \subseteq H$, which is the constraint set; a function $\operatorname{tangentCone} : H \to \mathcal{P}(H)$, assigning to each point a set of tangent vectors; and a function $\operatorname{projection} : H \to \mathcal{P}(H) \to H$, which takes a vector and a set and returns a vector of $H$.

The fields of the structure encode the following mathematical requirements.

- `closed_convex`: the set $C$ is closed and convex over $\mathbb{R}$, i.e.

  $$
  \operatorname{IsClosed}(C) \land \operatorname{Convex}_{\mathbb R}(C).
  $$

- `x`: there is a trajectory

  $$
  x : \mathbb{R} \to H.
  $$

- `path_in_constraint`: for every nonnegative time $t$,

  $$
  0 \le t \implies x(t) \in C.
  $$

  Thus the trajectory remains in the constraint set for forward time.

- `tangent_cone_at_path`: for every nonnegative time $t$,

  $$
  0 \le t \implies \operatorname{tangentCone}(x(t)) = \operatorname{tangentConeAt}_{\mathbb R}(C, x(t)).
  $$

  The user-supplied tangent-cone map agrees, along the trajectory for $t \ge 0$, with the actual tangent cone to $C$ at the point $x(t)$.

- `projection_mem`: for every nonnegative time $t$,

  $$
  0 \le t \implies
  \operatorname{projection}\!\left(-(\nabla \Psi)(x(t)), \operatorname{tangentCone}(x(t))\right)
  \in \operatorname{tangentCone}(x(t)).
  $$

  So the projected vector lies in the tangent cone.

- `projection_min_dist`: for every nonnegative time $t$ and every $z \in \operatorname{tangentCone}(x(t))$,

  $$
  \left\|
  -(\nabla \Psi)(x(t)) -
  \operatorname{projection}\!\left(-(\nabla \Psi)(x(t)), \operatorname{tangentCone}(x(t))\right)
  \right\|
  \le
  \left\|
  -(\nabla \Psi)(x(t)) - z
  \right\|.
  $$

  Hence the projected vector is a closest point in the tangent cone to the negative gradient $-\nabla \Psi(x(t))$, i.e. it is a metric projection of that vector onto the tangent cone.

- `differential_equation`: for every nonnegative time $t$,

  $$
  0 \le t \implies
  \operatorname{deriv} x(t)
  =
  \operatorname{projection}\!\left(-(\nabla \Psi)(x(t)), \operatorname{tangentCone}(x(t))\right).
  $$

  Thus the velocity of the trajectory is the projection of the negative gradient onto the tangent cone at the current point.

Overall, the structure packages the data and properties of a constrained gradient-flow trajectory: for $t \ge 0$, the trajectory $x(t)$ stays in the closed convex set $C$, and it evolves according to the projected differential equation

$$
\dot{x}(t) = P_{T_C(x(t))}\bigl(-\nabla \Psi(x(t))\bigr),
$$

where the projection is the closest-point projection onto the tangent cone to $C$ at $x(t)$. The structure records the potential, the constraint set, the tangent-cone map, the projection operation, and a trajectory satisfying these forward-time projected-dynamics conditions. It does not itself assert that such a trajectory exists.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `structure`, so it defines a record type and its projection functions rather than proving a proposition. The Lean proof block is empty. Consequently, there are no tactic steps such as `intro`, `rw`, `simp`, `exact`, or `linarith` to analyze, and no named lemma or theorem is invoked. The mathematical content is exactly the list of fields described in the first section: an inhabitant of `GradientProjectionDynamics` would have to supply a closed convex set $C$, a trajectory $x$, the membership and tangent-cone agreement properties along $x$, the membership and minimal-distance properties of the projection, and the projected differential equation for all nonnegative times. No additional assumptions or conclusions are introduced beyond those fields.

