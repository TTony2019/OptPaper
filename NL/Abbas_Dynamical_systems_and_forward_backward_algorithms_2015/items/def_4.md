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
Let \(H\) be a type. The declaration assumes \(H\) has a normed additive commutative group structure, a real inner product space structure over \(\mathbb R\), and is complete, so \(H\) is a real Hilbert space. Let \(\Psi: H \to \mathbb R\) be a real-valued function, \(C: \mathrm{Set}\,H\) be a subset of \(H\), \(\mathrm{tangentCone}: H \to \mathrm{Set}\,H\) be a map assigning to each point of \(H\) a set of tangent vectors, and \(\mathrm{projection}: H \to \mathrm{Set}\,H \to H\) be a map taking a vector and a set and returning a vector.

The declaration defines a structure type \(\mathsf{GradientProjectionDynamics}\) with these parameters. A term of this structure consists of the following data and properties:

- \(\mathsf{closed\_convex}\): the set \(C\) is closed and convex in \(H\). Symbolically, \(\operatorname{IsClosed} C \wedge \operatorname{Convex}_{\mathbb R} C\).
- \(\mathsf{x}\): a curve \(x: \mathbb R \to H\), parameterized by real time.
- \(\mathsf{path\_in\_constraint}\): for every \(t \ge 0\), the point \(x(t)\) lies in \(C\).
- \(\mathsf{tangent\_cone\_at\_path}\): for every \(t \ge 0\), the supplied set \(\mathrm{tangentCone}(x(t))\) equals the actual tangent cone of \(C\) at \(x(t)\), written \(\mathrm{tangentConeAt}_{\mathbb R} C (x(t))\).
- \(\mathsf{projection\_mem}\): for every \(t \ge 0\), the element obtained by applying \(\mathrm{projection}\) to the negative gradient \(-\nabla \Psi(x(t))\) and to \(\mathrm{tangentCone}(x(t))\) belongs to \(\mathrm{tangentCone}(x(t))\).
- \(\mathsf{projection\_min\_dist}\): for every \(t \ge 0\) and every \(z\) in \(\mathrm{tangentCone}(x(t))\), the distance from \(-\nabla \Psi(x(t))\) to that projected point is at most the distance from \(-\nabla \Psi(x(t))\) to \(z\). Thus the projected point is a nearest point to the negative gradient among all tangent vectors.
- \(\mathsf{differential\_equation}\): for every \(t \ge 0\), the derivative of the curve \(x\) at time \(t\), denoted \(\mathrm{deriv}\,x\,t\), equals \(\mathrm{projection}(-\nabla \Psi(x(t)), \mathrm{tangentCone}(x(t)))\).

The overall conclusion is: given the Hilbert space \(H\), the function \(\Psi\), the constraint set \(C\), the tangent-cone map, and the projection operator, an object of this structure is a curve \(x\) inside \(C\) whose tangent cone along the path matches the true tangent cone, whose projected negative gradients are chosen with minimal distance, and which satisfies the differential equation
\[
x'(t)=\operatorname{proj}_{\mathrm{tangentCone}(x(t))}(-\nabla \Psi(x(t)))
\]
for all \(t\ge 0\).

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof in the Lean source. The declaration is only a structure definition, and the source explicitly contains the comment “No separate proof part.” Consequently there are no Lean proof commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` to explain. The structure’s fields are not proved consequences; they are the requirements that any instance of \(\mathsf{GradientProjectionDynamics}\) must satisfy. To construct an instance, one would have to supply a curve \(x\) and proofs of each field, but such a construction is not given in this file.

