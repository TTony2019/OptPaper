## Source file
`Alvarez_Minimizing_property_second_order_dissipative_2000/items/def_1.lean`

## Lean statement
```lean
structure DissipativeSystem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (gamma : ℝ) (Phi : H → ℝ) (gradPhi : H → H) (u0 v0 : H) where
  gamma_pos : 0 < gamma
  is_gradient : ∀ x : H, HasGradientAt Phi (gradPhi x) x
  u : ℝ → H
  contDiff : ContDiffOn ℝ 2 u (Set.Ici 0)
  initial_position : u 0 = u0
  initial_velocity : fderiv ℝ u 0 1 = v0
  equation : ∀ t ∈ Set.Ici (0 : ℝ),
    fderiv ℝ (fun s => fderiv ℝ u s 1) t 1 + gamma • fderiv ℝ u t 1 + gradPhi (u t) = 0
```

## Statement explanation
This declaration is a Lean `structure`, not a theorem, so it introduces a type of records rather than proving a proposition. The structure `DissipativeSystem` is parameterized by a type \(H\), a real number \(\gamma\), a function \(\Phi : H \to \mathbb R\), a map \(\operatorname{gradPhi} : H \to H\), and two initial vectors \(u_0, v_0 \in H\). The type \(H\) carries the typeclass assumptions that it is a normed additive commutative group, a real inner product space, and complete; together these make \(H\) a real Hilbert space.

A term of type `DissipativeSystem gamma Phi gradPhi u0 v0` packages the following data and properties:

- A proof that \(0 < \gamma\). Thus \(\gamma\) is a positive real parameter, intended as a damping or friction coefficient.
- A proof that for every \(x \in H\), the predicate `HasGradientAt Phi (gradPhi x) x` holds. Mathematically, this means that at every point \(x\), the vector \(\operatorname{gradPhi}(x)\) is the gradient of the potential \(\Phi\) at \(x\). The exact library definition of `HasGradientAt` is not expanded in the source, but the visible content is precisely this gradient assertion for each \(x \in H\).
- A trajectory function \(u : \mathbb R \to H\).
- A proof that \(u\) is twice continuously differentiable on the half-line \( [0,\infty) \), expressed by `ContDiffOn ℝ 2 u (Set.Ici 0)`. Thus the differentiability is required only for nonnegative times.
- The initial condition \(u(0) = u_0\). So the trajectory starts at the prescribed position \(u_0\).
- The initial velocity condition. In Lean, `fderiv ℝ u 0 1 = v0` means that the Fréchet derivative of \(u\) at time \(0\), evaluated on the scalar \(1\), equals \(v_0\). Since the domain is \(\mathbb R\), this is the ordinary derivative vector \(u'(0)\), so the trajectory starts with prescribed velocity \(v_0\).
- For every \(t \in [0,\infty)\), the second-order differential equation
  \[
  u''(t) + \gamma u'(t) + \operatorname{gradPhi}(u(t)) = 0
  \]
  holds in \(H\). Here \(u'(t) = D u(t)(1)\) and
  \[
  u''(t) = D\bigl(s \mapsto D u(s)(1)\bigr)(t)(1),
  \]
  exactly as encoded by the nested uses of `fderiv ℝ`. The term \(\gamma u'(t)\) is scalar multiplication of the velocity by \(\gamma\), and \(\operatorname{gradPhi}(u(t))\) is the gradient force evaluated along the trajectory.

Thus the declaration defines what it means to be a dissipative system: a real Hilbert space, a positive damping coefficient, a potential with a chosen gradient field, initial position and velocity, and a \(C^2\) half-line trajectory satisfying the damped gradient-flow equation. It is a bundle of data and hypotheses; it does not assert that such a trajectory exists.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The Lean proof block contains only the comment `-- No separate proof part.` Therefore no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, and no named local theorems or lemmas are invoked. The mathematical obligations are exactly the fields of the structure: to construct a term of `DissipativeSystem gamma Phi gradPhi u0 v0`, one must supply proofs of `gamma_pos`, `is_gradient`, `contDiff`, `initial_position`, `initial_velocity`, and `equation`, together with the trajectory data `u`. The field `is_gradient` supplies the gradient property for \(\Phi\), the field `contDiff` supplies the required differentiability on \( [0,\infty) \), and the field `equation` is a required differential equation rather than a derived conclusion. No step-by-step mathematical proof is present in the source.

