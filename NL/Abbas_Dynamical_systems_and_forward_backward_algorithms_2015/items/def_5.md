## Source file
`Abbas_Dynamical_systems_and_forward_backward_algorithms_2015/items/def_5.lean`

## Lean statement
```lean
structure ProximalGradientDynamics {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (mu : ℝ) where
  mu_pos : 0 < mu
  x : ℝ → H
  differential_equation : ∀ t,
    deriv x t + x t - ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, mu_pos⟩
      (x t - mu • B (x t)) = 0
```

## Statement explanation
The declaration defines a **structure**, not a theorem. A structure is a type whose terms are records of data and proof fields satisfying the stated conditions.

The structure is named `ProximalGradientDynamics`. It is parameterized by a type `H`, together with implicit typeclass assumptions that `H` is a normed additive commutative group, carries an inner product over `ℝ`, and is complete. Thus, in this context, `H` is a real Hilbert space.

Other parameters are:
- `Phi`, a function from `H` to values in the extended-real type `EReal`, with the restriction that every value lies in the set `Set.Ioi ⊥`, i.e. is strictly greater than the bottom element `⊥` of `EReal`.
- `hPhi`, a proof that `Phi` belongs to the set/class `ERealFunction.gammaZero H`. This is an assumption needed as an argument to the proximity operator.
- `B`, a function from `H` to `H`, i.e. a vector field on `H`.
- `mu`, a real number.

A term of the structure `ProximalGradientDynamics Phi hPhi B mu` consists of the following fields:
- `mu_pos`: a proof that `0 < mu`.
- `x`: a curve `x : ℝ → H`, assigning to each real time a point of `H`.
- `differential_equation`: a proof that, for every real time `t`,
\[
\dot x(t) + x(t) - P\bigl(x(t) - \mu B(x(t))\bigr) = 0,
\]
where \(\dot x(t)\) denotes `deriv x t`, the derivative of the curve `x` at time `t`, and \(P\) abbreviates the expression `ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, mu_pos⟩`. Thus \(P\) is the scaled proximity operator of `Phi` with scaling parameter `mu`, using the positivity proof `mu_pos`. The argument \(x(t) - \mu B(x(t))\) is the current point `x t` minus the scalar multiple by `mu` of the vector `B (x t)`. The whole equality is an equality of vectors in `H`.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part in the source. After the structure declaration, the file only states that no proof is provided. Because this is a `structure` declaration, its role is definitional rather than proof-theoretic: it introduces the type of triples
\[
(\mathit{mu\_pos},\; x,\; \mathit{differential\_equation})
\]
satisfying the stated conditions. To construct an element of this structure, one would have to supply a proof that `mu > 0`, choose a curve `x`, and prove the differential equation for all real times `t`. The assumptions `Phi`, `hPhi`, `B`, and `mu` are fixed parameters of the structure, while `x` is part of the data being bundled. No commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` appear in a proof, and no further mathematical facts are derived from this definition.

