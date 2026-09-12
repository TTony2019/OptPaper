## Source file
`Alvarez_Minimizing_property_second_order_dissipative_2000/items/ext_def_7.lean`

## Lean statement
```lean
noncomputable def PositiveQuadraticPotential.potential {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {A : H →L[ℝ] H}
    (_ : PositiveQuadraticPotential A) (x : H) : ℝ :=
  (1 / 2 : ℝ) * ⟪A x, x⟫_ℝ
```

## Statement explanation
The declaration introduces a real-valued function `PositiveQuadraticPotential.potential` associated with a continuous linear operator $A$ on a complete real inner product space $H$. The ambient type $H$ is assumed to carry a normed additive commutative group structure, a real inner product space structure, and a completeness structure; equivalently, the setting is a real Hilbert space. The operator $A\colon H\to H$ is a continuous $\mathbb R$-linear map. There is also an argument of type $\mathrm{PositiveQuadraticPotential} A$, meaning that $A$ is assumed to satisfy the property named `PositiveQuadraticPotential`; the present declaration does not expand the internal conditions of that property. Finally, $x$ is a vector of $H$. The definition is marked `noncomputable`, so Lean treats it as a noncomputable function, but mathematically it is still an ordinary definition of a real-valued function.

For such an $A$, a witness $p$ of $\mathrm{PositiveQuadraticPotential} A$, and a vector $x\in H$, the potential is defined by

```math
\mathrm{potential}_{A,p}(x)
= \frac{1}{2}\,\langle A x, x\rangle_{\mathbb R}.
```

Thus the potential is the real scalar obtained by applying the continuous linear map $A$ to $x$, taking the real inner product with $x$, and multiplying the resulting real number by $1/2$. The argument $p$ does not occur on the right-hand side, so the value of the potential does not depend on which witness of the positive quadratic potential property is supplied. The completeness assumption on $H$ is part of the ambient context in which the property $\mathrm{PositiveQuadraticPotential} A$ is stated, but it does not appear in the displayed formula itself.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part: this is a definition, not a theorem. The only content is the defining equation

```math
\mathrm{potential}_{A,p}(x)
= \frac{1}{2}\,\langle A x, x\rangle_{\mathbb R}.
```

There are no proof tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no named lemmas or previously established results are invoked. The unused argument $p$ of type $\mathrm{PositiveQuadraticPotential} A$ is indicated by the underscore in the Lean source; since it is absent from the right-hand side, the defined value does not computationally depend on it. The hypotheses on $H$ and the assumption that $A$ satisfies the positive quadratic potential property are part of the surrounding context needed to type the definition, but they are not used as proof steps. The mathematical content is simply that $x$ is sent to $\frac{1}{2}\langle A x,x\rangle_{\mathbb R}$.

