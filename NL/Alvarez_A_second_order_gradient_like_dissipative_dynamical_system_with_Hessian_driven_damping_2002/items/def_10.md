## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/def_10.lean`

## Lean statement
```lean
noncomputable def constrainedEnergy {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Φ : H → ℝ) (a b ell : ℝ) (x y : H) : ℝ := ell * Φ x + (1 / 2) * ‖a • x + b • y‖ ^ 2
```

## Statement explanation
`constrainedEnergy` is a noncomputable definition. It takes a type $H$ equipped with the structure of a normed additive commutative group and of a normed vector space over $\mathbb R$; thus $H$ is treated as a real normed vector space. The remaining inputs are a function $\Phi : H \to \mathbb R$, three real parameters $a,b,\ell \in \mathbb R$, and two points $x,y \in H$.

The definition assigns to these data the real number

$$
\mathrm{constrainedEnergy}(\Phi,a,b,\ell,x,y)
=
\ell\,\Phi(x) + \frac12\,\lVert a \bullet x + b \bullet y\rVert^2 .
$$

Here $a \bullet x$ and $b \bullet y$ are the scalar multiples of $x$ and $y$ by the real numbers $a$ and $b$, so $a \bullet x + b \bullet y$ is a vector in $H$. Its norm $\lVert a \bullet x + b \bullet y\rVert$ is a real number, and that norm is squared and multiplied by $\frac12$. The first term $\ell\,\Phi(x)$ is the real number obtained by evaluating $\Phi$ at $x$ and multiplying by the real scalar $\ell$. The definition therefore produces a real-valued function of the point $x$ and the auxiliary point $y$, built from the scalar value $\Phi(x)$ and a quadratic norm term involving the linear combination $a \bullet x + b \bullet y$. The word `noncomputable` records that this definition is not intended as executable computational data, but it does not change its mathematical meaning.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part for this declaration because it is a definition, not a theorem or lemma. The Lean proof block contains only the comment that no separate proof part exists. Consequently there are no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` to explain, and no named local theorem, lemma, or previously established fact is invoked. The entire mathematical content is the definitional equation

$$
\mathrm{constrainedEnergy}(\Phi,a,b,\ell,x,y)
=
\ell\,\Phi(x) + \frac12\,\lVert a \bullet x + b \bullet y\rVert^2 .
$$

So any later use of `constrainedEnergy` can unfold it to this displayed right-hand side.

