## Source file
`Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022/items/def_6.lean`

## Lean statement
```lean
def stronglyConvexEnergyConstant {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (u : ℝ → H) (xStar : H) (mu t0 : ℝ)
    (hxStar : ∀ x : H, f xStar ≤ f x ∧ (f x = f xStar → x = xStar)) : ℝ :=
  stronglyConvexLyapunov f u xStar mu t0 hxStar * Real.exp (Real.sqrt mu * t0)
```

## Statement explanation
The declaration defines a real-valued constant attached to a strongly convex energy setup. The implicit type $H$ is assumed to be a real inner product space: it has a normed additive commutative group structure and an inner product over $\mathbb R$. There is no completeness or Hilbert-space hypothesis visible in the declaration. The explicit inputs are a function $f : H \to \mathbb R$, a function $u : \mathbb R \to H$, a point $x^\star \in H$, real parameters $\mu,t_0 \in \mathbb R$, and a proof term $h_{x^\star}$. The proof term $h_{x^\star}$ states that for every $x \in H$,

$$
f(x^\star) \le f(x) \quad\text{and}\quad \bigl(f(x)=f(x^\star) \Rightarrow x=x^\star\bigr).
$$

Thus $x^\star$ is a global minimizer of $f$, and it is the unique point at which the minimum value is attained. The definition then returns the real number

$$
\operatorname{stronglyConvexEnergyConstant}(f,u,x^\star,\mu,t_0,h_{x^\star})
=
\operatorname{stronglyConvexLyapunov}(f,u,x^\star,\mu,t_0,h_{x^\star})
\cdot
\exp\!\left(\sqrt{\mu}\,t_0\right).
$$

In words, it takes the value of the previously defined quantity `stronglyConvexLyapunov` on the same data and multiplies it by the exponential factor $e^{\sqrt{\mu}\,t_0}$. The multiplication inside the exponential is $(\sqrt{\mu}) \cdot t_0$, not $\sqrt{\mu t_0}$. No assumption that $\mu \ge 0$ or $t_0 \ge 0$ is present. Although the name refers to strong convexity, the declaration itself only records this product formula; it does not assert convexity of $f$, monotonicity, differentiability, or any inequality beyond those contained in $h_{x^\star}$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. This is a `def`, not a theorem, and the Lean source contains no `:= by` proof block or tactic sequence. The entire mathematical content is the defining term

$$
\operatorname{stronglyConvexLyapunov}(f,u,x^\star,\mu,t_0,h_{x^\star})
\cdot
\operatorname{Real.exp}\!\left(\operatorname{Real.sqrt}(\mu)\cdot t_0\right).
$$

Unfolding `stronglyConvexEnergyConstant` on given arguments therefore yields exactly this product. The first factor is the result of applying the earlier function `stronglyConvexLyapunov` to the arguments $f,u,x^\star,\mu,t_0,h_{x^\star}$. Since no statement of `stronglyConvexLyapunov` is supplied, its internal formula cannot be determined from the source, and the only precise fact available here is that it supplies the first factor as a real number. The second factor is computed using the real square root and real exponential functions: it is $\exp(\sqrt{\mu}\,t_0)$. No named theorem or lemma is invoked, and no rewriting, simplification, or arithmetic tactic such as `rw`, `simp`, `exact`, or `linarith` occurs. The proof argument $h_{x^\star}$ is not analyzed in this definition; it is merely passed as an input to `stronglyConvexLyapunov`.

