## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/ext_def_3.lean`

## Lean statement
```lean
def IsMetricProjection {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (_hC : C.Nonempty) (_hclosed : IsClosed C) (_hconvex : Convex ℝ C) (u p : H) : Prop := IsBestApproximation u C p ∧
  ∀ v ∈ C, ⟪v - p, u - p⟫ ≤ 0
```

## Statement explanation
The declaration introduces the predicate `IsMetricProjection`. Its ambient object is a type $H$ equipped with the structures `NormedAddCommGroup H` and `InnerProductSpace ℝ H`. Thus $H$ is a real inner product space whose additive group is normed: it has addition, subtraction, a norm, and a real-valued inner product $\langle \cdot,\cdot\rangle$. No completeness hypothesis is included, so $H$ is not assumed to be a Hilbert space. The set $C\subseteq H$ is a parameter. The arguments `_hC`, `_hclosed`, and `_hconvex` are, respectively, a proof that $C$ is nonempty, a proof that $C$ is closed in the norm topology, and a proof that $C$ is convex over $\mathbb R$; these are hypotheses supplied to the definition, but they are not used in the defining right-hand side. The points $u,p\in H$ are also parameters: $u$ is the point being approximated or projected, and $p$ is the candidate projection. The declaration returns a proposition.

The defining right-hand side is the conjunction

$$
\text{IsBestApproximation}(u,C,p)
\;\wedge\;
\forall v\in C,\ \langle v-p,\,u-p\rangle\le 0 .
$$

The first conjunct is the imported predicate `IsBestApproximation u C p`, whose mathematical role is that $p$ is a best approximation to $u$ from the set $C$. In the usual Mathlib formulation this means that $p\in C$ and $\operatorname{dist}(u,p)\le \operatorname{dist}(u,y)$ for every $y\in C$; the source here does not unfold that imported predicate further. The second conjunct says that for every $v\in C$, the real inner product of the difference $v-p$ with the residual $u-p$ is nonpositive. Since the inner product is symmetric on a real inner product space, this is the same as requiring

$$
\langle u-p,\,v-p\rangle\le 0
$$

for all $v\in C$. This is the usual variational inequality expressing that the residual vector $u-p$ makes a nonpositive inner product with every direction from $p$ into the convex set $C$, i.e. that $u-p$ lies in the normal cone to $C$ at $p$. Thus the definition packages together the closest-point condition and the normal-cone/variational-inequality condition for a metric projection.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof. The declaration is a `def`, and the Lean proof field is empty. Consequently there are no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no named local theorem or lemma is cited. The entire mathematical content is the definitional right-hand side

$$
\text{IsBestApproximation}(u,C,p)
\;\wedge\;
\forall v\in C,\ \langle v-p,\,u-p\rangle\le 0 .
$$

The parameters `_hC`, `_hclosed`, and `_hconvex` appear in the signature but are not used in the body of the definition; they do not become conjuncts of the resulting proposition. The variables $C$, $u$, and $p$ occur only in the best-approximation conjunct and in the universal inner-product inequality. Thus, for a fixed set $C$ and points $u,p$, unfolding `IsMetricProjection` reduces it exactly to the displayed conjunction, with no additional proof steps or hidden mathematical argument.

