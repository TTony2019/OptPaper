## Source file
`Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006/items/def_10.lean`

## Lean statement
```lean
def IsStronglyConvex (f : H → ℝ) (M : ℝ) : Prop :=
  M > 0 ∧ ContDiff ℝ 1 f ∧ ∀ x y, inner ℝ (gradient f x - gradient f y) (x - y) ≥ M * ‖x - y‖^2
```

## Statement explanation
The declaration introduces a predicate $\mathrm{IsStronglyConvex}$ for a function $f : H \to \mathbb R$ and a real number $M$. The visible notation uses a real inner product $\langle \cdot,\cdot\rangle_{\mathbb R}$, a norm $`\|\cdot\|`$, and a gradient$\nabla f$, so$H$is the ambient domain type carrying those operations; the declaration itself does not further specify$H$. The parameters are therefore a real-valued function$f$, a real scalar$M$, and, inside the quantified condition, arbitrary points$x,y \in H$.

The definitional body is the proposition

```math
M>0 \;\wedge\; \mathrm{ContDiff}_{\mathbb R}^{1}(f)
\;\wedge\;
\forall x,y,\
\bigl\langle \nabla f(x)-\nabla f(y),\,x-y\bigr\rangle_{\mathbb R}
\ge M\,\|x-y\|^2 .
```

Thus $\mathrm{IsStronglyConvex}(f,M)$ means that three requirements all hold:

1. The modulus $M$ is strictly positive: $M\gt 0$.
2. The function $f$ is continuously differentiable of order $1$ over $\mathbb R$, i.e. $f$ is $C^1$. This is the regularity condition used so that the gradient $\nabla f$ is available.
3. For every pair of points $x,y \in H$, the inner product of the gradient difference $\nabla f(x)-\nabla f(y)$ with the displacement $x-y$ is at least $M$ times the squared distance $`\|x-y\|^2`$. Equivalently,

```math
\bigl\langle \nabla f(x)-\nabla f(y),\,x-y\bigr\rangle_{\mathbb R}
\ge M\|x-y\|^2 .
```

In ordinary language, the declaration says that $f$ is $M$-strongly convex when $M$ is positive, $f$ is once continuously differentiable, and its gradient is $M$-strongly monotone: the gradient difference against the displacement is bounded below by $M$ times the squared displacement. This is the gradient-monotonicity form associated with strong convexity; the definition itself simply names this conjunction and does not assert any equivalence to another formulation.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `def`, so its content is exhausted by the definitional equation above. Consequently there are no proof steps to analyze: no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, and no named local theorem or lemma is invoked.

Mathematically, to use or establish $\mathrm{IsStronglyConvex}(f,M)$, one unfolds the definition and obtains exactly the conjunction

```math
M>0 \;\wedge\; \mathrm{ContDiff}_{\mathbb R}^{1}(f)
\;\wedge\;
\forall x,y,\
\bigl\langle \nabla f(x)-\nabla f(y),\,x-y\bigr\rangle_{\mathbb R}
\ge M\,\|x-y\|^2 .
```

No further hypothesis is supplied, and no additional conclusion is drawn beyond this definitional content.

