## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/ext_thm_1.lean`

## Lean statement
```lean
recall ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential
```

## Statement explanation
The recalled declaration is `ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential`. In the provided Lean source there is no full type for this declaration: the source contains only the command `recall ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential`, not the statement of the theorem and not its hypotheses. Therefore the exact domain, scalar field, convexity or closedness assumptions, and any step-size parameter cannot be read off from the supplied text.

What is determined by the identifier is the mathematical equivalence it names. The name says that, for an extended-real-valued function $f$, equality with the proximity operator is equivalent to membership of a difference in the subdifferential. In the usual convex-analysis formulation, this is the statement

$$
p = \operatorname{prox}_f(x)
\quad\Longleftrightarrow\quad
x-p \in \partial f(p),
$$

up to any scaling or indexing convention that may be hidden in the full Lean type. Here $\operatorname{prox}_f(x)$ is the point minimizing the prox objective

$$
y \mapsto f(y)+\frac{1}{2}\lVert y-x\rVert^2,
$$

and $\partial f(p)$ is the subdifferential of $f$ at $p$. The content of the theorem is the first-order optimality condition for that minimization problem: $p$ minimizes $f(y)+\frac{1}{2}\lVert y-x\rVert^2$ exactly when $0$ belongs to the subdifferential of the objective at $p$, which is equivalent to

$$
0 \in \partial f(p)+p-x,
$$

or equivalently

$$
x-p \in \partial f(p).
$$

Since the theorem is an “if and only if” result, it gives both directions: if $p$ is the proximity point of $x$, then the residual $x-p$ lies in the subdifferential of $f$ at $p$; and conversely, if $x-p$ lies in that subdifferential, then $p$ is the proximity point of $x$, under whatever regularity assumptions are present in the hidden full statement.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The Lean source contains only the `recall` command

`recall ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential`

and the comment `-- No separate proof part.` No tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur. No local hypotheses are introduced, no goal is transformed, and no previously established result is applied step by step. The `recall` command does not prove the equivalence; it simply makes the already existing declaration available by name.

Consequently, the mathematical content to be explained is exactly the content of the recalled theorem described above: the equivalence between $p=\operatorname{prox}_f(x)$ and $x-p\in\partial f(p)$. Because the supplied source does not include the theorem’s full type, no further proof-level verification of its hypotheses or of the subdifferential characterization can be given from the provided code.

