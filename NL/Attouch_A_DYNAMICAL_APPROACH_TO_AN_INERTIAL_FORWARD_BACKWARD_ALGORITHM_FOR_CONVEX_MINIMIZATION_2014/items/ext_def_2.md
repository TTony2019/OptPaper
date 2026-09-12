## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/ext_def_2.lean`

## Lean statement
```lean
recall ERealFunction.subdifferential
```

## Statement explanation
The source declaration is a `recall` of the existing Mathlib notion `ERealFunction.subdifferential`. It does not introduce a theorem with its own variables, hypotheses, or conclusion; rather, it records that the formal development will use the already-defined subdifferential for extended-real-valued functions.

Mathematically, the recalled definition applies to a real normed vector space $E$, an extended-real-valued function

$$
f : E \to \overline{\mathbb R},
$$

where $\overline{\mathbb R} = \mathbb R \cup \{-\infty,+\infty\}$, and a point $x \in E$. The subdifferential $\partial f(x)$ is defined as the set of continuous linear functionals $p : E \to \mathbb R$, equivalently elements $p \in E^*$, such that for every $y \in E$,

$$
f(x) + p(y-x) \le f(y).
$$

Here $p(y-x)$ is the real number obtained by applying the continuous linear functional $p$ to the vector $y-x$, and the sum is taken in the extended real numbers $\overline{\mathbb R}$. Thus $p \in \partial f(x)$ exactly when the affine function

$$
y \mapsto f(x) + p(y-x)
$$

lies below $f$ everywhere on $E$ and agrees with $f$ at $y=x$. Such a functional $p$ is called a subgradient of $f$ at $x$, and the set of all such subgradients is the subdifferential.

In convex analysis, this is the extended-real version of the set of supporting slopes of $f$ at $x$. If $f(x)=+\infty$, the inequality forces $f(y)=+\infty$ for every $y$; if $f(x)=-\infty$, the inequality is automatically satisfied. In the usual applications, $f$ is proper, so these degenerate cases do not occur at points of interest.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The Lean source contains only the recall of `ERealFunction.subdifferential`, and the proof field says explicitly that there is no separate proof. Therefore no tactics are executed, no goals are transformed, and no named lemmas or theorems are invoked. There are no steps involving `intro`, `rw`, `simp`, `exact`, or `linarith` to explain. The mathematical content of the declaration is exactly the recalled definition of the subdifferential described above, not a new assertion to be proved.

