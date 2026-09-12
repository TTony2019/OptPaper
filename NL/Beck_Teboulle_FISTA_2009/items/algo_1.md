## Source file
`Beck_Teboulle_FISTA_2009/items/algo_1.lean`

## Lean statement
```lean
theorem proximal_step_at {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ} {Lf : ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTAConstantStepsize f g Lf x0)
    (k : ℕ) : IsProxPoint f g Lf (A.y (k + 1)) (A.x (k + 1))
```

## Statement explanation
The theorem `proximal_step_at` is an accessor/export result for a FISTA constant-step-size iteration. Its parameters are a natural number $n$, the dimension; two real-valued functions

$$
f,g:\mathbb R^n\to \mathbb R,
$$

where $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)` in Lean; a real parameter $L_f$, corresponding to the Lean name `Lf`; an initial point $x_0\in\mathbb R^n$; and a bundled object $A$ of type `FISTAConstantStepsize f g Lf x0`. The object $A$ represents a FISTA iteration scheme for the data $f,g,L_f,x_0$. It supplies, among other components, the iterate families `A.x` and `A.y`, both taking natural indices to points of $\mathbb R^n$, and a stored proximal-step property named `A.proximal_step`. The final explicit parameter is a natural number $k$, an index.

The conclusion is

$$
\operatorname{IsProxPoint} f g L_f \bigl(A.y(k+1)\bigr) \bigl(A.x(k+1)\bigr).
$$

Writing $y_{k+1}$ for the value of the `A.y` iterate at $k+1$, and $x_{k+1}$ for the value of the `A.x` iterate at $k+1$, the theorem says that the pair consisting of $y_{k+1}$ and $x_{k+1}$ satisfies the predicate `IsProxPoint` for the functions $f,g$ and the parameter $L_f$. In FISTA terminology, this is the assertion that the iterate $x_{k+1}$ is a proximal point associated to the current auxiliary point $y_{k+1}$. The declaration does not expand the exact formula defining `IsProxPoint`; it only records that this proximal-point relation holds at the shifted index $k+1$. Thus the theorem states that the proximal-step relation is available for every positive time $k+1$, not merely for some specially chosen index.

## Lean proof
```lean
by
  exact A.proximal_step (k + 1) (by omega)
```

## Proof explanation
The proof is a single `exact` term:
`exact A.proximal_step (k + 1) (by omega)`.
No `intro` is needed, because the parameters $f,g,L_f,x_0,A,k$ are already in the local context from the theorem statement. The proof does not use rewriting, simplification, or a separate algebraic step; it directly provides a term of the required type.

The term `A.proximal_step` is the component of the structure `FISTAConstantStepsize` that stores the proximal-step property of the FISTA scheme. From its invocation here, it is a function that takes an index and a proof of the arithmetic side condition required for that index, and returns the corresponding proximal-point assertion. The proof specializes it to the index $k+1$. The second argument, `(by omega)`, is a proof of that side condition. The tactic `omega` is a decision procedure for linear arithmetic over natural numbers and integers. Since $k$ is a natural number, it can prove the elementary arithmetic fact needed for $k+1$, namely that the successor index $k+1$ is positive, equivalently nonzero. This matters because the FISTA iteration records its proximal-step property for positive times; shifting an arbitrary natural number $k$ to $k+1$ places the index in the range where the property applies.

After those arguments are supplied, `A.proximal_step (k+1) (by omega)` has exactly the type

$$
\operatorname{IsProxPoint} f g L_f \bigl(A.y(k+1)\bigr) \bigl(A.x(k+1)\bigr),
$$

which is the goal. The `exact` tactic therefore closes the theorem immediately. There are no further mathematical transformations in the proof: the only subsidiary reasoning is the `omega` arithmetic proof that the index $k+1$ satisfies the side condition required by `A.proximal_step`.

