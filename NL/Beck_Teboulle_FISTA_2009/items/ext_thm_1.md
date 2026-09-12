## Source file
`Beck_Teboulle_FISTA_2009/items/ext_thm_1.lean`

## Lean statement
```lean
theorem descent_lemma_C11 {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {Lf L : ℝ}
    (hf : IsC11 f Lf) (hL : Lf ≤ L) (x y : EuclideanSpace ℝ (Fin n)) :
    f x ≤ f y + ⟪gradient f y, x - y⟫ + (L / 2) * ‖x - y‖ ^ 2
```

## Statement explanation
The declaration `descent_lemma_C11` states the following. Let $n$ be a natural number, let

$$
f:\mathbb R^n\to\mathbb R
$$

be a real-valued function on the Euclidean space $\mathbb R^n$ (written in Lean as `EuclideanSpace ℝ (Fin n)`), and let $Lf$ and $L$ be real numbers. Assume the hypothesis $hf$, whose type is the predicate `IsC11 f Lf`. The source does not unfold the definition of `IsC11`; in this declaration it is used as the regularity hypothesis on $f$, with parameter $Lf$, that is required by the cited quadratic upper bound. Assume also $hL : Lf \le L$, meaning that the real number $L$ is at least the constant $Lf$. Finally, let $x$ and $y$ be two points of $\mathbb R^n$.

The conclusion is the inequality

$$
f(x)\le f(y)+\langle \nabla f(y),x-y\rangle+\frac{L}{2}\lVert x-y\rVert^2 .
$$

Here $\nabla f(y)$ is the gradient of $f$ at $y$, the bracket $\langle \cdot,\cdot\rangle$ is the Euclidean inner product, and $\lVert\cdot\rVert$ is the Euclidean norm. Thus the theorem gives a quadratic upper bound for $f(x)$ in terms of the first-order Taylor expansion of $f$ around $y$, plus a quadratic error term controlled by $L/2$. It is a form of the descent lemma: if the regularity constant $Lf$ is no larger than $L$, then the same quadratic upper bound can be written with the larger constant $L$.

## Lean proof
```lean
quadratic_upper_bound_C11 hf hL x y
```

## Proof explanation
The proof consists of the single term
`quadratic_upper_bound_C11 hf hL x y`.
The cited theorem `quadratic_upper_bound_C11` has exactly the same mathematical content as the target declaration: for every natural number $n$, every function

$$
f:\mathbb R^n\to\mathbb R,
$$

every real number $Lf$, every hypothesis $hf : \texttt{IsC11 } f\, Lf$, every real number $L$ with $Lf\le L$, and every pair of points $x,y\in\mathbb R^n$, it concludes

$$
f(x)\le f(y)+\langle \nabla f(y),x-y\rangle+\frac{L}{2}\lVert x-y\rVert^2 .
$$

The proof applies this previously established theorem to the current variables and hypotheses. Specifically, `hf` supplies the required regularity assumption `IsC11 f Lf`, `hL` supplies the comparison $Lf\le L$, and `x` and `y` supply the two points at which the inequality is asserted. The implicit arguments of `quadratic_upper_bound_C11`, namely $n$, $f$, $Lf$, and $L$, are inferred by Lean from the local context and from the types of `hf`, `hL`, `x`, and `y`.

The result of this application is exactly the displayed inequality, which is also the goal of `descent_lemma_C11`. Therefore the function application is already a complete proof term: in tactic mode the same step would be expressed by
`exact quadratic_upper_bound_C11 hf hL x y`.
No `intro`, `rw`, `simp`, or `linarith` is used, because no variables need to be introduced, no expressions need to be rewritten, and no arithmetic simplification is required. The entire mathematical content of the proof is the direct invocation of the previously proved quadratic upper bound.

