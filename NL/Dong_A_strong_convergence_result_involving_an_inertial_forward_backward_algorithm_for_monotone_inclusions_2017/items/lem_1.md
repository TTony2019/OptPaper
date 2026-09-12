## Source file
`Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017/items/lem_1.lean`

## Lean statement
```lean
theorem metric_projection_pythagorean {C : Set H} (hC : C.Nonempty) (hClosed : IsClosed C)
    (hConvex : Convex ℝ C) (x : H) (y : H) (hy : y ∈ C) :
    ‖y - projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC hClosed hConvex) x‖ ^ 2 +
      ‖x - projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC hClosed hConvex) x‖ ^ 2 ≤
        ‖x - y‖ ^ 2
```

## Statement explanation
The declaration `metric_projection_pythagorean` is stated in an ambient real Hilbert space $H$. It concerns a subset $C\subseteq H$ that is assumed nonempty, closed, and convex over $\mathbb R$. It also fixes two points $x\in H$ and $y\in H$, with the hypothesis $y\in C$. The expression

$$
\mathrm{proj}_C(x)
$$

denotes the metric projection of $x$ onto $C$, implemented by `projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC hClosed hConvex) x`. The auxiliary theorem `isChebyshev_of_nonempty_isClosed_convex` is what makes this projection well-defined: a nonempty closed convex subset of a real Hilbert space is Chebyshev, meaning every point of the Hilbert space has a unique nearest point in the set. Thus the chosen projection point belongs to $C$ and is the nearest point of $C$ to $x$.

The conclusion is the Pythagorean inequality for this metric projection:

$$
\|y-p\|^2+\|x-p\|^2\le \|x-y\|^2,
$$

where $p=\mathrm{proj}_C(x)$. In words, if $p$ is the nearest point of $C$ to $x$, then for every $y\in C$, the squared distance from $y$ to $p$ plus the squared distance from $x$ to $p$ is at most the squared distance from $x$ to $y$. This is the usual obtuse-angle or Pythagorean inequality for projection onto a closed convex set: the vector $x-p$ has nonpositive inner product with every vector $y-p$ with $y\in C$, so the angle at $p$ between $x-p$ and $y-p$ is at least a right angle. The law of cosines then gives the displayed inequality.

## Lean proof
```lean
by
  let p : H := projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC hClosed hConvex) x
  have hp_char : p ∈ C ∧ ∀ z ∈ C, ⟪z - p, x - p⟫_ℝ ≤ 0 := by
    simpa [p] using
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC hClosed hConvex).mp rfl
  have hinner : ⟪x - p, y - p⟫_ℝ ≤ 0 := by
    simpa [real_inner_comm] using hp_char.2 y hy
  have hvec : (x - p) - (y - p) = x - y := by
    abel_nf
  have hsq : ‖x - y‖ ^ 2 =
      ‖x - p‖ ^ 2 - 2 * ⟪x - p, y - p⟫_ℝ + ‖y - p‖ ^ 2 := by
    calc
      ‖x - y‖ ^ 2 = ‖(x - p) - (y - p)‖ ^ 2 := by
        rw [hvec]
      _ = ‖x - p‖ ^ 2 - 2 * ⟪x - p, y - p⟫_ℝ + ‖y - p‖ ^ 2 :=
        norm_sub_sq_real (x - p) (y - p)
  simpa only [p] using (show ‖y - p‖ ^ 2 + ‖x - p‖ ^ 2 ≤ ‖x - y‖ ^ 2 by
    nlinarith [hsq, hinner])
```

## Proof explanation
The proof begins by introducing a local abbreviation $p$ for the projection point:

$$
p=\mathrm{proj}_C(x).
$$

This is done with `let p : H := ...`. There is no use of `intro` here because the hypotheses $hC, hClosed, hConvex, x, y, hy$ are already parameters of the theorem. The proof then proceeds by establishing intermediate facts.

First, it proves `hp_char`, which states

$$
p\in C \quad\text{and}\quad \forall z\in C,\ \langle z-p,x-p\rangle_{\mathbb R}\le 0.
$$

This is obtained from the theorem `eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex`. That theorem, specialized to the same nonempty closed convex set $C$, says

$$
p = \mathrm{proj}_C(x)
\iff
p\in C \land \forall z\in C,\ \langle z-p,x-p\rangle_{\mathbb R}\le 0.
$$

Since $p$ was defined to be exactly the projection point, the left-hand equality is true by reflexivity, so the forward implication `.mp rfl` gives the right-hand side. The `simpa [p]` command unfolds the local definition of $p$ so that the result matches `hp_char`. Mathematically, this is the first-order optimality condition for the nearest point: moving from $p$ toward any other point $z\in C$ cannot make the distance to $x$ smaller, which is equivalent to the displayed inner product being nonpositive.

Second, the proof specializes the universal statement in `hp_char` to $z=y$. Since $hy:y\in C$, the application `hp_char.2 y hy` gives

$$
\langle y-p,x-p\rangle_{\mathbb R}\le 0.
$$

The real inner product is symmetric, so `real_inner_comm` rewrites this as

$$
\langle x-p,y-p\rangle_{\mathbb R}\le 0.
$$

This fact is named `hinner`. Geometrically, it says that the residual vector $x-p$ makes a nonpositive inner product with the vector $y-p$ pointing from the projection point to an arbitrary point of $C$.

Third, the proof records the algebraic identity

$$
(x-p)-(y-p)=x-y.
$$

This is `hvec`, proved by `abel_nf`, which normalizes addition and subtraction in an additive commutative group. This identity is used to replace $x-y$ by $(x-p)-(y-p)$ in the following squared-norm calculation.

Fourth, the proof establishes `hsq`, the law of cosines:

$$
\|x-y\|^2
=\|x-p\|^2-2\langle x-p,y-p\rangle_{\mathbb R}+\|y-p\|^2.
$$

The `calc` block first uses `rw [hvec]` to rewrite

$$
\|x-y\|^2
$$

as

$$
\|(x-p)-(y-p)\|^2.
$$

Then it applies `norm_sub_sq_real` to the vectors $u=x-p$ and $v=y-p$. That lemma states that in a real inner product space,

$$
\|u-v\|^2
=\|u\|^2-2\langle u,v\rangle_{\mathbb R}+\|v\|^2.
$$

Specializing to $u=x-p$ and $v=y-p$ gives exactly the displayed identity for $\|x-y\|^2$.

Finally, the proof proves the desired inequality in terms of the local abbreviation $p$ and then unfolds $p$. The temporary `show` changes the goal to

$$
\|y-p\|^2+\|x-p\|^2\le \|x-y\|^2.
$$

From `hsq` and `hinner`, we have

$$
\|x-y\|^2
=\|x-p\|^2+\|y-p\|^2-2\langle x-p,y-p\rangle_{\mathbb R}.
$$

Since $\langle x-p,y-p\rangle_{\mathbb R}\le 0$, the term $-2\langle x-p,y-p\rangle_{\mathbb R}$ is nonnegative. Therefore

$$
\|x-y\|^2
\ge
\|x-p\|^2+\|y-p\|^2,
$$

which is the desired inequality after commuting the two summands. The tactic `nlinarith` performs this arithmetic deduction from the equality `hsq` and the inequality `hinner`. The final `simpa only [p]` unfolds the local abbreviation $p$ back to the original projection point expression, so the proved inequality becomes precisely the conclusion stated in the theorem.

