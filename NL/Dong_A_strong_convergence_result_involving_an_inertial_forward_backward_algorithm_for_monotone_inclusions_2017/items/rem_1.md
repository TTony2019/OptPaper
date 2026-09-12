## Source file
`Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017/items/rem_1.lean`

## Lean statement
```lean
theorem q_constraint_iff_halfspace (x0 x u : H) :
    inner ℝ (u - x) (x0 - x) ≤ 0 ↔ inner ℝ u (x0 - x) ≤ inner ℝ x (x0 - x)
```

## Statement explanation
The declaration is a theorem named `q_constraint_iff_halfspace`. It is stated in an ambient real inner product space \(H\) and takes three vectors \(x_0,x,u\in H\). Writing the real inner product as \(\langle\cdot,\cdot\rangle_{\mathbb R}\), the theorem asserts the equivalence
\[
\langle u-x,\ x_0-x\rangle_{\mathbb R}\le 0
\quad\Longleftrightarrow\quad
\langle u,\ x_0-x\rangle_{\mathbb R}\le \langle x,\ x_0-x\rangle_{\mathbb R}.
\]
The left-hand condition says that the displacement \(u-x\) has nonpositive inner product with the fixed direction \(x_0-x\). The right-hand condition says that the scalar projection of \(u\) in the direction \(x_0-x\) is no larger than that of \(x\). Thus the declaration identifies the “\(q\)-constraint” form of the inequality with the equivalent closed-halfspace membership form: \(u\) lies in the halfspace through \(x\) whose normal vector is \(x_0-x\).

## Lean proof
```lean
by
  rw [inner_sub_left]
  constructor <;> intro h <;> linarith
```

## Proof explanation
The proof begins with `rw [inner_sub_left]`. The lemma `inner_sub_left` expresses linearity of the inner product in its first argument under subtraction: for real inner products,
\[
\langle u-x,\ y\rangle_{\mathbb R}
=
\langle u,\ y\rangle_{\mathbb R}
-
\langle x,\ y\rangle_{\mathbb R}.
\]
Applying it with \(y=x_0-x\) rewrites the left side of the equivalence. The goal becomes
\[
\langle u,\ x_0-x\rangle_{\mathbb R}
-
\langle x,\ x_0-x\rangle_{\mathbb R}
\le 0
\quad\Longleftrightarrow\quad
\langle u,\ x_0-x\rangle_{\mathbb R}
\le
\langle x,\ x_0-x\rangle_{\mathbb R}.
\]

The tactic `constructor` splits an iff-goal into its two implication directions. In the first direction, `intro h` assumes
\[
\langle u,\ x_0-x\rangle_{\mathbb R}
-
\langle x,\ x_0-x\rangle_{\mathbb R}
\le 0,
\]
and the goal is to prove
\[
\langle u,\ x_0-x\rangle_{\mathbb R}
\le
\langle x,\ x_0-x\rangle_{\mathbb R}.
\]
The tactic `linarith` treats the two inner-product expressions as real variables and derives this by ordinary linear arithmetic: if \(a-b\le 0\), then \(a\le b\).

In the second direction, `intro h` assumes
\[
\langle u,\ x_0-x\rangle_{\mathbb R}
\le
\langle x,\ x_0-x\rangle_{\mathbb R},
\]
and the goal is to prove
\[
\langle u,\ x_0-x\rangle_{\mathbb R}
-
\langle x,\ x_0-x\rangle_{\mathbb R}
\le 0.
\]
Again `linarith` closes the goal, since from \(a\le b\) it follows that \(a-b\le 0\). The symbol `<;>` applies the same subsequent tactic sequence to both generated goals. No symmetry, positive-definiteness, or norm estimate is used; the argument uses only first-variable linearity of the inner product and linear arithmetic in the real numbers.

