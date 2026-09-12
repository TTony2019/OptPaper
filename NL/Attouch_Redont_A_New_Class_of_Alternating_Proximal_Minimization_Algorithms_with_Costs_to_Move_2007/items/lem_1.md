## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/lem_1.lean`

## Lean statement
```lean
theorem lemma_2_3 {X Y : Type*} {f : X → ℝ} {g : Y → ℝ}
    {h : X → X → ℝ} {k : Y → Y → ℝ} {c : X → Y → ℝ}
    {α β μ ν : ℕ → ℝ} (alg : CA2 X Y f g h k c α β μ ν)
    (hyp : H21toH24 X Y f g h k c α β μ ν) (n : ℕ) :
    μ n * f (alg.x (n+1)) + β n * g (alg.y (n+1)) + β n * μ n * c (alg.x (n+1)) (alg.y (n+1)) +
    μ n * α n * h (alg.x n) (alg.x (n+1)) + β n * ν n * k (alg.y n) (alg.y (n+1)) ≤
    μ n * f (alg.x n) + β n * g (alg.y n) + β n * μ n * c (alg.x n) (alg.y n)
```

## Statement explanation
The theorem `lemma_2_3` is a weighted descent inequality for an alternating proximal-type algorithm. The data are two arbitrary types $X$ and $Y$, real-valued functions

$$
f:X\to\mathbb R,\qquad g:Y\to\mathbb R,\qquad h:X\times X\to\mathbb R,\qquad k:Y\times Y\to\mathbb R,\qquad c:X\times Y\to\mathbb R,
$$

and four real sequences

$$
\alpha,\beta,\mu,\nu:\mathbb N\to\mathbb R.
$$

The hypothesis `alg` is an object of type `CA2 X Y f g h k c α β μ ν`; from the proof it supplies the algorithm’s iterates, written

$$
x_n=\operatorname{alg}.x\,n,\qquad y_n=\operatorname{alg}.y\,n,
$$

as well as the two one-step inequalities for the $x$- and $y$-updates. The hypothesis `hyp` is an object of type `H21toH24 X Y f g h k c α β μ ν`; the proof uses from it the diagonal vanishings $h(x_n,x_n)=0$ and $k(y_n,y_n)=0$, together with the positivity information that yields $0\le \mu_n$ and $0\le \beta_n$.

For each $n\in\mathbb N$, the theorem concludes

$$
\begin{aligned}
&\mu_n f(x_{n+1})+\beta_n g(y_{n+1})+\beta_n\mu_n c(x_{n+1},y_{n+1})\\
&\quad+\mu_n\alpha_n h(x_n,x_{n+1})+\beta_n\nu_n k(y_n,y_{n+1})\\
&\le
\mu_n f(x_n)+\beta_n g(y_n)+\beta_n\mu_n c(x_n,y_n).
\end{aligned}
$$

In ordinary language, the weighted value of the objective plus the weighted costs to move from $x_n$ to $x_{n+1}$ and from $y_n$ to $y_{n+1}$ after the update is bounded above by the weighted value at the previous pair. The coupling term involving $c(x_{n+1},y_n)$ does not appear in the final inequality because it is introduced on both sides of the two combined step inequalities and cancels.

## Lean proof
```lean
by
  -- Instantiate CA² inequalities with ξ = x_n and η = y_n
  have hx := alg.step_x n (alg.x n)
  have hy := alg.step_y n (alg.y n)
  -- Simplify using h(x_n, x_n) = 0 and k(y_n, y_n) = 0
  have hx' : f (alg.x (n+1)) + α n * h (alg.x n) (alg.x (n+1)) + β n * c (alg.x (n+1)) (alg.y n) ≤
      f (alg.x n) + β n * c (alg.x n) (alg.y n) := by
    simpa [hyp.h_diag_zero (alg.x n)] using hx
  have hy' : g (alg.y (n+1)) + μ n * c (alg.x (n+1)) (alg.y (n+1)) + ν n * k (alg.y n) (alg.y (n+1)) ≤
      g (alg.y n) + μ n * c (alg.x (n+1)) (alg.y n) := by
    simpa [hyp.k_diag_zero (alg.y n)] using hy
  -- Multiply by nonnegative coefficients μ_n > 0, β_n > 0
  have hpos_mu : 0 ≤ μ n := by linarith [hyp.mu_pos n]
  have hpos_beta : 0 ≤ β n := by linarith [hyp.beta_pos n]
  have hx_mul := mul_le_mul_of_nonneg_left hx' hpos_mu
  have hy_mul := mul_le_mul_of_nonneg_left hy' hpos_beta
  -- Add the two inequalities and cancel the common cross-term μ_n β_n c(x_{n+1}, y_n)
  have h_add := add_le_add hx_mul hy_mul
  nlinarith
```

## Proof explanation
The proof has no `intro` step, because the variables and hypotheses of the theorem are already present in the tactic context.

First, the command `have hx := alg.step_x n (alg.x n)` instantiates the $x$-step inequality stored in `alg` at iteration $n$, comparing with the point $x_n$. The next command `simpa [hyp.h_diag_zero (alg.x n)] using hx` rewrites the diagonal value $h(x_n,x_n)$ to $0$ and simplifies the resulting arithmetic. This produces the intermediate inequality

$$
f(x_{n+1})+\alpha_n h(x_n,x_{n+1})+\beta_n c(x_{n+1},y_n)
\le f(x_n)+\beta_n c(x_n,y_n).
$$

It says that the new $f$-value plus the weighted $x$-move cost plus the coupling to the old $y_n$ is at most the old $f$-value plus the old coupling.

Similarly, `have hy := alg.step_y n (alg.y n)` instantiates the $y$-step inequality at iteration $n$, using $y_n$. After `simpa [hyp.k_diag_zero (alg.y n)] using hy`, the diagonal term $k(y_n,y_n)$ is removed, giving

$$
g(y_{n+1})+\mu_n c(x_{n+1},y_{n+1})+\nu_n k(y_n,y_{n+1})
\le g(y_n)+\mu_n c(x_{n+1},y_n).
$$

This says that the new $g$-value plus the weighted coupling to the new $x_{n+1}$ plus the weighted $y$-move cost is at most the old $g$-value plus the coupling evaluated at $(x_{n+1},y_n)$.

Next, `have hpos_mu : 0 ≤ μ n := by linarith [hyp.mu_pos n]` uses the positivity hypothesis for $\mu_n$ supplied by `hyp` and `linarith` to obtain the non-strict bound $0\le \mu_n$. Here `linarith` is linear arithmetic over the real numbers. The analogous command for $\beta_n$ gives $0\le \beta_n$. These nonnegativity facts are needed so that multiplying an inequality by $\mu_n$ or $\beta_n$ does not reverse it.

The command `mul_le_mul_of_nonneg_left hx' hpos_mu` applies the monotonicity rule for multiplication by a nonnegative real number: from $A\le B$ and $0\le \mu_n$, it concludes $\mu_n A\le \mu_n B$. With $A$ and $B$ being the two sides of the $x$-step inequality, this gives

$$
\mu_n\bigl(f(x_{n+1})+\alpha_n h(x_n,x_{n+1})+\beta_n c(x_{n+1},y_n)\bigr)
\le
\mu_n\bigl(f(x_n)+\beta_n c(x_n,y_n)\bigr).
$$

Likewise, `mul_le_mul_of_nonneg_left hy' hpos_beta` gives

$$
\beta_n\bigl(g(y_{n+1})+\mu_n c(x_{n+1},y_{n+1})+\nu_n k(y_n,y_{n+1})\bigr)
\le
\beta_n\bigl(g(y_n)+\mu_n c(x_{n+1},y_n)\bigr).
$$

The command `add_le_add hx_mul hy_mul` then adds these two inequalities term by term. It yields

$$
\begin{aligned}
&\mu_n f(x_{n+1})+\mu_n\alpha_n h(x_n,x_{n+1})+\mu_n\beta_n c(x_{n+1},y_n)\\
&\quad+\beta_n g(y_{n+1})+\beta_n\mu_n c(x_{n+1},y_{n+1})+\beta_n\nu_n k(y_n,y_{n+1})\\
&\le
\mu_n f(x_n)+\mu_n\beta_n c(x_n,y_n)
+\beta_n g(y_n)+\beta_n\mu_n c(x_{n+1},y_n).
\end{aligned}
$$

Finally, `nlinarith` proves the goal from this combined inequality. It treats expressions such as $f(x_{n+1})$, $c(x_{n+1},y_n)$, and so on as real variables and performs polynomial arithmetic. In particular, the term $\mu_n\beta_n c(x_{n+1},y_n)$ on the left and the term $\beta_n\mu_n c(x_{n+1},y_n)$ on the right are equal by commutativity of multiplication, so they cancel. After this cancellation and rearrangement, the combined inequality becomes exactly

$$
\begin{aligned}
&\mu_n f(x_{n+1})+\beta_n g(y_{n+1})+\beta_n\mu_n c(x_{n+1},y_{n+1})\\
&\quad+\mu_n\alpha_n h(x_n,x_{n+1})+\beta_n\nu_n k(y_n,y_{n+1})\\
&\le
\mu_n f(x_n)+\beta_n g(y_n)+\beta_n\mu_n c(x_n,y_n),
\end{aligned}
$$

which is the theorem’s conclusion.

