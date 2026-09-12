## Source file
`Nesterov_Accelerated_gradient_1983/items/algo_1.lean`

## Lean statement
```lean
structure AcceleratedGradientMethod {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) where
  y : ℕ → E
  x : ℕ → E
  step : ℕ → ℝ
  weight : ℕ → ℝ
  y0 : E
  y_zero : y 0 = y0
  x_neg_one : E
  initialStep : ℝ
  z : E
  z_ne_y0 : z ≠ y0
  gradient_z_ne_gradient_y0 : gradient f z ≠ gradient f y0
  x_neg_one_eq_y0 : x_neg_one = y0
  initialStep_eq : initialStep = ‖y0 - z‖ / ‖gradient f y0 - gradient f z‖
  weight_zero : weight 0 = 1
  searchIndex : ℕ → ℕ
  step_eq_dyadic_previous : ∀ k, step k = (2 : ℝ) ^ (-(searchIndex k : ℤ)) *
    if k = 0 then initialStep else step (k - 1)
  accepted : ∀ k, (step k / 2) * ‖gradient f (y k)‖ ^ 2 ≤ f (y k) - f (x k)
  minimal_searchIndex : ∀ k j, j < searchIndex k →
    f (y k) - f (y k - ((2 : ℝ) ^ (-(j : ℤ)) *
      (if k = 0 then initialStep else step (k - 1))) • gradient f (y k)) <
      ((2 : ℝ) ^ (-(j : ℤ)) * (if k = 0 then initialStep else step (k - 1))) / 2 *
        ‖gradient f (y k)‖ ^ 2
  update_x : ∀ k, x k = y k - step k • gradient f (y k)
  update_weight : ∀ k, weight (k + 1) = (1 + Real.sqrt (4 * weight k ^ 2 + 1)) / 2
  update_y : ∀ k, y (k + 1) = x k + ((weight k - 1) / weight (k + 1)) •
    (x k - if k = 0 then x_neg_one else x (k - 1))
```

## Statement explanation
The declaration defines a structure (a record type) named `AcceleratedGradientMethod`. It is parameterized by a type $E$ and a function $f:E\to\mathbb{R}$. The typeclass assumptions on $E$ say that it is a normed additive commutative group, a real inner product space, and complete; thus $E$ is a complete real inner product space, i.e. a real Hilbert space. The function $f$ is the real-valued objective. Write $y_k=y(k)$, $x_k=x(k)$, $t_k=step(k)$, $w_k=weight(k)$, $y_{\mathrm{init}}=y0$, $t_{\mathrm{init}}=initialStep$, and $s_k=searchIndex(k)$. Write $x_{-1}$ for the field `x_neg_one`, and write $\nabla f(p)$ for `gradient f p`.

The fields of the structure are the following data and conditions.

- `y` and `x` are sequences $k\mapsto y_k$ and $k\mapsto x_k$ in $E$, indexed by $\mathbb{N}$.
- `step` is a real-valued sequence $k\mapsto t_k$, and `weight` is a real-valued sequence $k\mapsto w_k$.
- `y0` is an initial point $y_{\mathrm{init}}$, and `y_zero` states $y_0=y_{\mathrm{init}}$.
- `x_neg_one` is an auxiliary previous iterate $x_{-1}$, and `x_neg_one_eq_y0` states $x_{-1}=y_{\mathrm{init}}$.
- `initialStep` is a real number $t_{\mathrm{init}}$, and `initialStep_eq` states

$$
t_{\mathrm{init}}
=\frac{\lVert y_{\mathrm{init}}-z\rVert}
{\lVert \nabla f(y_{\mathrm{init}})-\nabla f(z)\rVert}.
$$

- `z` is an auxiliary point, with `z_ne_y0` stating $z\ne y_{\mathrm{init}}$, and `gradient_z_ne_gradient_y0` stating

$$
\nabla f(z)\ne \nabla f(y_{\mathrm{init}}).
$$

The latter condition makes the denominator in the formula for $t_{\mathrm{init}}$ nonzero.
- `weight_zero` states $w_0=1$.
- `searchIndex` is a sequence $k\mapsto s_k$ of natural numbers. For each $k$, define the base trial step

```math
B_k=
\begin{cases}
t_{\mathrm{init}}, & k=0,\\
t_{k-1}, & k>0.
\end{cases}
```

The field `step_eq_dyadic_previous` states that for every $k$,

$$
t_k=2^{-s_k}B_k.
$$

Equivalently, $t_0=2^{-s_0}t_{\mathrm{init}}$, and for $k\gt 0$, $t_k=2^{-s_k}t_{k-1}$.
- `accepted` states that for every $k$,

$$
\frac{t_k}{2}\lVert \nabla f(y_k)\rVert^2
\le
f(y_k)-f(x_k).
$$

- `minimal_searchIndex` states that for every $k$ and every natural number $j\lt s_k$,

```math
f(y_k)-f\!\left(y_k-2^{-j}B_k\,\nabla f(y_k)\right)
<
\frac{2^{-j}B_k}{2}\lVert \nabla f(y_k)\rVert^2.
```

Thus every smaller index $j$ fails the strict form of the acceptance condition, so $s_k$ is the first index for which the dyadic step $2^{-s_k}B_k$ satisfies the required decrease inequality.
- `update_x` states that for every $k$,

```math
x_k=y_k-t_k\,\nabla f(y_k).
```

So $x_k$ is the gradient step from $y_k$ with step size $t_k$.
- `update_weight` states that for every $k$,

$$
w_{k+1}=\frac{1+\sqrt{4w_k^2+1}}{2}.
$$

- `update_y` states that for every $k$,

```math
y_{k+1}
=x_k+\frac{w_k-1}{w_{k+1}}
\left(
x_k-
\begin{cases}
x_{-1}, & k=0,\\
x_{k-1}, & k>0
\end{cases}
\right).
```

Since $x_{-1}=y_{\mathrm{init}}$ and $w_0=1$, the case $k=0$ gives $y_1=x_0$. For $k\gt 0$, this is the momentum or extrapolation step using the previous displacement $x_k-x_{k-1}$.

In summary, the structure specifies data for a Nesterov-style accelerated gradient method with a dyadic backtracking line search. The line search chooses the smallest index $s_k$ such that the step $t_k=2^{-s_k}B_k$ satisfies a sufficient-decrease inequality, while all smaller indices fail strictly. The $x$-update is the corresponding gradient step, and the $y$-update is the extrapolation step using the weight recurrence. The initial step $t_{\mathrm{init}}$ is determined by the ratio of the separation of $y_{\mathrm{init}}$ and $z$ to the separation of their gradients. The declaration does not assert that such data exist or that the method converges; it packages the data and conditions that an inhabitant of the structure must satisfy.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `structure`, so its fields are the data and conditions that a record inhabiting the structure must provide; they are not derived by a proof in this source. Consequently there are no proof steps, no tactic commands such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no named theorems or lemmas invoked. The mathematical content is exactly the field-by-field specification explained in the first section. To construct an inhabitant, one would have to supply the sequences $x$ and $y$, the step and weight functions, the points $y_{\mathrm{init}}$, $z$, and $x_{-1}$, the numbers $t_{\mathrm{init}}$, the search indices $s_k$, and proofs of all the listed equalities, inequalities, and recurrences; the declaration itself does not provide such a construction.

