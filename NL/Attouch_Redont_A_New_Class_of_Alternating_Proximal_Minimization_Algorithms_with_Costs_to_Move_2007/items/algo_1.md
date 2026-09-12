## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/algo_1.lean`

## Lean statement
```lean
structure CA2 (X Y : Type*) (f : X → ℝ) (g : Y → ℝ)
    (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (α β μ ν : ℕ → ℝ) where
  /-- The sequence in X. -/
  x : ℕ → X
  /-- The sequence in Y. -/
  y : ℕ → Y
  /-- The x-update inequality from the argmin definition:
      f(x_{n+1}) + α_n h(x_n, x_{n+1}) + β_n c(x_{n+1}, y_n) ≤ f(ξ) + α_n h(x_n, ξ) + β_n c(ξ, y_n)
      for all ξ ∈ X. -/
  step_x (n : ℕ) (ξ : X) :
    f (x (n+1)) + α n * h (x n) (x (n+1)) + β n * c (x (n+1)) (y n) ≤
    f ξ + α n * h (x n) ξ + β n * c ξ (y n)
  /-- The y-update inequality from the argmin definition:
      g(y_{n+1}) + μ_n c(x_{n+1}, y_{n+1}) + ν_n k(y_n, y_{n+1}) ≤ g(η) + μ_n c(x_{n+1}, η) + ν_n k(y_n, η)
      for all η ∈ Y. -/
  step_y (n : ℕ) (η : Y) :
    g (y (n+1)) + μ n * c (x (n+1)) (y (n+1)) + ν n * k (y n) (y (n+1)) ≤
    g η + μ n * c (x (n+1)) η + ν n * k (y n) η
```

## Statement explanation
The Lean declaration `CA2` is not a theorem but a structure, i.e. a record type of data and properties. Its parameters are arbitrary types \(X\) and \(Y\), real-valued functions
\[
f:X\to\mathbb R,\qquad g:Y\to\mathbb R,
\]
two-place real-valued functions
\[
h:X\to X\to\mathbb R,\qquad k:Y\to Y\to\mathbb R,\qquad c:X\to Y\to\mathbb R,
\]
and four real parameter sequences
\[
\alpha,\beta,\mu,\nu:\mathbb N\to\mathbb R.
\]
Thus \(f\) and \(g\) are objective functions on \(X\) and \(Y\), while \(h,k,c\) are real-valued coupling or cost terms, with \(h\) on \(X\times X\), \(k\) on \(Y\times Y\), and \(c\) on \(X\times Y\). No symmetry, convexity, nonnegativity, or other property of these functions or parameters is assumed.

An element of `CA2` consists of a sequence in \(X\),
\[
x:\mathbb N\to X,
\]
a sequence in \(Y\),
\[
y:\mathbb N\to Y,
\]
and two families of inequalities. The field `step_x` states that for every \(n\in\mathbb N\) and every \(\xi\in X\),
\[
f(x_{n+1})+\alpha_n h(x_n,x_{n+1})+\beta_n c(x_{n+1},y_n)
\le
f(\xi)+\alpha_n h(x_n,\xi)+\beta_n c(\xi,y_n).
\]
Equivalently, \(x_{n+1}\) is a minimizer, in the weak sense of this inequality, of the function
\[
\xi\mapsto f(\xi)+\alpha_n h(x_n,\xi)+\beta_n c(\xi,y_n)
\]
over \(X\). The inequality uses the previous point \(x_n\) and the previous point \(y_n\).

The field `step_y` states that for every \(n\in\mathbb N\) and every \(\eta\in Y\),
\[
g(y_{n+1})+\mu_n c(x_{n+1},y_{n+1})+\nu_n k(y_n,y_{n+1})
\le
g(\eta)+\mu_n c(x_{n+1},\eta)+\nu_n k(y_n,\eta).
\]
Equivalently, \(y_{n+1}\) is a minimizer, again in the weak inequality sense, of
\[
\eta\mapsto g(\eta)+\mu_n c(x_{n+1},\eta)+\nu_n k(y_n,\eta)
\]
over \(Y\). This update uses the already updated point \(x_{n+1}\) and the previous point \(y_n\), so the two steps alternate in the order \(x\)-update followed by \(y\)-update.

The declaration therefore packages a discrete trajectory \((x_n,y_n)\) satisfying the two alternating minimization optimality inequalities. It does not assert that such a trajectory exists, nor that the minimizers are unique; it only describes the required inequalities if such a trajectory is given. The indices begin at \(0\) in the natural-number indexing, so the inequalities include the case \(n=0\), producing \(x_1,y_1\) from \(x_0,y_0\).

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `structure`, so Lean simply introduces a record type whose fields are the two sequences \(x\) and \(y\) together with the proofs of the two inequality families. No tactic commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` appear, and no named theorem or local lemma is invoked.

Mathematically, the fields `step_x` and `step_y` are not conclusions derived from earlier hypotheses; they are the defining constraints of an element of `CA2`. To construct an element of `CA2`, one would have to supply \(x:\mathbb N\to X\), \(y:\mathbb N\to Y\), and, for every \(n\in\mathbb N\), proofs that the displayed inequalities hold for all test points \(\xi\in X\) and \(\eta\in Y\). Conversely, from an existing element of `CA2`, one may project its fields to obtain those sequences and inequalities. The comments in the source identify these inequalities with the argmin or optimality conditions for the two updates, but the mathematical content of the declaration is exactly the two displayed families of inequalities and the data they constrain.

