## Source file
`Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004/items/algo_1.lean`

## Lean statement
```lean
structure RelaxedInertialHPPA
    (A : SetValuedOperator H H) (lam alpha rho : ℕ → ℝ) (sigma : ℝ) where
  x : ℕ → H
  y : ℕ → H
  z : ℕ → H
  v : ℕ → H
  eta : ℕ → H
  /-- The natural-number encoding uses the standard initialization `x⁻¹ = x⁰`.
  Thus the paper's first inertial step is represented by the `k = 0` case. -/
  y_def : ∀ k : ℕ, y k = x k + alpha k • (x k - x (k - 1))
  step_inclusion :
    ∀ k : ℕ,
      v k ∈ (rho k) • A ((rho k)⁻¹ • z k + (1 - (rho k)⁻¹) • y k)
  residual_bound :
    ∀ k : ℕ,
      ‖eta k‖ ≤ sigma *
        max (‖z k - y k‖ / lam k) (‖v k‖)
  equation :
    ∀ k : ℕ,
      (lam k)⁻¹ • (z k - y k) + v k = eta k
  finite_stop_if_zero :
    ∀ k : ℕ, v k = 0 →
      ∀ n : ℕ, k + 1 ≤ n → x n = y k ∧ y n = y k ∧ z n = y k ∧ v n = 0
  update_if_nonzero :
    ∀ k : ℕ, v k ≠ 0 →
      x (k + 1) =
        y k - (⟪v k, y k - z k⟫_ℝ / ‖v k‖ ^ 2) • v k
```

## Statement explanation
The declaration introduces a structure, not a theorem, called `RelaxedInertialHPPA`. It packages the data and constraints defining a relaxed inertial hybrid projection-proximal point algorithm. The ambient space is denoted $H$, with norm $\|\cdot\|$ and real inner product $\langle\cdot,\cdot\rangle_{\mathbb R}$. The parameters are a set-valued operator $A$ of type `SetValuedOperator H H`, real sequences $\lambda,\alpha,\rho:\mathbb N\to\mathbb R$, and a real number $\sigma$. An inhabitant of the structure consists of five sequences

$$
x,y,z,v,\eta:\mathbb N\to H
$$

together with proofs of the following conditions.

- The field `y_def` states that for every $k\in\mathbb N$,

  $$
  y_k=x_k+\alpha_k(x_k-x_{k-1}).
  $$

  The documentation comment explains that Lean uses the standard initialization $x_{-1}=x_0$. Formally, since natural-number subtraction is truncated, at $k=0$ the term $x_{k-1}$ is $x_0$, so the formula gives $y_0=x_0+\alpha_0(x_0-x_0)=x_0$. For $k\ge 1$, this is the usual inertial extrapolation step using the previous iterate $x_{k-1}$.

- The field `step_inclusion` states that for every $k\in\mathbb N$,

  $$
  v_k\in \rho_k\cdot A\!\left(\rho_k^{-1}z_k+(1-\rho_k^{-1})y_k\right).
  $$

  Here $A(w)$ is a subset of $H$, and $\rho_k\cdot A(w)$ means the set of all scalar multiples $\rho_k a$ with $a\in A(w)$. Thus $v_k$ is selected from the scaled value of $A$ at the relaxed point

  $$
  w_k=\rho_k^{-1}z_k+(1-\rho_k^{-1})y_k,
  $$

  which is an affine combination of $z_k$ and $y_k$. When $\rho_k\ne 0$, the inclusion is equivalent to

  $$
  \frac{v_k}{\rho_k}\in A(w_k).
  $$

- The field `residual_bound` states that for every $k\in\mathbb N$,

  $$
  \|\eta_k\|\le \sigma\max\!\left(\frac{\|z_k-y_k\|}{\lambda_k},\|v_k\|\right).
  $$

  This is an inexactness or residual control condition: it bounds the norm of the error sequence $\eta_k$ by $\sigma$ times the larger of a step-size-scaled distance and the norm of the selected operator value.

- The field `equation` states that for every $k\in\mathbb N$,

  $$
  \lambda_k^{-1}(z_k-y_k)+v_k=\eta_k.
  $$

  Thus $\eta_k$ is the residual of the perturbed proximal relation. If $\lambda_k\ne 0$, this can be rearranged as

  $$
  z_k=y_k+\lambda_k(\eta_k-v_k).
  $$

  Together with `step_inclusion` and `residual_bound`, this encodes an inexact relaxed proximal step.

- The field `finite_stop_if_zero` states that if $v_k=0$ for some $k$, then for every $n\in\mathbb N$ with $k+1\le n$,

  $$
  x_n=y_k,\qquad y_n=y_k,\qquad z_n=y_k,\qquad v_n=0.
  $$

  In words, once the selected operator value vanishes at step $k$, the algorithm remains fixed at $y_k$ from the next index onward, with all later $x,y,z$ equal to $y_k$ and all later $v$ equal to zero. This condition is conditional: it does not assert that such a $k$ exists.

- The field `update_if_nonzero` states that if $v_k\ne 0$, then

  $$
  x_{k+1}
  =
  y_k-\frac{\langle v_k,y_k-z_k\rangle_{\mathbb R}}{\|v_k\|^2}v_k.
  $$

  This is the orthogonal projection of $y_k$ onto the affine hyperplane through $z_k$ with normal $v_k$, namely

  $$
  \{u\in H:\langle v_k,u-z_k\rangle_{\mathbb R}=0\}.
  $$

  The hypothesis $v_k\ne 0$ ensures that the denominator $\|v_k\|^2$ is nonzero.

Overall, `RelaxedInertialHPPA` is a record type whose elements are complete trajectories of the algorithm: the inertial step defines $y$, the relaxed inclusion defines $v$, the equation and residual bound define and control $\eta$, the zero case describes termination or stagnation, and the nonzero case gives the projection update for $x_{k+1}$. The declaration itself does not assert that such a trajectory exists, nor does it include any explicit maximal-monotonicity hypothesis on $A$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `structure`, so the lines after `where` are field specifications rather than a theorem whose proof is being constructed. Consequently, there are no proof steps involving tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no named theorem or lemma is invoked. The documentation comments, including the comment about the initialization $x_{-1}=x_0$, are metadata and do not change the mathematical content of the fields. To produce an inhabitant of `RelaxedInertialHPPA`, one must supply the five sequences $x,y,z,v,\eta$ and proofs that they satisfy the six listed field conditions. Thus the mathematical content is entirely specification: the structure defines what it means for such sequences to be a relaxed inertial hybrid projection-proximal point trajectory.

