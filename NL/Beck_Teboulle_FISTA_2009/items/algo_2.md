## Source file
`Beck_Teboulle_FISTA_2009/items/algo_2.lean`

## Lean statement
```lean
theorem descent_condition {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTABacktracking f g x0)
    (k : ℕ) (hk : 1 ≤ k) :
    compositeObjective f g (A.x k) ≤ quadraticApprox f g (A.L k) (A.x k) (A.y k)
```

## Statement explanation
Let $n$ be a natural number and let $E=\mathbb R^n$, represented in Lean by `EuclideanSpace ℝ (Fin n)`. The theorem is stated for two functions $f,g:E\to\mathbb R$ and an initial point $x_0\in E$. The hypothesis $A:\mathrm{FISTABacktracking}\,f\,g\,x_0$ says that $A$ is a FISTA backtracking run for the composite objective built from $f$ and $g$, initialized at $x_0$. In particular, for each index $k$, the notation $A.x_k$ and $A.y_k$ denotes the corresponding points of $E$, and $A.L_k$ denotes the step-size or majorization parameter chosen at that iteration.

Besides the run $A$, the theorem assumes a natural number $k$ and the side condition $1\le k$. The conclusion is

$$
\mathrm{compositeObjective}(f,g)(A.x_k)
\le
\mathrm{quadraticApprox}(f,g)(A.L_k)(A.x_k)(A.y_k).
$$

Equivalently, if we abbreviate

$$
F(z)=\mathrm{compositeObjective}(f,g)(z),
\qquad
Q(L,u,v)=\mathrm{quadraticApprox}(f,g)(L)(u)(v),
$$

then the statement is

$$
F(A.x_k)\le Q(A.L_k,A.x_k,A.y_k).
$$

Mathematically, this is the descent or acceptance condition for the backtracking step at iteration $k$: the true composite objective value at the iterate $x_k$ is bounded above by the quadratic approximation using the chosen parameter $L_k$, evaluated at the two iterates $x_k$ and $y_k$. Thus the chosen backtracking parameter is admissible because the quadratic model does not underestimate the objective at this step. The statement does not explicitly list smoothness, convexity, or Lipschitz assumptions; such information is intended to be encapsulated in the structure `FISTABacktracking`. The condition $1\le k$ ensures that the step-update rules for a noninitial iteration are available.

## Lean proof
```lean
by
  have haccepted := (A.exponent_is_least k hk).1
  rw [A.stepsize_update k hk, A.x_update k hk]
  exact haccepted
```

## Proof explanation
The proof is by tactic mode. The first command is

`have haccepted := (A.exponent_is_least k hk).1`.

The term `A.exponent_is_least k hk` is a fact or field of the backtracking run $A$. It is invoked with the index $k$ and the proof $h_k:1\le k$. Its result is a conjunction or product, and `.1` extracts the first component. That first component is the acceptance inequality for the backtracking step at iteration $k$. The full statement of `exponent_is_least` is not contained in the provided excerpt, so the only visible consequence is that this extracted first component is precisely the inequality needed for the target once the definitions of $A.L_k$ and $A.x_k$ have been unfolded. In mathematical terms, it supplies the already-established fact that the chosen step size and the corresponding updated point satisfy the required quadratic bound.

The next command is

`rw [A.stepsize_update k hk, A.x_update k hk]`.

The two named facts `A.stepsize_update k hk` and `A.x_update k hk` are conditional equations available from the run $A$ under the side condition $1\le k$. The first rewrites the occurrence of the step-size parameter $A.L_k$ in the goal into the value determined by the backtracking update. The second rewrites the occurrence of the iterate $A.x_k$ into the point determined by the update, namely the proximal-gradient-type point associated with the current step. Passing `k` and `hk` supplies the iteration index and discharges the condition $1\le k$. After these rewrites, the goal has the same form as the inequality extracted as `haccepted`.

The final command is `exact haccepted`. Since the rewritten goal is syntactically the same as the type of the local fact `haccepted`, this proof term closes the goal. No `intro`, `simp`, or `linarith` is used here. The proof is a projection of the accepted inequality from the backtracking data followed by a rewriting of the target into the form in which that inequality was stated.

