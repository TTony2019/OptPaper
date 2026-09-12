## Source file
`Beck_Teboulle_FISTA_2009/items/thm_1.lean`

## Lean statement
```lean
theorem ista_convergence_rate {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {Lf : ℝ} (hP : ProblemP f g Lf)
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTARun f g Lf x0)
    (xStar : EuclideanSpace ℝ (Fin n)) (hxStar : xStar ∈ solutionSet f g)
    (k : ℕ) (hk : 1 ≤ k) :
    compositeObjective f g (A.x k) - compositeObjective f g xStar ≤
      (A.alpha * Lf * ‖x0 - xStar‖ ^ 2) / (2 * (k : ℝ))
```

## Statement explanation
The theorem `ista_convergence_rate` is a convergence-rate statement for an ISTA run in finite dimension. The ambient space is $\mathbb R^n$, represented in Lean as `EuclideanSpace ℝ (Fin n)`. The data are functions $f,g:\mathbb R^n\to\mathbb R$, a real parameter $L_f$, an initial point $x_0\in\mathbb R^n$, and a run $A$ of type `ISTARun f g Lf x0`. The hypothesis $hP$ is a proof of `ProblemP f g Lf`; its internal content is not expanded in the supplied source, and in the proof it is simply passed to the two specialized rate theorems. The point $x_\star$ satisfies $x_\star\in\texttt{solutionSet f g}$; the definition of `solutionSet` is not supplied, but this is the reference point against which the objective gap is measured. The natural number $k$ satisfies $1\le k$.

Let $A_k$ denote the iterate `A.x k`, and let $\alpha_A$ denote the scalar `A.alpha`. The conclusion is

$$
\operatorname{compositeObjective}(f,g)(A_k)
-
\operatorname{compositeObjective}(f,g)(x_\star)
\le
\frac{\alpha_A L_f \|x_0-x_\star\|^2}{2 (k:\mathbb R)}.
$$

The scalar $\alpha_A$ is defined by cases on the run: for a constant-stepsize run $\alpha_A=1$, while for a backtracking run $\alpha_A$ is the backtracking parameter $\eta$ of the underlying run. Thus the theorem says uniformly that after $k\ge 1$ ISTA iterations, the composite-objective gap at the $k$-th iterate relative to a solution is bounded by $(\alpha_A L_f \|x_0-x_\star\|^2)/(2k)$. In the constant-stepsize case this is the usual $L_f/(2k)$ rate; in the backtracking case the same bound carries the extra factor $\eta$. The theorem is therefore a common wrapper for the two concrete rates.

## Lean proof
```lean
by
  cases A with
  | constant run =>
      simpa [ISTARun.x, ISTARun.alpha] using
        ista_constant_stepsize_rate hP run xStar hxStar k hk
  | backtracking run bounds =>
      simpa [ISTARun.x, ISTARun.alpha] using
        ista_backtracking_rate hP run bounds xStar hxStar k hk
```

## Proof explanation
The proof is a case analysis on the inductive type `ISTARun`. The command `cases A with` splits the run $A$ into its two possible constructors. No `intro`, `rw`, `simp`, `exact`, or `linarith` appears in the supplied proof; the essential commands are `cases`, `simpa`, and `using`. In each branch, `simpa` simplifies the goal using the defining equations of `ISTARun.x` and `ISTARun.alpha`, and `using` supplies the proof of the already-established specialized rate theorem.

In the constant branch, $A$ is `ISTARun.constant run`, where `run` is a constant-stepsize ISTA run. The definition of `ISTARun.x` gives that the iterate sequence of $A$ is the iterate sequence of `run`, so `A.x k` becomes `run.x k`. The definition of `ISTARun.alpha` gives $\alpha_A=1$. Therefore the goal in this branch reduces to

$$
\operatorname{compositeObjective}(f,g)(run.x(k))
-
\operatorname{compositeObjective}(f,g)(x_\star)
\le
\frac{L_f \|x_0-x_\star\|^2}{2 (k:\mathbb R)}.
$$

The theorem `ista_constant_stepsize_rate` says exactly this: under the same problem hypothesis $hP$, for a constant-stepsize run `run`, a solution $x_\star$, and $1\le k$, the composite-objective gap of the $k$-th iterate is bounded by $(L_f \|x_0-x_\star\|^2)/(2k)$. The proof invokes it with `hP`, `run`, `xStar`, `hxStar`, `k`, and `hk`. The `simpa` step performs the reductions `A.x k = run.x k` and `A.alpha = 1`, simplifies the trivial factor $1\cdot L_f$ to $L_f$, and then uses the specialized theorem to close the goal.

In the backtracking branch, $A$ is `ISTARun.backtracking run bounds`. Here `run` is the underlying backtracking ISTA run and `bounds` is the bundled proof of the backtracking step-size bounds required by the backtracking rate theorem. The definition of `ISTARun.x` again gives `A.x k = run.x k`. The definition of `ISTARun.alpha` gives $\alpha_A=\texttt{run.eta}$, the backtracking parameter. Hence the goal in this branch reduces to

$$
\operatorname{compositeObjective}(f,g)(run.x(k))
-
\operatorname{compositeObjective}(f,g)(x_\star)
\le
\frac{\eta L_f \|x_0-x_\star\|^2}{2 (k:\mathbb R)},
$$

where $\eta$ is the backtracking parameter of `run`. The theorem `ista_backtracking_rate` states precisely this: under $hP$, for a backtracking run with its step-size bounds `bounds`, a solution $x_\star$, and $1\le k$, the composite-objective gap is bounded by $(\eta L_f \|x_0-x_\star\|^2)/(2k)$. The proof invokes it with `hP`, `run`, `bounds`, `xStar`, `hxStar`, `k`, and `hk`. The `simpa` step reduces `A.x` to `run.x` and `A.alpha` to `run.eta`, then uses that theorem to close the goal. Thus both possible forms of an ISTA run satisfy the single displayed bound from the statement, with $\alpha_A$ equal to $1$ in the constant case and to the backtracking parameter in the backtracking case.

