## Source file
`Beck_Teboulle_FISTA_2009/items/thm_2.lean`

## Lean statement
```lean
theorem fista_convergence_rate {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {Lf : ℝ} (hP : ProblemP f g Lf)
    {x0 : EuclideanSpace ℝ (Fin n)} (A : FISTARun f g Lf x0)
    (xStar : EuclideanSpace ℝ (Fin n)) (hxStar : xStar ∈ solutionSet f g)
    (k : ℕ) (hk : 1 ≤ k) :
    compositeObjective f g (A.x k) - compositeObjective f g xStar ≤
      (2 * A.alpha * Lf * ‖x0 - xStar‖ ^ 2) / (((k : ℝ) + 1) ^ 2)
```

## Statement explanation
The declaration `fista_convergence_rate` is a theorem. It is quantified over a dimension $n : \mathbb N$, two real-valued functions $f,g$ on the Euclidean space $\mathbb R^n$, a real parameter $L_f$, a problem hypothesis `hP : ProblemP f g Lf`, an initial point $x_0$, a FISTA run $A : FISTARun f g Lf x_0$, a point $x^\star$, a hypothesis `hxStar : x^\star \in solutionSet f g`, a natural number $k$, and a proof `hk : 1 \le k`.

The type `FISTARun f g Lf x_0` is an inductive type whose two constructors correspond to the constant-stepsize and backtracking variants of FISTA. Thus $A$ is not merely a parameter tuple but a whole run, carrying its iterates. The term `A.x k` is the $k$-th iterate of the underlying run, and `A.alpha` is a real coefficient which distinguishes the two variants. The supplied definition of `FISTARun.alpha` gives

$$
\alpha(A)=
\begin{cases}
1, & A = \mathrm{constant}(\mathrm{run}),\\
\mathrm{run.eta}, & A = \mathrm{backtracking}(\mathrm{run},\mathrm{bounds}).
\end{cases}
$$

The supplied definition of `FISTARun.x` gives, in both cases, the iterate sequence of the underlying `run`:

$$
A.x\,k =
\begin{cases}
\mathrm{run}.x\,k, & A = \mathrm{constant}(\mathrm{run}),\\
\mathrm{run}.x\,k, & A = \mathrm{backtracking}(\mathrm{run},\mathrm{bounds}).
\end{cases}
$$

Let

$$
F(x)=\mathrm{compositeObjective} f g (x)
$$

and write $X_k=A.x\,k$. The conclusion is the non-asymptotic objective-gap bound

$$
F(X_k)-F(x^\star)
\le
\frac{2\,\alpha(A)\,L_f\,\|x_0-x^\star\|^2}
{((k:\mathbb R)+1)^2}.
$$

Here $\|x_0-x^\star\|^2$ is the squared Euclidean distance from the initial point to $x^\star$, and $((k:\mathbb R)+1)^2$ is $(k+1)^2$ computed in the real numbers. The hypothesis `hxStar` says that $x^\star$ belongs to `solutionSet f g`, the solution set used by the theorem. The hypothesis `hP` is the common problem assumption passed unchanged to the two cited rate theorems; its internal fields are not unfolded in this proof. The definitions of `ProblemP`, `solutionSet`, and `compositeObjective` are not expanded in the source, so the theorem uses them only through the two cited FISTA rate results.

The statement is therefore a unified $O(1/k^2)$ convergence-rate theorem for FISTA. For the constant-stepsize constructor, $\alpha(A)=1$, so the coefficient is $2L_f$. For the backtracking constructor, $\alpha(A)=\mathrm{run.eta}$, so the coefficient is $2\eta L_f$, where $\eta$ is the backtracking parameter of the underlying run.

## Lean proof
```lean
by
  cases A with
  | constant run =>
      simpa [FISTARun.x, FISTARun.alpha] using
        fista_constant_stepsize_rate hP run xStar hxStar k hk
  | backtracking run bounds =>
      simpa [FISTARun.x, FISTARun.alpha] using
        fista_backtracking_rate hP run bounds xStar hxStar k hk
```

## Proof explanation
The proof begins with `by`. The first tactic is `cases A with`, which performs case analysis on the inductive value $A : FISTARun f g Lf x_0$. This splits the proof into the two possible constructors of `FISTARun`: the constant-stepsize case and the backtracking case. In each branch, Lean substitutes the corresponding constructor into the goal and introduces the constructor fields.

In the constant branch, Lean has replaced $A$ by `FISTARun.constant run`. The goal is therefore the original inequality with $A$ specialized to this constructor. Using the definitions `FISTARun.x` and `FISTARun.alpha`, the term `(FISTARun.constant run).x` rewrites to `run.x`, and the term `(FISTARun.constant run).alpha` rewrites to $1$. Thus the goal becomes

$$
F(\mathrm{run}.x\,k)-F(x^\star)
\le
\frac{2\cdot 1\cdot L_f\,\|x_0-x^\star\|^2}
{((k:\mathbb R)+1)^2}.
$$

The cited theorem `fista_constant_stepsize_rate` states that for a constant-stepsize FISTA run `A`, under the same problem hypothesis `hP`, with $x^\star \in solutionSet f g$ and $1 \le k$,

$$
F(A.x\,k)-F(x^\star)
\le
\frac{2\,L_f\,\|x_0-x^\star\|^2}
{((k:\mathbb R)+1)^2}.
$$

Applying it to the introduced `run`, and using the same `hP`, `xStar`, `hxStar`, `k`, and `hk`, gives exactly the needed inequality after simplifying $2\cdot 1$ to $2$. The command `simpa [FISTARun.x, FISTARun.alpha] using fista_constant_stepsize_rate hP run xStar hxStar k hk` performs this rewriting and then closes the goal with the cited theorem instance.

In the backtracking branch, Lean has replaced $A$ by `FISTARun.backtracking run bounds`. Here `run` is the underlying backtracking FISTA run and `bounds` is the step-size bound proof stored in the constructor. The definitions `FISTARun.x` and `FISTARun.alpha` rewrite `(FISTARun.backtracking run bounds).x` to `run.x` and `(FISTARun.backtracking run bounds).alpha` to `run.eta`. Hence the goal becomes

$$
F(\mathrm{run}.x\,k)-F(x^\star)
\le
\frac{2\,\mathrm{run.eta}\,L_f\,\|x_0-x^\star\|^2}
{((k:\mathbb R)+1)^2}.
$$

The cited theorem `fista_backtracking_rate` states that for a backtracking FISTA run `A`, under the same `hP`, with a step-size bounds hypothesis `h_bounds : BacktrackingStepsizeBounds Lf A.L0 A.eta A.L`, with $x^\star \in solutionSet f g$, and with $1 \le k$,

$$
F(A.x\,k)-F(x^\star)
\le
\frac{2\,A.\eta\,L_f\,\|x_0-x^\star\|^2}
{((k:\mathbb R)+1)^2}.
$$

Applying it to `run` and to the embedded `bounds` proof, together with the same `hP`, `xStar`, `hxStar`, `k`, and `hk`, gives exactly the needed inequality. The command `simpa [FISTARun.x, FISTARun.alpha] using fista_backtracking_rate hP run bounds xStar hxStar k hk` rewrites the goal to match that theorem’s conclusion and closes it.

There is no explicit use of `intro`, `rw`, `exact`, or `linarith` in this proof. The case split is handled by `cases`, while `simpa ... using ...` performs the needed definitional rewriting, simple arithmetic simplification, and final application of the cited rate theorem. The proof is complete once both constructors of `FISTARun` have been treated.

