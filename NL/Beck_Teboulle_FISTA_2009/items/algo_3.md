## Source file
`Beck_Teboulle_FISTA_2009/items/algo_3.lean`

## Lean statement
```lean
theorem proximal_step_at {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ} {Lf : ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTAConstantStepsize f g Lf x0)
    (k : ℕ) : IsProxPoint f g Lf (A.x k) (A.x (k + 1))
```

## Statement explanation
Fix a natural number $n$ and work in the Euclidean space $\mathbb{R}^n$. The theorem concerns two real-valued functions $f,g:\mathbb{R}^n\to\mathbb{R}$, a real parameter $L_f$, and an initial point $x_0\in\mathbb{R}^n$. The main hypothesis is an object $A$ of type `ISTAConstantStepsize f g Lf x0`. Such an object provides a sequence of iterates; write $x_k$ for the value of the sequence field `A.x` at $k$. The theorem also takes an arbitrary natural number $k$. Its conclusion is

$$
\operatorname{IsProxPoint} f g L_f x_k x_{k+1}.
$$

The predicate `IsProxPoint` is the formal proximal-step relation for the data $f,g,L_f$: it relates an input point and an output point. Thus the theorem says that every consecutive pair of iterates of this constant-stepsize ISTA construction satisfies the proximal-step condition. In other words, for every natural number $k$, the transition from $x_k$ to $x_{k+1}$ is a proximal step. It does not assert convergence, optimality, or any inequality; it only records the local step relation at each index. Since $k$ is allowed to be $0$, the statement also covers the first transition from $x_0$ to $x_1$. The provided source does not spell out the defining equation of `IsProxPoint`, so the explanation treats it as the named proximal-step predicate rather than asserting a specific formula for it.

## Lean proof
```lean
by
  exact A.proximal_step (k + 1) (by omega)
```

## Proof explanation
The proof is a direct application of a field of the hypothesis $A$. The goal is

$$
\operatorname{IsProxPoint} f g L_f x_k x_{k+1}.
$$

The term `A.proximal_step` is a component of the structure $A$. As used in this proof, its content is: for every natural number $i$ satisfying the required positivity/nonzero side condition, one has

$$
\operatorname{IsProxPoint} f g L_f x_{i-1} x_i.
$$

The proof instantiates this field at $i=k+1$. The second argument, `(by omega)`, is an anonymous proof term for the side condition required by the field at this instantiation, namely that $k+1$ is positive, equivalently $k+1\neq 0$, in the natural numbers. The tactic `omega` is a decision procedure for linear arithmetic over naturals and integers, so it discharges this immediate arithmetic obligation.

After specialization, the field gives

$$
\operatorname{IsProxPoint} f g L_f x_{(k+1)-1} x_{k+1}.
$$

Since $(k+1)-1=k$ in $\mathbb{N}$, this is exactly

$$
\operatorname{IsProxPoint} f g L_f x_k x_{k+1},
$$

which is the desired conclusion. The tactic `exact` closes the goal by supplying this term directly. No induction, rewriting, simplification, or additional inequality reasoning is used; the mathematical content is precisely the reindexing of the proximal-step field from the pair $x_{i-1},x_i$ to the pair $x_k,x_{k+1}$ by choosing $i=k+1$. The commands `intro`, `rw`, `simp`, and `linarith` do not appear in the proof.

