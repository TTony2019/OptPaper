## Source file
`Beck_Teboulle_FISTA_2009/items/algo_4.lean`

## Lean statement
```lean
theorem descent_condition {n : ℕ} {f g : EuclideanSpace ℝ (Fin n) → ℝ}
    {x0 : EuclideanSpace ℝ (Fin n)} (A : ISTABacktracking f g x0)
    (k : ℕ) (hk : 1 ≤ k) :
    compositeObjective f g (A.x k) ≤
      quadraticApprox f g (A.L k) (A.x k) (A.x (k - 1))
```

## Statement explanation
The declaration `descent_condition` is a theorem about one step of a backtracking ISTA iteration. Let $n$ be a natural number, let $f,g:\mathbb R^n\to\mathbb R$, let $x_0\in\mathbb R^n$, and let $A$ be a structure of type `ISTABacktracking f g x0`. Such a structure encodes a run of ISTA with backtracking; in particular it supplies an iterate sequence $A.x:\mathbb N\to\mathbb R^n$ and a step-size or parameter sequence $A.L:\mathbb N\to\mathbb R$. The theorem is stated for a natural number $k$ with hypothesis $1\le k$, meaning that $k$ is a positive step index and $k-1$ is its predecessor.

Writing $F(z)$ for the composite objective `compositeObjective f g z`, and $Q_L(z,y)$ for the quadratic approximation `quadraticApprox f g L z y`, the conclusion is

```math
F\bigl(A.x(k)\bigr)
\le
Q_{A.L(k)}\bigl(A.x(k),\,A.x(k-1)\bigr).
```

The supplied definition of `BacktrackingAccepted` says exactly that

$$
\text{BacktrackingAccepted}(f,g,L,y,z)
\quad\Longleftrightarrow\quad
F(z)\le Q_L(z,y).
$$

Thus the theorem says that at every positive step $k$, the current iterate $A.x(k)$ is accepted by the backtracking test with parameter $A.L(k)$ and previous point $A.x(k-1)$. Equivalently, the composite objective at the new point is bounded above by the quadratic approximation centered at the previous point, evaluated at the new point, with the current step-size parameter. This is the descent or acceptance condition used in the backtracking loop: the chosen parameter $A.L(k)$ makes the quadratic model an upper bound for the objective at the update.

## Lean proof
```lean
by
  have haccepted := (A.exponent_is_least k hk).1
  rw [A.stepsize_update k hk, A.x_update k hk]
  simpa [BacktrackingAccepted] using haccepted
```

## Proof explanation
The proof is a direct repackaging of the backtracking acceptance condition at step $k$.

First, the line

```lean
have haccepted := (A.exponent_is_least k hk).1
```

introduces a local hypothesis named `haccepted`. The expression `A.exponent_is_least k hk` is a result about step $k$, using the hypothesis $hk:1\le k$. Its first component is extracted by `.1`. From the way this hypothesis is used later, the only relevant consequence is that it provides the acceptance assertion for the candidate update at step $k$, i.e. an instance of `BacktrackingAccepted` for the candidate parameter and candidate point produced by the backtracking rule. The full statement of `A.exponent_is_least` is not otherwise needed; the proof uses only this first component.

Next, the line

```lean
rw [A.stepsize_update k hk, A.x_update k hk]
```

rewrites the goal using the two structural update equations for the positive step $k$. The hypothesis $hk:1\le k$ is exactly the side condition that makes these update equations applicable. Mathematically, these rewrites expose the actual expressions for the step size $A.L(k)$ and the iterate $A.x(k)$ that are used in the backtracking test. The original goal is stated in terms of the stored sequences $A.L$ and $A.x$; after rewriting, the goal is stated in terms of the underlying candidate quantities to which `haccepted` refers. This is why the two rewrites are needed before applying the acceptance condition.

Finally, the line

```lean
simpa [BacktrackingAccepted] using haccepted
```

closes the goal. The tactic `simpa` simplifies the goal using the definition of `BacktrackingAccepted`. By that definition, `BacktrackingAccepted(f,g,L,y,z)` is precisely the inequality

$$
F(z)\le Q_L(z,y).
$$

After the previous rewrites, the goal has exactly this form for the appropriate $L$, $y$, and $z$. The hypothesis `haccepted` is a proof of the corresponding `BacktrackingAccepted` proposition. Therefore `simpa [BacktrackingAccepted] using haccepted` unfolds the definition and applies the stored acceptance fact to prove

```math
F\bigl(A.x(k)\bigr)
\le
Q_{A.L(k)}\bigl(A.x(k),\,A.x(k-1)\bigr).
```

No arithmetic reasoning such as `linarith` is required; the proof is entirely a matter of exposing the algorithmic update equations and then unfolding the definition of backtracking acceptance.

