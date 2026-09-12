## Source file
`Attouch_Redont_A_New_Class_of_Alternating_Proximal_Minimization_Algorithms_with_Costs_to_Move_2007/items/algo_3.lean`

## Lean statement
```lean
structure JointProximalAlgorithm (X Y : Type*)
    (f : X → ℝ) (g : Y → ℝ) (h : X → X → ℝ) (k : Y → Y → ℝ)
    (c : X → Y → ℝ) (α β μ ν : ℕ → ℝ) where
  x : ℕ → X
  y : ℕ → Y
  step (n : ℕ) (ξ : X) (η : Y) :
    jointProximalObjective f g h k c α β μ ν x y n (x (n+1)) (y (n+1)) ≤
      jointProximalObjective f g h k c α β μ ν x y n ξ η
```

## Statement explanation
This declaration defines a structure named `JointProximalAlgorithm`. It is parameterized by two arbitrary types $X$ and $Y$ (Lean `Type*`), by two real-valued functions

$$
f:X\to\mathbb R,\qquad g:Y\to\mathbb R,
$$

by two binary real-valued functions

$$
h:X\to X\to\mathbb R,\qquad k:Y\to Y\to\mathbb R,
$$

by a real-valued function on the product

$$
c:X\to Y\to\mathbb R,
$$

and by four real sequences indexed by the natural numbers

$$
\alpha,\beta,\mu,\nu:\mathbb N\to\mathbb R.
$$

These are all parameters of the structure; the declaration imposes no separate algebraic, convexity, positivity, or existence hypotheses on them.

An inhabitant of the structure consists of two sequences

$$
x:\mathbb N\to X,\qquad y:\mathbb N\to Y,
$$

together with a field named `step`. For this field, write $J_n(\xi,\eta)$ for the real number denoted by the visible expression

$$
\operatorname{jointProximalObjective}(f,g,h,k,c,\alpha,\beta,\mu,\nu,x,y,n,\xi,\eta).
$$

The exact internal formula of `jointProximalObjective` is not supplied in the declaration, so its only mathematically specified role here is as the real-valued objective being compared by $\le$. The field `step` has the type: for every $n\in\mathbb N$, every $\xi\in X$, and every $\eta\in Y$,

$$
J_n(x(n+1),y(n+1))\le J_n(\xi,\eta).
$$

Here $x(n+1)$ and $y(n+1)$ are the next elements of the two sequences. Therefore the declaration says that the pair $(x(n+1),y(n+1))$ is a global minimizer, up to equality, of the objective $J_n$ over all possible pairs $(\xi,\eta)\in X\times Y$, for every step $n$. It is a joint proximal or joint minimization condition, because the minimization is performed simultaneously over both variables $\xi$ and $\eta$, not alternately.

The declaration does not assert that such sequences exist. It defines a class of algorithm trajectories: any object of type `JointProximalAlgorithm` is a pair of sequences together with a proof that each successive pair minimizes the specified objective at that step.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `structure`, so the body consists only of data and proof fields. The sequences $x$ and $y$ are data fields, and `step` is the single proof-bearing field. Its type is a dependent function: to every $n\in\mathbb N$, $\xi\in X$, and $\eta\in Y$ it assigns a proof of the inequality

$$
J_n(x(n+1),y(n+1))\le J_n(\xi,\eta).
$$

Thus, to construct an inhabitant of the structure, one must supply the two sequences and, for each step index and each candidate pair, a proof that the chosen next pair gives a value no larger than that candidate pair.

No tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` appear, and no named local theorem or lemma is invoked. The only cited identifier in the field type is `jointProximalObjective`, whose defining formula is not provided; the mathematically visible content is exactly the pointwise minimization inequality above. If an inhabitant $A$ of the structure is available, projecting its field `step` at $n,\xi,\eta$ yields precisely that inequality, specialized to the sequences carried by $A$.

