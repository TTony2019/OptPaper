## Source file
`Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001/items/algo_1.lean`

## Lean statement
```lean
structure InertialProximalPointAlgorithm (A : SetValuedOperator H H)
    (x : ℕ → H) (alpha lambda : ℕ → ℝ) : Prop where
  alpha_mem : ∀ k : ℕ, 0 ≤ alpha k ∧ alpha k < 1
  lambda_pos : ∀ k : ℕ, 0 < lambda k
  update : ∀ k : ℕ, 1 ≤ k →
    x (k + 1) ∈ (lambda k • A).resolvent (x k + alpha k • (x k - x (k - 1)))
```

## Statement explanation
The declaration introduces a proposition-valued structure named `InertialProximalPointAlgorithm`. Its parameters are a set-valued operator $A$ on an ambient space $H$, a sequence $x:\mathbb N\to H$, and two real sequences $\alpha:\mathbb N\to\mathbb R$ and $\lambda:\mathbb N\to\mathbb R$. Thus $x=(x_k)_{k\in\mathbb N}$, $\alpha=(\alpha_k)_{k\in\mathbb N}$, and $\lambda=(\lambda_k)_{k\in\mathbb N}$. The operator $A$ is set-valued, so $A(z)\subseteq H$ for each $z\in H$, and the notation $(\lambda_k A)$ denotes the scalar-rescaled operator.

The structure says that the triple $(x,\alpha,\lambda)$ is an inertial proximal point algorithm for $A$ exactly when three conditions hold.

First, `alpha_mem` states that for every $k\in\mathbb N$,

$$
0\le \alpha_k<1.
$$

So the inertial parameter $\alpha_k$ is nonnegative and strictly smaller than $1$.

Second, `lambda_pos` states that for every $k\in\mathbb N$,

$$
0<\lambda_k.
$$

So all proximal step sizes $\lambda_k$ are strictly positive.

Third, `update` states that for every $k\in\mathbb N$ with $1\le k$,

$$
x_{k+1}\in (\lambda_k A).\operatorname{resolvent}\!\left(x_k+\alpha_k(x_k-x_{k-1})\right).
$$

Here $x_k+\alpha_k(x_k-x_{k-1})$ is the inertial, or extrapolated, point obtained from the current iterate $x_k$ and the previous iterate $x_{k-1}$. The next iterate $x_{k+1}$ is required to lie in the resolvent of the scaled operator $\lambda_k A$ at that extrapolated point. In the usual set-valued notation, if $J_{\lambda_k A}=(I+\lambda_k A)^{-1}$ is the resolvent, then this membership is equivalent to

$$
x_k+\alpha_k(x_k-x_{k-1})\in x_{k+1}+\lambda_k A(x_{k+1}),
$$

or, since $\lambda_k>0$, equivalently

$$
\frac{x_k+\alpha_k(x_k-x_{k-1})-x_{k+1}}{\lambda_k}\in A(x_{k+1}).
$$

Thus the declaration encodes the standard implicit inertial proximal-point recurrence: form an inertial point from $x_{k-1}$ and $x_k$, then take a proximal step with parameter $\lambda_k$. The condition is stated as membership because $A$ is set-valued; the structure does not assert uniqueness of $x_{k+1}$. The recurrence begins at $k=1$, so the initial points $x_0$ and $x_1$ are not constrained by this structure except through later updates.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `structure`, not a theorem, so it does not prove existence of such a sequence or derive the conditions from other facts. Instead, it defines a predicate whose fields are the required hypotheses: the inequalities on $\alpha_k$, the positivity of $\lambda_k$, and the resolvent membership for every $k\ge 1$.

Mathematically, to use an assumption that `InertialProximalPointAlgorithm A x alpha lambda` holds, one may extract:
- `alpha_mem k`, giving $0\le \alpha_k$ and $\alpha_k<1$;
- `lambda_pos k`, giving $0<\lambda_k$;
- `update k hk` for $k\ge 1$, giving

$$
x_{k+1}\in (\lambda_k A).\operatorname{resolvent}\!\left(x_k+\alpha_k(x_k-x_{k-1})\right).
$$

Conversely, to prove that $x,\alpha,\lambda$ form an inertial proximal point algorithm for $A$, one must supply exactly these three fields. No named local theorem or lemma is cited, and no tactic commands such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur in this declaration.

