## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/algo_3.lean`

## Lean statement
```lean
noncomputable def IsClassicalGradientProjectionTrajectory {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (hC : IsChebyshev C) (Ci : ℕ → Set H) (hCi : ∀ i, IsChebyshev (Ci i))
    (ω : ℕ → ℝ) (p : ℕ) (lam : ℝ) (u : ℕ → H) : Prop :=
  0 < lam ∧ lam < 2 ∧ ∀ k,
    u (k + 1) = projectionPoint C hC ((1 - lam) • u k + lam • ∑ i ∈ Finset.Icc 1 p,
      ω i • projectionPoint (Ci i) (hCi i) (u k))
```

## Statement explanation
The declaration introduces a proposition-valued predicate. Its ambient space is a type $H$ equipped with the structure of a normed additive commutative group and of an inner product space over $\mathbb R$. Thus $H$ is the vector space in which all points, sums, and scalar multiplications take place; completeness of $H$ is not assumed in the statement.

The parameters are:

- $C\subseteq H$, a set in $H$.
- `hC`, a proof that $C$ is Chebyshev; this is the certificate used by `projectionPoint` to define projection onto $C$.
- $C_i\subseteq H$ for each $i\in\mathbb N$, a sequence of sets.
- `hCi`, a function assigning to every $i\in\mathbb N$ a proof that $C_i$ is Chebyshev; thus `hCi i` is the certificate used for projection onto $C_i$.
- $\omega:\mathbb N\to\mathbb R$, a real-valued sequence of weights.
- $p\in\mathbb N$, a natural number controlling how many of the sets $C_i$ are used.
- $\lambda\in\mathbb R$, a real relaxation parameter.
- $u:\mathbb N\to H$, a sequence of points in $H$, thought of as the iterates of the algorithm.

The predicate `IsClassicalGradientProjectionTrajectory C hC Ci hCi ω p lam u` is true exactly when the following three conditions hold:

$$
0<\lambda,
\qquad
\lambda<2,
$$

and, for every $k\in\mathbb N$,

$$
u(k+1)
=P_C\!\left(
(1-\lambda)u(k)
+\lambda
\sum_{i=1}^{p}
\omega(i)\,P_{C_i}(u(k))
\right).
$$

Here $P_C$ denotes the projection point associated with the Chebyshev certificate `hC`, and $P_{C_i}$ denotes the projection point associated with the certificate `hCi i`. The sum is over the finite index set `Finset.Icc 1 p`, i.e. over all $i\in\mathbb N$ satisfying $1\le i\le p$. If $p=0$, this sum is empty and contributes $0$.

Mathematically, the declaration says that $u$ is a trajectory of a relaxed projection-type iteration: at each step $k$, one first projects the current point $u(k)$ onto each of the sets $C_1,\dots,C_p$, forms the weighted sum

$$
\sum_{i=1}^{p}\omega(i)\,P_{C_i}(u(k)),
$$

then takes the affine combination

$$
(1-\lambda)u(k)+\lambda\sum_{i=1}^{p}\omega(i)\,P_{C_i}(u(k)),
$$

and finally projects that point back onto $C$ to obtain the next iterate $u(k+1)$. The condition $0<\lambda<2$ places the relaxation parameter in the open interval $(0,2)$. The Chebyshev hypotheses `hC` and `hCi` are parameters needed to define the projection points; they are not additional conjuncts of the predicate itself. The predicate does not assert any nonnegativity, normalization, or summability condition on the weights $\omega$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `noncomputable def`, so the body after `:=` is the definition of the predicate rather than a proof of a theorem. Consequently there are no tactic commands such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no named lemmas are invoked in a proof.

The definition body is the proposition

$$
0<\lambda \;\wedge\; \lambda<2 \;\wedge\;
\forall k\in\mathbb N,\;
u(k+1)
=P_C\!\left(
(1-\lambda)u(k)
+\lambda
\sum_{i=1}^{p}
\omega(i)\,P_{C_i}(u(k))
\right).
$$

The conjunction requires all listed conditions to hold. The first two conjuncts say that the scalar $\lambda$ lies strictly between $0$ and $2$. The universal quantifier then requires the displayed recurrence to hold for every natural number $k$, so it relates $u(k+1)$ to $u(k)$ for all iterates.

On the right-hand side of the recurrence, the term

$$
P_{C_i}(u(k))
$$

is the projection point of $u(k)$ onto $C_i$, using the Chebyshev certificate `hCi i`. Each such projection is multiplied by the scalar $\omega(i)$. The notation

$$
\sum_{i=1}^{p}
$$

is Lean's finite sum over `Finset.Icc 1 p`, i.e. over the natural numbers $i$ with $1\le i\le p$. The resulting vector is multiplied by $\lambda$. The term

$$
(1-\lambda)u(k)
$$

is the current iterate scaled by $1-\lambda$. Their sum is then projected onto $C$ by

$$
P_C,
$$

using the Chebyshev certificate `hC`. The equality asserts that this projected point is exactly the next iterate $u(k+1)$.

The marker `noncomputable` indicates that the definition may rely on classical choice through the projection operator; it is not an additional mathematical hypothesis. No further assumptions about $C$, the sets $C_i$, the weights $\omega$, or the sequence $u$ are introduced beyond those appearing explicitly in the statement.

