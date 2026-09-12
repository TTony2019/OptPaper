## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/algo_4.lean`

## Lean statement
```lean
noncomputable def IsGeneralIFBGradientProjection {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (hC : IsChebyshev C) (Ci : ℕ → Set H) (hCi : ∀ i, IsChebyshev (Ci i))
    (ω : ℕ → ℝ) (p : ℕ) (a b lam : ℝ)
    (u y : ℕ → H) : Prop := ∀ k,
  0 < a ∧ 0 < b ∧ u (k + 1) = projectionPoint C hC ((1 - lam * a) • u k + (lam * b) • y k) ∧
  y (k + 1) = (1 / (1 + lam * b)) • y k + (lam * a / (1 + lam * b)) • u (k + 1) -
    (lam / (1 + lam * b)) • (u (k + 1) - ∑ i ∈ Finset.Icc 1 p,
      ω i • projectionPoint (Ci i) (hCi i) (u (k + 1)))
```

## Statement explanation
The declaration introduces a noncomputable predicate named `IsGeneralIFBGradientProjection`. It is parametrized by a type $H$ equipped with a normed additive commutative group structure and a real inner-product-space structure. Thus $H$ carries addition, real scalar multiplication, an inner product, and a norm; no completeness assumption is included in the statement.

The remaining parameters are:

- $C\subseteq H$, together with a hypothesis $hC$ saying that $C$ is Chebyshev.
- A sequence of subsets $C_i\subseteq H$ for $i\in\mathbb N$, together with hypotheses $hC_i$ saying that each $C_i$ is Chebyshev.
- A sequence of real weights $\omega:\mathbb N\to\mathbb R$.
- A natural number $p$, which is used only to bound the finite sum over $i=1,\dots,p$.
- Real parameters $a,b,\lambda$.
- Two sequences $u,y:\mathbb N\to H$.

Using $P_C(z)$ for the projection point onto $C$ supplied by the Chebyshev hypothesis $hC$, and $P_{C_i}(z)$ for the projection point onto $C_i$ supplied by $hC_i$, the predicate says that for every $k\in\mathbb N$,

$$
0<a \quad\text{and}\quad 0<b,
$$

and the two recursions

$$
u_{k+1}
=
P_C\bigl((1-\lambda a)u_k+\lambda b y_k\bigr)
$$

and

$$
y_{k+1}
=
\frac{1}{1+\lambda b}y_k
+
\frac{\lambda a}{1+\lambda b}u_{k+1}
-
\frac{\lambda}{1+\lambda b}
\left(
u_{k+1}
-
\sum_{i=1}^{p}\omega_i P_{C_i}(u_{k+1})
\right)
$$

hold. The sum $\sum_{i=1}^{p}$ is the finite sum over the natural indices $i$ satisfying $1\le i\le p$; if $p=0$, this sum is empty.

Mathematically, the declaration defines a property of the sequences $u$ and $y$: at each step, the primal variable $u_{k+1}$ is obtained by projecting a linear combination of $u_k$ and the auxiliary variable $y_k$ onto $C$, and then the auxiliary variable $y_{k+1}$ is updated by an affine combination of $y_k$, the new primal point $u_{k+1}$, and a correction term involving the projections of $u_{k+1}$ onto the Chebyshev sets $C_i$, weighted by $\omega_i$. The predicate asserts only that these recursive identities hold for every step; it does not assert existence, convergence, optimality, or any condition on $\lambda$, $\omega$, $p$, or the initial points.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part for this declaration. It is a definition, not a theorem or lemma, so Lean checks only that the right-hand side is a well-formed proposition. No tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, and no local named result is cited.

If one unfolds the definition, it reveals a universal statement over $k\in\mathbb N$. Proving the predicate for given data would require introducing an arbitrary $k$ and proving the conjunction of all conditions at that step: the positivity conditions $0<a$ and $0<b$, the primal projection update defining $u_{k+1}$, and the auxiliary update defining $y_{k+1}$. The Chebyshev hypotheses $hC$ and $hC_i$ are not conclusions to be proved inside the definition; they are supplied as arguments to the projection operator so that the projection points $P_C(\cdot)$ and $P_{C_i}(\cdot)$ are available. No convergence, stability, or optimality conclusion is derived here.

