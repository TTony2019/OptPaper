## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/algo_7.lean`

## Lean statement
```lean
def IsISTATrajectory {n : Type*} [Fintype n] [DecidableEq n]
    {K : Type*} [NormedAddCommGroup K] [NormedSpace ℝ K]
    [InnerProductSpace ℝ K] (prox : (n → ℝ) → n → ℝ) (A : (n → ℝ) → K) (At : K → n → ℝ)
    (data : K) (lam γ : ℝ) (_hAt : ∀ x z, inner ℝ (A x) z = ∑ i, x i * (At z) i)
    (f : (n → ℝ) → EReal) (_hf : ∀ v, f v = ((lam * γ * ∑ i, |v i| : ℝ) : EReal))
    (hfproper : ERealFunction.IsProper f) (hflsc : IsClosed (ERealFunction.epigraph f))
    (hfconvex : Convex ℝ (ERealFunction.epigraph f))
    (_hprox : ∀ x, ERealFunction.IsProxPoint (ERealFunction.properIoi f hfproper) x (prox x))
    (u : ℕ → n → ℝ) : Prop :=
  ∀ k, u (k + 1) = prox (u k - (2 * lam) • At (A (u k) - data))
```

## Statement explanation
The declaration introduces a predicate named `IsISTATrajectory`. It is a definition, not a theorem, and it describes when a sequence $u$ follows an ISTA-type recurrence, given a collection of auxiliary data and hypotheses.

The first parameters are type-level data. The type $n$ is a finite index type with decidable equality, encoded by the typeclass assumptions `Fintype n` and `DecidableEq n`. Thus $n \to \mathbb{R}$ is the finite-dimensional real vector space of functions from $n$ to $\mathbb{R}$, which one may view as $\mathbb{R}^n$ when $n$ is a finite index set. The type $K$ is a real inner product space: it has a normed additive group structure, an $\mathbb{R}$-vector-space structure, and an inner product, written $\langle \cdot,\cdot\rangle_K$ or in Lean as `inner ℝ`.

The non-type parameters are:

- $\mathrm{prox} : (n \to \mathbb{R}) \to (n \to \mathbb{R})$, a map from vectors in $\mathbb{R}^n$ to vectors in $\mathbb{R}^n$.
- $A : (n \to \mathbb{R}) \to K$, a map from $\mathbb{R}^n$ to $K$.
- $\mathrm{At} : K \to (n \to \mathbb{R})$, a map from $K$ back to $\mathbb{R}^n$.
- $d \in K$, called `data`.
- real scalars $\lambda$ and $\gamma$.

There is a hypothesis `_hAt` saying that for every $x \in n \to \mathbb{R}$ and every $z \in K$,

```math
\langle A x, z\rangle_K = \sum_{i \in n} x_i\,(\mathrm{At} z)_i .
```

This is an adjoint-pairing identity: the inner product in $K$ between $A x$ and $z$ equals the Euclidean dot product in $\mathbb{R}^n$ between $x$ and $\mathrm{At} z$. It does not by itself assert that $A$ or $\mathrm{At}$ is linear; it states this pairing identity for all $x$ and $z$.

There is also an extended-real-valued function $f : (n \to \mathbb{R}) \to \overline{\mathbb{R}}$. The hypothesis `_hf` states that for every $v \in n \to \mathbb{R}$,

$$
f(v) = \lambda\gamma \sum_{i \in n} |v_i|,
$$

where the right-hand side is first computed as a real number and then coerced into the extended real line. Thus $f$ is the weighted $\ell^1$-type function with weight $\lambda\gamma$.

The remaining hypotheses on $f$ are that $f$ is proper, that its epigraph is closed, and that its epigraph is convex over $\mathbb{R}$:

$$
\mathrm{IsProper}(f), \qquad
\mathrm{epi}(f) \text{ is closed}, \qquad
\mathrm{epi}(f) \text{ is convex over } \mathbb{R}.
$$

These are the properness, closedness, and convexity assumptions for an extended-real function. Their exact internal definitions are not expanded in the source.

The hypothesis `_hprox` states that for every $x \in n \to \mathbb{R}$, the point $\mathrm{prox}(x)$ is a proximal point of the auxiliary function `ERealFunction.properIoi f hfproper` at $x$. In symbols, it says

$$
\forall x,\quad
\mathrm{IsProxPoint}\bigl(\mathrm{properIoi}(f), x, \mathrm{prox}(x)\bigr).
$$

The exact defining inequality of `ERealFunction.IsProxPoint`, and the exact definition of `ERealFunction.properIoi`, are not present in the supplied source, so the visible content is exactly that this proximal-point predicate holds for the auxiliary function constructed from $f$.

Finally, $u : \mathbb{N} \to (n \to \mathbb{R})$ is a sequence of vectors in $\mathbb{R}^n$, written $u_k = u(k)$. The predicate `IsISTATrajectory` is then defined by

$$
\forall k \in \mathbb{N},\qquad
u_{k+1}
=\mathrm{prox}\left(
u_k - (2\lambda)\mathrm{At}\bigl(A(u_k)-d\bigr)
\right).
$$

Here subtraction and scalar multiplication take place in the vector space $n \to \mathbb{R}$. Thus the definition says that each successor $u_{k+1}$ is obtained from $u_k$ by subtracting $2\lambda$ times the adjoint image of the residual $A(u_k)-d$, and then applying `prox`. The hypotheses `_hAt`, `_hf`, `_hprox`, `hfproper`, `hflsc`, and `hfconvex` are parameters of the predicate, but they do not occur in the final defining recurrence. They serve as ambient context rather than additional conjuncts of the predicate. The definition does not assert existence, uniqueness, convergence, or optimality of such a sequence; it only defines the property that a given sequence satisfies the displayed recurrence.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The declaration is a `def`, and the Lean source contains only the comment that there is no proof. Therefore there are no tactic commands such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no local lemmas or theorems are invoked.

Mathematically, the content of the definition is exactly the universal recurrence

$$
\forall k \in \mathbb{N},\qquad
u_{k+1}
=\mathrm{prox}\left(
u_k - (2\lambda)\mathrm{At}\bigl(A(u_k)-d\bigr)
\right).
$$

If one unfolds `IsISTATrajectory`, this is the proposition obtained. To prove the predicate for a particular sequence $u$, one would have to prove this equality for every natural number $k$. Conversely, from a proof of the predicate, one may extract the equality at any chosen $k$. No such proof is present in the source.

The assumptions `_hAt`, `_hf`, `_hprox`, `hfproper`, `hflsc`, and `hfconvex` are carried as parameters but are not used in the defining recurrence. In particular, `hfproper` appears in the type of `_hprox`, but none of these hypotheses form part of the final proposition after the definition is unfolded. Thus the declaration itself imposes no condition on $u$ beyond the displayed update equation.

