## Source file
`Alvarez_Minimizing_property_second_order_dissipative_2000/items/algo_1.lean`

## Lean statement
```lean
structure InertialProximalMethod {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) where
  u : ℕ → H
  eps : ℕ → ℝ
  lam : ℕ → ℝ
  alpha : ℕ → ℝ
  proper : ERealFunction.IsProper f
  closed_epigraph : IsClosed (ERealFunction.epigraph f)
  convex : Convex ℝ (ERealFunction.epigraph f)
  eps_pos : ∀ k, 0 < eps k
  lam_pos : ∀ k, 0 < lam k
  alpha_range : ∀ k, 0 ≤ alpha k ∧ alpha k < 1
  update : ∀ k : ℕ, 0 < k → 0 ∈ (fun p =>
    (lam k)⁻¹ • (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1)) + p) ''
      epsilonSubdifferential f (eps k) (u (k + 1))
```

## Statement explanation
The declaration introduces a structure, named `InertialProximalMethod`, whose parameters are a type $H$ satisfying `NormedAddCommGroup H` and `InnerProductSpace ℝ H`, and a function $f:H\to \overline{\mathbb R}$ (the Lean type `EReal`). Thus $H$ is a real inner product space, and $f$ is an extended-real-valued objective function.

An element of this structure consists of four data fields:

- $u:\mathbb N\to H$, a sequence of iterates $u_k$;
- $\varepsilon:\mathbb N\to \mathbb R$, a sequence of positive tolerances $\varepsilon_k$;
- $\lambda:\mathbb N\to \mathbb R$, a sequence of positive step sizes $\lambda_k$;
- $\alpha:\mathbb N\to \mathbb R$, a sequence of inertial parameters $\alpha_k$.

In addition, the structure requires the following propositional fields. The field `proper` asserts that $f$ is proper in the extended-real sense used by `ERealFunction.IsProper`; standardly this means that $f$ is not identically $+\infty$ and never takes the value $-\infty$. The field `closed_epigraph` asserts that the epigraph $\mathrm{epi} f$, as given by `ERealFunction.epigraph f`, is closed. The field `convex` asserts that this epigraph is convex over $\mathbb R$. Thus $f$ is assumed to be a proper closed convex extended-real-valued function.

The numerical parameter fields are:

- `eps_pos`: for every $k$, $0\lt \varepsilon_k$;
- `lam_pos`: for every $k$, $0\lt \lambda_k$;
- `alpha_range`: for every $k$, $0\le \alpha_k\lt 1$.

The final field is the update condition. Let $\partial_{\varepsilon} f(x)$ denote the $\varepsilon$-subdifferential of $f$ at $x$, as encoded by `epsilonSubdifferential f ε x`. This is the set of vectors $p\in H$ satisfying the usual approximate subgradient inequality: $p\in \partial_\epsilon f(x)$ means that for all $y\in H$,

$$
f(y)\ge f(x)+\langle p,y-x\rangle-\varepsilon .
$$

The update field says that for every natural number $k$ with $0\lt k$,

```math
0\in
\left\{
\lambda_k^{-1}\left(u_{k+1}-(1+\alpha_k)u_k+\alpha_k u_{k-1}\right)+p
\;\middle|\;
p\in \partial_{\varepsilon_k} f(u_{k+1})
\right\}.
```

The set on the right is the image of the $\varepsilon_k$-subdifferential under the translation $p\mapsto c_k+p$, where

$$
c_k=\lambda_k^{-1}\left(u_{k+1}-(1+\alpha_k)u_k+\alpha_k u_{k-1}\right).
$$

Therefore the condition $0\in c_k+\partial_{\varepsilon_k} f(u_{k+1})$ is equivalent to

$$
-c_k\in \partial_{\varepsilon_k} f(u_{k+1}),
$$

that is,

$$
-\lambda_k^{-1}\left(u_{k+1}-(1+\alpha_k)u_k+\alpha_k u_{k-1}\right)
\in \partial_{\varepsilon_k} f(u_{k+1}).
$$

If we set

$$
y_k=u_k+\alpha_k(u_k-u_{k-1}),
$$

then

$$
c_k=\lambda_k^{-1}(u_{k+1}-y_k),
$$

so the update condition becomes

$$
\lambda_k^{-1}(y_k-u_{k+1})\in \partial_{\varepsilon_k} f(u_{k+1}),
$$

or equivalently,

$$
0\in \partial_{\varepsilon_k} f(u_{k+1})
+\lambda_k^{-1}(u_{k+1}-y_k).
$$

This is exactly the approximate proximal inclusion for $u_{k+1}$ from the inertial point $y_k$. In ordinary language, the structure packages an inertial proximal method for minimizing a proper closed convex extended-real function $f$: at each positive index $k$, the next iterate $u_{k+1}$ is an $\varepsilon_k$-approximate proximal point of the extrapolated point $u_k+\alpha_k(u_k-u_{k-1})$, with step size $\lambda_k$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The source is only a `structure` declaration, and the Lean proof block is empty, with the comment `-- No separate proof part.` Therefore no tactics such as `intro`, `rw`, `simp`, `exact`, or `linarith` occur, and no named theorem or local lemma is invoked.

In Lean, a `structure` declares a record type rather than proving a theorem. To inhabit `InertialProximalMethod f`, one must provide the four data fields $u,\varepsilon,\lambda,\alpha$ together with proofs of all the propositional fields. The fields `proper`, `closed_epigraph`, and `convex` are assumptions on the objective $f$. The fields `eps_pos`, `lam_pos`, and `alpha_range` are the parameter restrictions. The field `update` is the single dynamical condition: for each $k$ with $0\lt k$, it requires the approximate proximal inclusion described above. Since there are no proof steps, the mathematical content is exactly the collection of data and obligations listed in the structure.

