## Source file
`Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020/items/def_4.lean`

## Lean statement
```lean
structure VariableMetricMoreauData {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (M : H →L[ℝ] H) (lam : ℝ) (hlam : 0 < lam) where
  symmetric : ∀ x y, @inner ℝ H _ (M x) y = @inner ℝ H _ x (M y)
  positive_definite : ∀ x, x ≠ 0 → 0 < metricNormSq M x
  envelope : H → ℝ
  prox : H → H
  envelope_eq (x : H) : envelope x = variableMetricMoreauEnvelope f M symmetric positive_definite lam hlam x
  prox_minimizes (x xi : H) : f (prox x) + metricNormSq M (x - prox x) / (2 * lam) ≤
    f xi + metricNormSq M (x - xi) / (2 * lam)
  prox_unique (x p : H) :
    f p + metricNormSq M (x - p) / (2 * lam) = envelope x → p = prox x
  optimality (x : H) : M (x - prox x) ∈ (fun u ↦ lam • u) '' subdifferential f (prox x)
  gradient : H → H
  gradient_eq (x : H) : gradient x = (1 / lam) • M (x - prox x)
  muMin : ℝ
  muMax : ℝ
  muMin_pos : 0 < muMin
  muMin_isLeast : ∀ μ : ℝ, (∃ v : H, v ≠ 0 ∧ M v = μ • v) → muMin ≤ μ
  muMin_isEigenvalue : ∃ v : H, v ≠ 0 ∧ M v = muMin • v
  muMax_isGreatest : ∀ μ : ℝ, (∃ v : H, v ≠ 0 ∧ M v = μ • v) → μ ≤ muMax
  muMax_isEigenvalue : ∃ v : H, v ≠ 0 ∧ M v = muMax • v
  prox_lipschitz : ∀ x y,
    ‖prox x - prox y‖ ≤ (muMax / muMin) * ‖x - y‖
  gradient_lipschitz : ∀ x y,
    ‖gradient x - gradient y‖ ≤ (1 / lam) * Real.sqrt (muMax / muMin) * ‖x - y‖
  minimizers : ∀ x, (envelope x = sInf (Set.range f)) ↔ (f x = sInf (Set.range f))
```

## Statement explanation
The declaration `VariableMetricMoreauData` introduces a structure, that is, a bundled specification of data and properties, rather than a theorem to be proved. Its parameters are: an arbitrary type $H$ equipped with the structure of a normed additive commutative group and a real inner product space; a function $f : H \to \mathbb R$; a continuous $\mathbb R$-linear map $M : H \to H$; a real number $\lambda$; and a proof $h_\lambda$ that $0 \lt  \lambda$. Thus any instance of this structure is data attached to a positive parameter $\lambda$, an objective $f$, and a linear metric operator $M$.

The field `symmetric` states that

$$
\forall x,y\in H,\qquad \langle M x, y\rangle_{\mathbb R}=\langle x, M y\rangle_{\mathbb R}.
$$

So $M$ is self-adjoint with respect to the real inner product.

The field `positive_definite` states that

$$
\forall x\in H,\qquad x\ne 0 \implies 0 < \mathrm{metricNormSq}(M,x).
$$

The expression $\mathrm{metricNormSq}(M,x)$ is the metric squared norm associated with $M$; its exact definition is not included in this declaration, but the visible condition is that it is strictly positive on nonzero vectors.

The fields `envelope : H → ℝ` and `prox : H → H` are the variable-metric Moreau envelope and the proximal map. The field `envelope_eq` says that for every $x\in H$,

$$
\mathrm{envelope}(x)
=\mathrm{variableMetricMoreauEnvelope}(f,M,\lambda,h_\lambda,x),
$$

with the Lean term also passing the symmetry and positive-definiteness proofs as explicit arguments. This makes the envelope the variable-metric Moreau envelope determined by $f$, $M$, and $\lambda$. The exact definition of `variableMetricMoreauEnvelope` is not part of this declaration.

The field `prox_minimizes` says that for all $x,\xi\in H$,

$$
f(\mathrm{prox}(x))
+\frac{\mathrm{metricNormSq}(M,x-\mathrm{prox}(x))}{2\lambda}
\le
f(\xi)
+\frac{\mathrm{metricNormSq}(M,x-\xi)}{2\lambda}.
$$

Thus $\mathrm{prox}(x)$ is a global minimizer of the Moreau objective

$$
\xi \mapsto f(\xi)+\frac{1}{2\lambda}\mathrm{metricNormSq}(M,x-\xi).
$$

The field `prox_unique` says that if a point $p$ satisfies

$$
f(p)+\frac{\mathrm{metricNormSq}(M,x-p)}{2\lambda}=\mathrm{envelope}(x),
$$

then $p=\mathrm{prox}(x)$. So the proximal minimizer is unique.

The field `optimality` states that

$$
M(x-\mathrm{prox}(x))\in \lambda\cdot \partial f(\mathrm{prox}(x)),
$$

where $\lambda\cdot \partial f(\mathrm{prox}(x))$ is the image of the subdifferential under the map $u\mapsto \lambda u$. Equivalently, there exists $u\in \partial f(\mathrm{prox}(x))$ such that

$$
M(x-\mathrm{prox}(x))=\lambda u.
$$

This is the first-order optimality condition for the proximal minimization problem.

The fields `gradient : H → H` and `gradient_eq` define the gradient map by

$$
\mathrm{gradient}(x)
=\frac{1}{\lambda}M(x-\mathrm{prox}(x)).
$$

So the gradient is the scaled metric displacement between $x$ and its proximal point.

The real numbers `muMin` and `muMax` represent the extremal eigenvalues of $M$. The field `muMin_pos` says $0\lt \mu_{\min}$. The field `muMin_isLeast` says that every real eigenvalue $\mu$ of $M$, meaning every $\mu$ for which there exists nonzero $v$ with $M v=\mu v$, satisfies $\mu_{\min}\le \mu$. The field `muMin_isEigenvalue` says that $\mu_{\min}$ itself is an eigenvalue. Hence $\mu_{\min}$ is the least eigenvalue of $M$. Similarly, `muMax_isGreatest` says every eigenvalue $\mu$ satisfies $\mu\le \mu_{\max}$, and `muMax_isEigenvalue` says $\mu_{\max}$ is an eigenvalue. Hence $\mu_{\max}$ is the greatest eigenvalue of $M$. In particular, from these fields one also gets $\mu_{\min}\le \mu_{\max}$.

The field `prox_lipschitz` states that for all $x,y\in H$,

```math
\|\mathrm{prox}(x)-\mathrm{prox}(y)\|
\le
\frac{\mu_{\max}}{\mu_{\min}}\,\|x-y\|.
```

Thus the proximal map is Lipschitz with constant equal to the ratio of the largest to the smallest eigenvalue of $M$.

The field `gradient_lipschitz` states that for all $x,y\in H$,

```math
\|\mathrm{gradient}(x)-\mathrm{gradient}(y)\|
\le
\frac{1}{\lambda}\sqrt{\frac{\mu_{\max}}{\mu_{\min}}}\,\|x-y\|.
```

Thus the gradient map is Lipschitz with constant involving the square root of the same eigenvalue ratio, scaled by $1/\lambda$.

Finally, the field `minimizers` states that for every $x\in H$,

$$
\mathrm{envelope}(x)=\inf_{z\in H} f(z)
\quad\Longleftrightarrow\quad
f(x)=\inf_{z\in H} f(z).
$$

Here the infimum is the infimum of the set of values of $f$, written in Lean as `sInf (Set.range f)`. So $x$ is a global minimizer of $f$ exactly when the envelope value at $x$ equals the global infimum of $f$. In summary, the structure packages a variable-metric Moreau envelope, proximal map, gradient map, extremal eigenvalues of the metric, first-order optimality, uniqueness of the proximal point, Lipschitz bounds, and preservation of global minimizers. It does not assert that such data exist; it specifies the properties any instance must satisfy.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part. The Lean source contains only the structure declaration and the comment `-- No separate proof part.` Therefore there are no tactic steps such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and no named theorem or lemma is invoked. The mathematical content is entirely contained in the field types of the structure.

To construct an element of `VariableMetricMoreauData f M lam hlam`, one must supply the functions `envelope`, `prox`, and `gradient`, the real numbers `muMin` and `muMax`, and proofs of all the listed properties: symmetry and positive definiteness of $M$, the defining equality of the envelope, the minimization and uniqueness properties of `prox`, the optimality condition, the formula for `gradient`, the extremal eigenvalue statements, the Lipschitz estimates for `prox` and `gradient`, and the minimizer equivalence. No such construction or existence proof is performed in this declaration.

The field types mention `variableMetricMoreauEnvelope`, `metricNormSq`, `subdifferential`, and `Real.sqrt`. Their complete definitions are not included in this declaration. The visible mathematical consequences are exactly those recorded in the fields: the envelope equals the variable-metric Moreau envelope of $f$; the metric squared norm appears in the positivity condition and in the proximal penalty terms; the subdifferential appears in the first-order optimality condition; and `Real.sqrt` appears in the gradient Lipschitz bound. No local result is cited because no proof is performed.

