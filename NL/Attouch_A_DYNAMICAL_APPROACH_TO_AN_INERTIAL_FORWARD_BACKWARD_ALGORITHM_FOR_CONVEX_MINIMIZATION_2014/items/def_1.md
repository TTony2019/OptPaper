## Source file
`Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014/items/def_1.lean`

## Lean statement
```lean
structure IFBHypothesis {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi theta : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (a b lam Lpsi : ℝ) : Prop where
  phi_proper : ERealFunction.IsProper phi
  phi_lower_semicontinuous : IsClosed (ERealFunction.epigraph phi)
  phi_convex : Convex ℝ (ERealFunction.epigraph phi)
  psi_differentiable : Differentiable ℝ psi
  psi_gradient : ∀ x h, fderiv ℝ psi x h = inner ℝ (gradPsi x) h
  psi_lipschitz : ∀ x y, ‖gradPsi x - gradPsi y‖ ≤ Lpsi * ‖x - y‖
  a_pos : 0 < a
  b_pos : 0 < b
  step_pos : 0 < lam
  step_lt : lam < min (1 / a) (2 * (a + b) / (b * Lpsi))
  theta_eq : ∀ x, theta x = phi x + (psi x : EReal)
  theta_convex : Convex ℝ (ERealFunction.epigraph theta)
  theta_bounded_below : ∃ m : ℝ, ∀ x, (m : EReal) ≤ theta x
```

## Statement explanation
The declaration introduces a proposition-valued structure named `IFBHypothesis`. Its parameters are a real inner product space $H$, two extended-real-valued functions $\varphi,\theta:H\to\mathrm{EReal}$, a real-valued function $\psi:H\to\mathbb R$, a map $g:H\to H$, and four real parameters $a,b,\lambda,L_\psi$. Here $H$ is assumed to be a normed additive commutative group and an inner product space over $\mathbb R$, so it carries a norm $\lVert\cdot\rVert$ and an inner product $\langle\cdot,\cdot\rangle$. The structure does not assert that such objects exist; rather, an inhabitant of `IFBHypothesis` is a package of all the following hypotheses.

- `phi_proper` records that $\varphi$ is a proper extended-real function in the sense of `ERealFunction.IsProper`.
- `phi_lower_semicontinuous` states that the epigraph of $\varphi$, as encoded by `ERealFunction.epigraph`, is closed. For extended-real functions this is the closed-epigraph formulation of lower semicontinuity of $\varphi$.
- `phi_convex` states that the epigraph of $\varphi$ is convex over $\mathbb R$. This is the epigraphical formulation of convexity of $\varphi$.
- `psi_differentiable` states that $\psi$ is differentiable over $\mathbb R$.
- `psi_gradient` states that for every $x\in H$ and every $h\in H$,

$$
D\psi(x)(h)=\langle g(x),h\rangle,
$$

  where $D\psi(x)$ is the Fréchet derivative of $\psi$ at $x$. Thus the derivative linear functional is represented by the vector $g(x)$ through the inner product, so $g$ is a gradient field for $\psi$.
- `psi_lipschitz` states that for all $x,y\in H$,

$$
\lVert g(x)-g(y)\rVert\le L_\psi\lVert x-y\rVert.
$$

  Thus $g$ is Lipschitz with constant $L_\psi$. Together with the previous field, this says that $\psi$ has a Lipschitz gradient represented by $g$.
- `a_pos`, `b_pos`, and `step_pos` state respectively that

$$
0<a,\qquad 0<b,\qquad 0<\lambda.
$$

- `step_lt` imposes the strict step-size bound

$$
\lambda<\min\left(\frac{1}{a},\frac{2(a+b)}{bL_\psi}\right).
$$

  This is a parameter restriction involving the two positive parameters $a,b$, the step size $\lambda$, and the Lipschitz constant $L_\psi$.
- `theta_eq` states that for every $x\in H$,

$$
\theta(x)=\varphi(x)+(\psi(x))_{\mathrm{EReal}},
$$

  where $\psi(x)\in\mathbb R$ is regarded as an element of $\mathrm{EReal}$. Thus $\theta$ is the extended-real sum of the nonsmooth part $\varphi$ and the finite smooth part $\psi$.
- `theta_convex` states that the epigraph of $\theta$ is convex over $\mathbb R$, i.e. that $\theta$ is convex in the epigraphical sense.
- `theta_bounded_below` states that there exists a real number $m$ such that for every $x\in H$,

$$
(m)_{\mathrm{EReal}}\le \theta(x).
$$

  Thus $\theta$ has a finite lower bound.

In summary, `IFBHypothesis` is not a convergence theorem or an algorithm statement. It is a structure that bundles the standing assumptions for an inertial forward-backward setting: a proper, closed, convex extended-real function $\varphi$; a differentiable real-valued function $\psi$ whose gradient is the map $g$ and is Lipschitz with constant $L_\psi$; positive parameters $a,b,\lambda$ satisfying the displayed step-size bound; and a convex, bounded-below composite function $\theta=\varphi+\psi$.

## Lean proof
```lean
-- No separate proof part.
```

## Proof explanation
There is no separate proof part for this declaration. The Lean source contains only the comment `-- No separate proof part.` The declaration is a `structure` definition whose target is `Prop`, so Lean creates a proposition-like type whose fields are exactly the listed hypotheses. There are no tactic commands such as `intro`, `rw`, `simp`, `exact`, or `linarith`, and there are no applications of named lemmas or previously established results. Consequently there are no proof steps to analyze and no cited mathematical results whose hypotheses or conclusions need to be specialized. Using an inhabitant of `IFBHypothesis` would mean projecting the relevant field as a hypothesis; constructing an inhabitant would mean supplying proofs for every field. But the declaration itself performs neither operation.

