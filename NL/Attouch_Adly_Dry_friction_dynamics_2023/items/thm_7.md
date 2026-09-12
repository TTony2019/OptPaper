## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/thm_7.lean`

## Lean statement
```lean
theorem theorem_4_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [FiniteDimensional ℝ H] [Nontrivial H]
    {s₀ r α : ℝ} (hr : 0 < r) (hα : 1 < α) (hs₀ : 0 < s₀)
    (A : H →L[ℝ] H) (f : H → ℝ) (hf_quadratic : ∀ x : H,
      f x = inner ℝ (A x) x / 2)
    (_hf : Differentiable ℝ f)
    (x dx _ddx p g q : ℝ → H) (hg : Differentiable ℝ g)
    (_hx2 : ContDiff ℝ 2 x)
    (hsymm : A.IsSymmetric) (hpos : ∀ u ≠ 0, 0 < inner ℝ (A u) u)
    (_hsolution : IsDryStarTrajectory r α s₀ f x p)
    (hbridge : ∀ s ∈ Set.Ici s₀,
      g (s ^ 2 / (2 * (α - 1))) = A (x s + (s / (α - 1)) • dx s))
    (hdualFlow : ∀ t, q t ∈ frictionBallProjector r (g t) ∧
      fderiv ℝ (gradient (fun u =>
        (ERealFunction.conjugate (fun x => (f x : EReal)) u).toReal))
        (g t) (deriv g t) + g t - q t = 0)
    (hinitial : r < ‖g (s₀ ^ 2 / (2 * (α - 1)))‖) :
    ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧ ∀ s ∈ Set.Ici s₀,
      Metric.infDist (A (x s + (s / (α - 1)) • dx s)) (frictionBall r) ≤
        C * Real.exp (-μ * s ^ 2)
```

## Statement explanation
Let $H$ be a nontrivial finite-dimensional real Hilbert space. The declaration is about real parameters $s_0,r,\alpha$ satisfying $r\gt 0$, $\alpha\gt 1$, and $s_0\gt 0$. It takes a continuous linear map $A:H\to H$, a real-valued function $f:H\to\mathbb R$, and paths $x,dx,ddx,p,g,q:\mathbb R\to H$. The main structural assumptions are:

- $f$ is the quadratic form attached to $A$:

$$
f(x)=\frac12\langle A x,x\rangle
$$

  for every $x\in H$.
- $A$ is symmetric: $A$ is self-adjoint for the real inner product.
- $A$ is positive definite: for every nonzero $u\in H$,

$$
0<\langle A u,u\rangle.
$$

- $g$ is differentiable. There are also hypotheses that $f$ is differentiable, that $x$ is $C^2$, and that $(x,p)$ is a dry-star trajectory, but in the Lean statement these are marked with leading underscores and are not used in the proof.
- The bridge condition connects the transformed path $g$ to the original scaled trajectory: for every $s\ge s_0$,

```math
g\!\left(\frac{s^2}{2(\alpha-1)}\right)
=A\!\left(x(s)+\frac{s}{\alpha-1}\,dx(s)\right).
```

- The dual-flow condition says that for every $t$,

$$
q(t)\in \mathrm{frictionBallProjector}_r(g(t)),
$$

  and, writing

$$
\Phi(u)=\left(\mathrm{conj}\bigl(v\mapsto f(v)\bigr)(u)\right)_{\mathbb R}
$$

  for the real value of the extended-real Fenchel conjugate of $f$,

$$
\left(\mathrm{fderiv}_{\mathbb R}(\nabla \Phi)(g(t))\right)(g'(t))
+g(t)-q(t)=0.
$$

  Here the exact definition of the friction-ball projector and extended-real conjugate is not needed for the algebraic part of the proof; the whole condition is passed to the cited theorem.
- The initial condition is

```math
r<\|g(s_0^2/(2(\alpha-1)))\|.
```

The conclusion is that there exist positive constants $C$ and $\mu$ such that for every $s\ge s_0$,

```math
\mathrm{infDist}\!\left(
A\!\left(x(s)+\frac{s}{\alpha-1}\,dx(s)\right),
\mathrm{frictionBall}_r
\right)
\le C e^{-\mu s^2}.
```

Thus the distance of the scaled trajectory $A(x(s)+(s/(\alpha-1))dx(s))$ from the friction ball decays exponentially in the squared variable $s^2$.

## Lean proof
```lean
by
  rcases theorem_3_3 (t₀ := s₀ ^ 2 / (2 * (α - 1))) hr A f hsymm hpos g q
    hf_quadratic hg hdualFlow hinitial with
    ⟨Cupper, Clower, rate, ν, hCupper, hClower, hrate, hν, hupper, hlower, hnotmem⟩
  refine ⟨Cupper, rate / (2 * (α - 1)), hCupper,
    div_pos hrate (mul_pos (by norm_num) (sub_pos.mpr hα)), ?_⟩
  intro s hs
  have hbound := hupper (s ^ 2 / (2 * (α - 1)))
    (scaled_time_mem_Ici hs₀ hα hs)
  rw [hbridge s hs, scaled_exponent_eq hα] at hbound
  exact hbound
```

## Proof explanation
The proof first invokes the previously established theorem `theorem_3_3`. In its own variables, that theorem assumes a symmetric positive definite continuous linear operator, the associated quadratic form $f(x)=\frac12\langle Ax,x\rangle$, a differentiable path $g$, a path $p$ satisfying the friction-ball projector and dual-flow condition, and an initial condition $`r<\|g(t_0)\|`$. It then produces positive constants$C_{\text{upper}},C_{\text{lower}},\mu,\nu$such that for every$t\ge t_0$,

$$
\mathrm{infDist}(g(t),\mathrm{frictionBall}_r)\le C_{\text{upper}}e^{-\mu t},
$$

together with a lower exponential bound and the statement that $g(t)$ never lies in the friction ball.

In this proof, `theorem_3_3` is applied with time origin

$$
t_0=\frac{s_0^2}{2(\alpha-1)}.
$$

The supplied hypotheses $r\gt 0$, symmetry of $A$, positive definiteness of $A$, the quadratic identity for $f$, differentiability of $g$, the dual-flow condition with the given path $q$, and the initial inequality

```math
r<\|g(s_0^2/(2(\alpha-1)))\|
```

match exactly the hypotheses of `theorem_3_3`, with its path $p$ instantiated as the current path $q$. The `rcases` step therefore unpacks the existential conclusion of `theorem_3_3` into constants $C_{\text{upper}}$, $C_{\text{lower}}$, a rate `rate`, another positive constant $\nu$, and the associated inequalities. The lower bound and nonmembership conclusion are not used.

The proof then chooses witnesses

$$
C=C_{\text{upper}},\qquad
\mu=\frac{\text{rate}}{2(\alpha-1)}.
$$

The positivity of $C$ is exactly the positivity of $C_{\text{upper}}$. For the positivity of $\mu$, the Lean term

```math
\texttt{div\_pos hrate (mul\_pos (by norm\_num) (sub\_pos.mpr hα))}
```

first uses $\alpha\gt 1$ to get $\alpha-1\gt 0$, then combines $0\lt 2$ with $0\lt \alpha-1$ to get $0\lt 2(\alpha-1)$, and finally divides the positive numerator `rate` by this positive denominator. Hence $0\lt \mu$.

Next `intro s hs` introduces an arbitrary $s$ together with the hypothesis $hs:s\in \mathrm{Ici}s_0$, i.e. $s\ge s_0$. The goal is to prove the desired decay inequality at this arbitrary $s$.

The upper bound from `theorem_3_3` is then applied at the transformed time

$$
t=\frac{s^2}{2(\alpha-1)}.
$$

To use it, the proof needs

```math
\frac{s^2}{2(\alpha-1)}
\in
\mathrm{Ici}\!\left(\frac{s_0^2}{2(\alpha-1)}\right),
```

that is,

$$
\frac{s^2}{2(\alpha-1)}
\ge
\frac{s_0^2}{2(\alpha-1)}.
$$

This is supplied by `scaled_time_mem_Ici`. That lemma uses $s_0\gt 0$, $\alpha\gt 1$, and $s\ge s_0$. Since $s_0\gt 0$ and $s\ge s_0$, both $s$ and $s_0$ are nonnegative, so $s^2\ge s_0^2$. Also $2(\alpha-1)\gt 0$, so dividing by this positive denominator preserves the inequality. Therefore the transformed time lies in the interval where the upper bound from `theorem_3_3` is valid.

Consequently, the hypothesis `hbound` contains

```math
\mathrm{infDist}\!\left(
g\!\left(\frac{s^2}{2(\alpha-1)}\right),
\mathrm{frictionBall}_r
\right)
\le
C_{\text{upper}}
\exp\!\left(-\text{rate}\cdot \frac{s^2}{2(\alpha-1)}\right).
```

The rewrite `rw [hbridge s hs, scaled_exponent_eq hα] at hbound` transforms this inequality in two ways. First, the bridge hypothesis for $s\ge s_0$ replaces

```math
g\!\left(\frac{s^2}{2(\alpha-1)}\right)
```

by

```math
A\!\left(x(s)+\frac{s}{\alpha-1}\,dx(s)\right).
```

Second, `scaled_exponent_eq` gives the algebraic identity

$$
-\text{rate}\cdot \frac{s^2}{2(\alpha-1)}
=-\left(\frac{\text{rate}}{2(\alpha-1)}\right)s^2.
$$

Thus the exponent becomes exactly $-\mu s^2$ for the chosen

$$
\mu=\frac{\text{rate}}{2(\alpha-1)}.
$$

After these rewrites, `hbound` has the form

```math
\mathrm{infDist}\!\left(
A\!\left(x(s)+\frac{s}{\alpha-1}\,dx(s)\right),
\mathrm{frictionBall}_r
\right)
\le
C_{\text{upper}}e^{-\mu s^2},
```

which is precisely the goal for the chosen $C$ and $\mu$. The final `exact hbound` closes the proof. Since $s\ge s_0$ was arbitrary, the universal decay statement follows.

