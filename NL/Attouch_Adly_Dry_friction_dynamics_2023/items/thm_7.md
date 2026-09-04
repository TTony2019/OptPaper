## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/thm_7.lean`

## Lean statement
```lean
theorem theorem_4_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {s₀ r α : ℝ} (hr : 0 < r) (hα : 1 < α) (hs₀ : 0 < s₀)
    (A : H →L[ℝ] H) (f : H → ℝ) (hf : Differentiable ℝ f) (x dx ddx p g q : ℝ → H)
    (hsymm : A.IsSymmetric) (hpos : ∀ u ≠ 0, 0 < inner ℝ (A u) u)
    (_hsolution : IsDryStarTrajectory r α s₀ f hf x dx ddx p)
    (hbridge : ∀ s ∈ Set.Ici s₀,
      g (s ^ 2 / (2 * (α - 1))) = A (x s + (s / (α - 1)) • dx s))
    (hdualDrygrad : ∀ t, q t ∈ frictionBallProjector r (g t) ∧
      HasDerivAt g (A (q t - g t)) t)
    (hcoercive : ∃ rate ν : ℝ, 0 < rate ∧ 0 < ν ∧ ∀ ξ : H,
      rate * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ ∧ inner ℝ (A ξ) ξ ≤ ν * ‖ξ‖ ^ 2)
    (henergyDeriv : ∀ t : ℝ, HasDerivAt
      (fun u => Metric.infDist (g u) (frictionBall r) ^ 2 / 2)
      (- inner ℝ (g t - q t) (A (g t - q t))) t)
    (hinitial : r < ‖g (s₀ ^ 2 / (2 * (α - 1)))‖) :
    ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧ ∀ s ∈ Set.Ici s₀,
      Metric.infDist (A (x s + (s / (α - 1)) • dx s)) (frictionBall r) ≤ C * Real.exp (-μ * s ^ 2)
```

## Statement explanation
The theorem is a statement about a real Hilbert space \(H\) with a symmetric positive-definite continuous linear operator \(A\). It assumes \(r>0\), \(\alpha>1\), and \(s_0>0\). The data include a differentiable function \(f:H\to\mathbb R\), curves \(x,dx,ddx,p,g,q:\mathbb R\to H\), and a collection of hypotheses:

- \(A\) is symmetric, and for every nonzero \(u\in H\), \(\langle A u,u\rangle>0\).
- \(x\) is part of a “dry star trajectory” satisfying a predicate `IsDryStarTrajectory r α s₀ f hf x dx ddx p`.
- For every \(s\ge s_0\),
  \[
  g\left(\frac{s^2}{2(\alpha-1)}\right)
  =
  A\left(x(s)+\frac{s}{\alpha-1}\,dx(s)\right).
  \]
- For every \(t\), \(q(t)\) belongs to the friction ball projector of \(g(t)\), and the derivative of \(g\) at \(t\) is \(A(q(t)-g(t))\).
- The operator \(A\) is coercive and bounded above in the sense that there exist positive constants \(\mathsf{rate}\) and \(\nu\) such that for all \(\xi\in H\),
  \[
  \mathsf{rate}\,\|\xi\|^2 \le \langle A\xi,\xi\rangle \le \nu\,\|\xi\|^2.
  \]
- For every \(t\), the derivative of
  \[
  \frac{1}{2}\operatorname{dist}(g(t),\operatorname{frictionBall}(r))^2
  \]
  is
  \[
  -\langle g(t)-q(t), A(g(t)-q(t))\rangle.
  \]
- Initially,
  \[
  r<\left\|g\left(\frac{s_0^2}{2(\alpha-1)}\right)\right\|.
  \]

Under these assumptions, the conclusion is that there exist positive real constants \(C\) and \(\mu\) such that for every \(s\ge s_0\),
\[
\operatorname{dist}\left(
A\left(x(s)+\frac{s}{\alpha-1}dx(s)\right),
\operatorname{frictionBall}(r)
\right)
\le
C e^{-\mu s^2}.
\]
Thus the distance from the rescaled trajectory point to the friction ball decays exponentially in \(s^2\).

## Lean proof
```lean
by
  rcases theorem_3_3 (t₀ := s₀ ^ 2 / (2 * (α - 1))) hr A g q hsymm hpos
    hdualDrygrad hcoercive henergyDeriv hinitial with
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
The proof begins by invoking a previous theorem, `theorem_3_3`, with initial time
\[
t_0=\frac{s_0^2}{2(\alpha-1)}.
\]
It supplies the assumptions \(hr\), \(A\), \(g\), \(q\), \(hsymm\), \(hpos\), `hdualDrygrad`, `hcoercive`, `henergyDeriv`, and `hinitial`. The `rcases` command destructs the existential conclusion of `theorem_3_3`, obtaining constants `Cupper`, `Clower`, `rate`, `ν` and associated positivity and bound properties. The important component used later is `hupper`, which gives an exponential upper bound for the distance of \(g(t)\) from the friction ball for times \(t\ge t_0\).

Next, the proof uses `refine` to produce the desired existential witnesses:
\[
C=\mathrm{Cupper},\qquad \mu=\frac{\mathsf{rate}}{2(\alpha-1)}.
\]
The positivity of \(C\) is given by `hCupper`. The positivity of \(\mu\) is proved by `div_pos`: the numerator is positive by `hrate`, and the denominator is positive because \(2>0\) and \(\alpha-1>0\). The fact \(0<\alpha-1\) is obtained from \(1<\alpha\) using `sub_pos.mpr`.

After supplying the witnesses, the proof introduces an arbitrary \(s\) with \(s\in \operatorname{Ici} s_0\), i.e. \(s\ge s_0\). It then applies the upper bound `hupper` to the time
\[
t=\frac{s^2}{2(\alpha-1)}.
\]
The proof that this time is at least the initial time \(t_0\) is supplied by `scaled_time_mem_Ici`.

This gives a bound for
\[
\operatorname{dist}\left(g\left(\frac{s^2}{2(\alpha-1)}\right),\operatorname{frictionBall}(r)\right).
\]
The rewrite `rw [hbridge s hs, scaled_exponent_eq hα] at hbound` replaces the argument of \(g\) using the bridge hypothesis:
\[
g\left(\frac{s^2}{2(\alpha-1)}\right)
=
A\left(x(s)+\frac{s}{\alpha-1}dx(s)\right),
\]
and also rewrites the exponent from
\[
-\mathsf{rate}\cdot \frac{s^2}{2(\alpha-1)}
\]
to
\[
-\frac{\mathsf{rate}}{2(\alpha-1)}\cdot s^2.
\]
After these rewrites, `hbound` is exactly the desired inequality, so `exact hbound` finishes the proof. The commands `simp` and `linarith` are not used in this proof.

