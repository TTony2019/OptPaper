## Source file
`Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022/items/thm_4.lean`

## Lean statement
```lean
theorem togesVR_rate_and_weak_convergence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → EReal) (prox : H → H)
    (u : ℝ → H) (alpha : ℝ) (lam : ERealFunction.PosReal) (t0 : ℝ)
    (hLam : 0 < (lam : ℝ)) (hProper : ERealFunction.IsProper f) (hlsc : LowerSemicontinuous f)
    (hConvex : Convex ℝ (ERealFunction.epigraph f))
    (hArgmin : ∃ x : H, f x = sInf (Set.range f))
    (hProx : ∀ x, ERealFunction.IsProxPoint
      (lam • ERealFunction.properIoi f hProper) x (prox x)) --recall
    (hFConvex : ConvexOn ℝ Set.univ (fun x => (ERealFunction.moreauEnvelope f lam x).toReal)) --merge
    (hFMin : ∃ z, IsMinOn (fun x => (ERealFunction.moreauEnvelope f lam x).toReal) Set.univ z) --merge
    (hFInf : sInf (Set.range (fun x => (ERealFunction.moreauEnvelope f lam x).toReal)) = --merge
      (sInf (Set.range f)).toReal) (ht0pos : 0 < t0)
    (hUContDiff : ContDiff ℝ 3 u)
    (hAuxiliaryStrict : 3 < alpha → ∃ vInfinity : H,
      Asymptotics.IsLittleO atTop
        (fun t => (ERealFunction.moreauEnvelope f lam (u t + (t / 4) • deriv u t)).toReal -
          sInf (Set.range (fun x => (ERealFunction.moreauEnvelope f lam x).toReal)))
        (fun t => 1 / t ^ 3) ∧
      Tendsto (fun t => toWeakSpace ℝ H (u t + (t / 4) • deriv u t)) atTop
        (nhds (toWeakSpace ℝ H vInfinity)) ∧
      (ERealFunction.moreauEnvelope f lam vInfinity).toReal =
        sInf (Set.range (fun x => (ERealFunction.moreauEnvelope f lam x).toReal)))
    (hTrajectory : IsTOGESV alpha u (fun x => (ERealFunction.moreauEnvelope f lam x).toReal) t0) :
    (3 ≤ alpha → ∃ C : ℝ, 0 ≤ C ∧ ∀ t ≥ t0,
      (ERealFunction.moreauEnvelope f lam (u t + (t / 4) • deriv u t)).toReal -
          (sInf (Set.range f)).toReal ≤ C / t ^ 3 ∧
      (f (prox (u t + (t / 4) • deriv u t))).toReal -
          (sInf (Set.range f)).toReal ≤ C / t ^ 3 ∧
      (ERealFunction.moreauEnvelope f lam (u t)).toReal - (sInf (Set.range f)).toReal ≤ C / t ^ 3 ∧
      (f (prox (u t))).toReal - (sInf (Set.range f)).toReal ≤ C / t ^ 3) ∧
    (3 < alpha → ∃ uInfinity : H,
      Asymptotics.IsLittleO atTop
        (fun t => (ERealFunction.moreauEnvelope f lam (u t + (t / 4) • deriv u t)).toReal -
          (sInf (Set.range f)).toReal) (fun t => 1 / t ^ 3) ∧
      Asymptotics.IsLittleO atTop
        (fun t => (f (prox (u t + (t / 4) • deriv u t))).toReal -
          (sInf (Set.range f)).toReal) (fun t => 1 / t ^ 3) ∧
      Asymptotics.IsLittleO atTop
        (fun t => (ERealFunction.moreauEnvelope f lam (u t)).toReal - (sInf (Set.range f)).toReal)
          (fun t => 1 / t ^ 3) ∧
      Asymptotics.IsLittleO atTop
        (fun t => (f (prox (u t))).toReal - (sInf (Set.range f)).toReal)
          (fun t => 1 / t ^ 3) ∧
      Tendsto (fun t => toWeakSpace ℝ H (u t)) atTop
      (nhds (toWeakSpace ℝ H uInfinity)) ∧
      f uInfinity = sInf (Set.range f))
```

## Statement explanation
The theorem is a convergence-rate statement for a TOGES-V third-order-in-time evolution method applied to a convex extended-real-valued objective on a real Hilbert space. Let $H$ be a complete real inner product space. The objective is

$$
f:H\to \overline{\mathbb R},
$$

assumed to be proper, lower semicontinuous, and convex, encoded by convexity of its epigraph. The parameter $\lambda$ is a positive real parameter (Lean type `ERealFunction.PosReal`), and $e_\lambda f$ denotes the Moreau envelope of $f$ with parameter $\lambda$:

$$
e_\lambda f(x)=\inf_{y\in H}\left(f(y)+\frac{1}{2\lambda}\|x-y\|^2\right).
$$

The map $\mathrm{prox}:H\to H$ is a proximal selection. The hypothesis `hProx` says that for every $x$, $\mathrm{prox}(x)$ is a proximal point of $f$ with parameter $\lambda$ at $x$. The trajectory is

$$
u:\mathbb R\to H,
$$

and it is assumed to be $C^3$, i.e. three times continuously differentiable. The number $\alpha\in\mathbb R$ is the order parameter, and $t_0>0$ is the initial time.

Write

$$
F(x)=\bigl(e_\lambda f(x)\bigr).toReal
$$

for the real-valued Moreau envelope obtained by applying `.toReal` to the extended-real value. The assumptions on $F$ are that $F$ is convex on all of $H$, that $F$ attains a minimum on $H$, and that

$$
\inf_{x\in H} F(x)=\left(\inf_{x\in H} f(x)\right).toReal .
$$

There is also an auxiliary asymptotic hypothesis: if $3<\alpha$, then there exists $v_\infty\in H$ such that

$$
F\!\left(u(t)+\frac t4 \dot u(t)\right)-\inf F=o(t^{-3}),
$$

the shifted trajectory converges weakly,

$$
u(t)+\frac t4 \dot u(t)\rightharpoonup v_\infty,
$$

and

$$
F(v_\infty)=\inf F.
$$

Finally, the hypothesis `hTrajectory` says that $u$ is a TOGES-V trajectory of order $\alpha$ for the real objective $F$, starting at time $t_0$.

The conclusion has two parts. First, if $\alpha\ge 3$, then there is a real constant $C\ge 0$ such that for every $t\ge t_0$,

$$
\bigl(e_\lambda f(u(t)+\tfrac t4 \dot u(t))\bigr).toReal-(\inf f).toReal
\le \frac{C}{t^3},
$$

$$
\bigl(f(\mathrm{prox}(u(t)+\tfrac t4 \dot u(t)))\bigr).toReal-(\inf f).toReal
\le \frac{C}{t^3},
$$

$$
\bigl(e_\lambda f(u(t))\bigr).toReal-(\inf f).toReal
\le \frac{C}{t^3},
$$

and

$$
\bigl(f(\mathrm{prox}(u(t)))\bigr).toReal-(\inf f).toReal
\le \frac{C}{t^3}.
$$

Second, if $\alpha>3$, then there exists $u_\infty\in H$ such that all four corresponding differences are $o(t^{-3})$, the trajectory converges weakly,

$$
u(t)\rightharpoonup u_\infty,
$$

and

$$
f(u_\infty)=\inf f.
$$

Thus the theorem gives a cubic $O(t^{-3})$ rate in the critical case $\alpha\ge 3$, and a faster little- $o$ cubic rate together with weak convergence to a minimizer in the supercritical case $\alpha>3$.

## Lean proof
```lean
by
  obtain ⟨hres, hformula⟩ := proximal_point_data f lam prox hProper hlsc hConvex hProx
  have hFContDiff : ContDiff ℝ 1 (fun x => (ERealFunction.moreauEnvelope f lam x).toReal) :=
    (moreau_envelope_regularity_and_minimizers f lam hLam hProper hlsc hConvex
      (ERealFunction.moreauEnvelope f lam) prox hres (fun x => (hformula x).symm)).2.1
  have hFGradient : ∀ x, HasFDerivAt (fun x => (ERealFunction.moreauEnvelope f lam x).toReal)
      (innerSL ℝ (gradient (fun x => (ERealFunction.moreauEnvelope f lam x).toReal) x)) x := by
    intro x
    simpa [innerSL_apply_apply] using
      ((hFContDiff.differentiable (by norm_num) x).hasGradientAt.hasFDerivAt)
  have huDiff : Differentiable ℝ u := hUContDiff.differentiable (by norm_num)
  have hFirstDiff : Differentiable ℝ (deriv u) :=
    (hUContDiff.of_le (by norm_num)).differentiable_deriv_two
  have hSecondDiff : Differentiable ℝ (deriv (deriv u)) := by
    exact hUContDiff.deriv'.differentiable_deriv_two
  have hRegularity :
      (∀ t, t0 ≤ t → HasDerivAt u (deriv u t) t) ∧
      (∀ t, t0 ≤ t → HasDerivAt (deriv u) (deriv (deriv u) t) t) ∧
      (∀ t, t0 ≤ t → HasDerivAt (deriv (deriv u))
        (deriv (deriv (deriv u)) t) t) := by
    refine ⟨?_, ?_, ?_⟩
    · intro t _
      exact (huDiff t).hasDerivAt
    · intro t _
      exact (hFirstDiff t).hasDerivAt
    · intro t _
      exact (hSecondDiff t).hasDerivAt
  exact togesVR_rate_and_weak_convergence_core f prox u (deriv u) (deriv (deriv u))
    (deriv (deriv (deriv u)))
    (gradient (fun x => (ERealFunction.moreauEnvelope f lam x).toReal)) alpha lam t0 hLam hProper hlsc
    hConvex hArgmin hProx hFConvex hFGradient hFMin hFInf ht0pos
    hRegularity.1 hRegularity.2.1 hRegularity.2.2
    (fun t ht => ⟨rfl, rfl, rfl⟩) hAuxiliaryStrict hTrajectory
```

## Proof explanation
The proof is a reduction to the previously established core theorem `togesVR_rate_and_weak_convergence_core`.

First, the proof invokes `proximal_point_data` with the given objective $f$, parameter $\lambda$, proximal map $\mathrm{prox}$, and the hypotheses that $f$ is proper, lower semicontinuous, convex, and that $\mathrm{prox}$ is a proximal selection. This lemma produces two facts:

$$
\mathrm{prox}(x)\in \mathrm{resolvent}\bigl(\lambda\,\partial f\bigr)(x)
$$

for every $x$, and

$$
f(\mathrm{prox}(x))+
\frac{1}{2\lambda}\|x-\mathrm{prox}(x)\|^2
=e_\lambda f(x)
$$

for every $x$. The proof unpacks this conjunction as `hres` and `hformula`. The first fact is the standard proximal first-order/resolvent relation for $\lambda\partial f$. The second is the exact Moreau-envelope formula expressing the envelope value at $x$ in terms of the value at the proximal point and the quadratic penalty.

Next, the proof derives regularity of the real-valued Moreau envelope $F$. It applies `moreau_envelope_regularity_and_minimizers` to $f$, $\lambda$, the envelope $e_\lambda f$, and the map $\mathrm{prox}$. The hypotheses supplied to that result are positivity of $\lambda$, properness, lower semicontinuity, convexity, the resolvent membership `hres`, and the reversed envelope formula `(hformula x).symm`. The theorem `moreau_envelope_regularity_and_minimizers` states, in this setting, that the epigraph of the envelope is convex, that the real-valued function

$$
x\mapsto \bigl(e_\lambda f(x)\bigr).toReal
$$

is $C^1$, that the infimum of the envelope equals the infimum of $f$, that the minimizer set of the envelope equals the minimizer set of $f$, and that the envelope satisfies the proximal representation formula. The proof only needs the second component, so it extracts

$$
\text{`hFContDiff`}:\quad
x\mapsto \bigl(e_\lambda f(x)\bigr).toReal
\text{ is }C^1.
$$

From this $C^1$ regularity, the proof constructs the gradient hypothesis needed by the core theorem. For every $x$, the function

$$
F(x)=\bigl(e_\lambda f(x)\bigr).toReal
$$

is differentiable at $x$. On a Hilbert space, differentiability of a real-valued function yields a gradient $\nabla F(x)$, and the Fréchet derivative is the continuous linear map

$$
v\mapsto \langle \nabla F(x),v\rangle.
$$

The proof records this as `hFGradient`. The `simpa [innerSL_apply_apply]` step only rewrites the Lean representation of the inner-product functional; mathematically it identifies the Fréchet derivative with the inner product against the gradient.

The proof then uses the assumption that $u$ is $C^3$. From this it obtains differentiability of $u$, differentiability of $\dot u$, and differentiability of $\ddot u$. Concretely, $u\in C^3$ implies $u\in C^2$, so $\dot u$ is differentiable; and $u\in C^3$ implies $\dot u\in C^2$, so $\ddot u$ is differentiable. These are the facts `huDiff`, `hFirstDiff`, and `hSecondDiff`.

Using these differentiability facts, the proof assembles the derivative regularity triple `hRegularity`:

$$
\forall t,\ t_0\le t,\quad
u'(t)=\dot u(t),
$$

$$
\forall t,\ t_0\le t,\quad
\dot u'(t)=\ddot u(t),
$$

$$
\forall t,\ t_0\le t,\quad
\ddot u'(t)=\dddot u(t).
$$

The proof splits the triple conjunction with `refine ⟨?_, ?_, ?_⟩`. For each component it introduces $t$ and ignores the side condition $t_0\le t$, because the differentiability statements hold for every real $t$. Then `(huDiff t).hasDerivAt`, `(hFirstDiff t).hasDerivAt`, and `(hSecondDiff t).hasDerivAt` provide the three `HasDerivAt` facts. The tactic `intro` introduces the variable and hypothesis, and `exact` closes each goal by the corresponding differentiability-to-derivative result.

Finally, the proof applies the core theorem `togesVR_rate_and_weak_convergence_core`. It supplies:
- the first derivative function $\dot u$,
- the second derivative function $\ddot u$,
- the third derivative function $\dddot u$,
- the envelope gradient $\nabla F$,
- the original assumptions `hLam`, `hProper`, `hlsc`, `hConvex`, `hArgmin`, `hProx`, `hFConvex`, `hFGradient`, `hFMin`, `hFInf`, and `ht0pos`,
- the derivative regularity facts `hRegularity.1`, `hRegularity.2.1`, and `hRegularity.2.2`,
- the compatibility condition between the chosen derivative functions and the derivatives of $u$, supplied by

  $$
  \langle \mathrm{rfl},\mathrm{rfl},\mathrm{rfl}\rangle,
  $$

  which proves the equalities

  $$
  \dot u(t)=\dot u(t),\qquad
  \ddot u(t)=\ddot u(t),\qquad
  \dddot u(t)=\dddot u(t)
  $$

  by reflexivity,
- the auxiliary asymptotic hypothesis `hAuxiliaryStrict`,
- the TOGES-V trajectory hypothesis `hTrajectory`.

The core theorem already has exactly the desired conclusion: for $\alpha\ge 3$, a constant $C\ge 0$ giving the four $O(t^{-3})$ bounds; for $\alpha>3$, four $o(t^{-3})$ bounds, weak convergence of $u(t)$ to some $u_\infty$, and the minimizer identity $f(u_\infty)=\inf f$. Therefore the final `exact` command closes the target theorem by directly providing the core theorem’s specialized conclusion. No `rw` or `linarith` step occurs in this proof; the only simplification is the `simpa` conversion of the gradient representation into the corresponding Fréchet derivative.

