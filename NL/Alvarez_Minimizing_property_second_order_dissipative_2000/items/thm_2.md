## Source file
`Alvarez_Minimizing_property_second_order_dissipative_2000/items/thm_2.lean`

## Lean statement
```lean
theorem scalar_damped_strong_convergence {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    (hcase : ((argmin Phi (potential_range_bddBelow hPhi)).Nonempty ∧ IsEvenFunction Phi) ∨
      (interior (argmin Phi (potential_range_bddBelow hPhi))).Nonempty) :
    ∃ uhat ∈ argmin Phi (potential_range_bddBelow hPhi), Tendsto sys.u atTop (nhds uhat)
```

## Statement explanation
The declaration concerns a complete real inner product space $H$ (a real Hilbert space), a real damping coefficient $\gamma$, a potential $\Phi:H\to\mathbb R$, a gradient map $\operatorname{grad}\Phi:H\to H$, and initial data $u_0,v_0\in H$. It assumes a bundled potential hypothesis `hPhi : HasPotentialAssumption Phi`. The proof uses the consequences of this hypothesis that $\Phi$ is $C^1$, convex on all of $H$, bounded below, that its range is bounded below, and that its infimum is a lower bound for every value of $\Phi$. It also assumes a dissipative second-order system `sys : DissipativeSystem gamma Phi gradPhi u0 v0`, whose trajectory is denoted $u(t)=\text{sys.u}(t)$. From the system the proof uses that $\operatorname{grad}\Phi$ is a gradient of $\Phi$, that the trajectory has the needed smoothness, and that $\gamma>0$.

The set

$$
\operatorname{argmin}\Phi
=
\{x\in H:\Phi(x)=\inf \Phi(H)\}
$$

is the set of global minimizers of $\Phi$; in Lean it is written `argmin Phi (potential_range_bddBelow hPhi)`, where the second argument is the proof that the range of $\Phi$ is bounded below. The hypothesis `hcase` is a disjunction of two alternatives. The first alternative says that the minimizer set is nonempty and that $\Phi$ is an even function. The second alternative says that the interior of the minimizer set is nonempty.

The conclusion is that there exists a minimizer $u_\ast\in\operatorname{argmin}\Phi$ such that

$$
u(t)\to u_\ast
$$

strongly in norm as $t\to\infty$, i.e. `Tendsto sys.u atTop (nhds uhat)`. Thus the theorem asserts strong convergence of the trajectory of the dissipative system to a global minimizer of the potential, under either the even-potential-with-minimizer hypothesis or the interior-minimizer hypothesis.

## Lean proof
```lean
by
  rcases hcase with hEven | hInterior
  · rcases hEven with ⟨hMin, hPhiEven⟩
    simpa only [proof_irrel_heq] using
      (scalar_damped_even_strong_convergence_result hPhi.contDiff hPhi.convex hPhi.bounded_below
        sys hMin hPhiEven)
  · obtain ⟨z0, rho, hrho, hball⟩ := interior_argmin_closedBall hPhi hInterior
    have hradial : ∀ x : H, rho * ‖gradPhi x‖ ≤ ⟪gradPhi x, x - z0⟫_ℝ :=
      fun x => gradient_radial_lower_bound_of_argmin_closedBall hPhi sys.is_gradient hrho hball x
    obtain ⟨hvel2, hvel0, hPhi0, hweak⟩ := scalar_damped_minimizing_property hPhi sys
    have hz0min : z0 ∈ argmin Phi (potential_range_bddBelow hPhi) :=
      hball (Metric.mem_closedBall_self (le_of_lt hrho))
    have hz0value : Phi z0 = sInf (Set.range Phi) := hz0min
    have hdistance_ineq : ∀ ⦃t : ℝ⦄, 0 < t →
        deriv (deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2)) t +
            gamma * deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2) t ≤
          ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
      intro t ht
      have h := scalar_distance_damped_ineq_local hPhi sys z0 ht
      have hgap : Phi z0 - Phi (sys.u t) ≤ 0 := by
        rw [hz0value]
        linarith [potential_sInf_le hPhi (sys.u t)]
      linarith
    have hphiLimit : ∃ L : ℝ, Tendsto
        (fun s => (1 / 2 : ℝ) * ‖sys.u (s + 1) - z0‖ ^ 2) atTop (nhds L) :=
      shifted_distance_converges sys hvel2 hdistance_ineq
    have haccelIneq : ∀ ⦃t : ℝ⦄, 0 < t →
        rho * ‖fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t 1 +
            gamma • fderiv ℝ sys.u t 1‖ ≤
          -deriv (deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2)) t +
            ‖fderiv ℝ sys.u t 1‖ ^ 2 -
              gamma * deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2) t :=
      fun _ ht => radial_distance_acceleration_ineq sys hradial ht
    let phi : ℝ → ℝ := fun s => (1 / 2 : ℝ) * ‖sys.u s - z0‖ ^ 2
    rcases hphiLimit with ⟨L, hphiTail⟩
    have hshift : Tendsto (fun t : ℝ => t - 1) atTop atTop := by
      simpa only [sub_eq_add_neg] using
        (tendsto_atTop_add_const_right atTop (-1) tendsto_id)
    have hphi : Tendsto phi atTop (nhds L) := by
      convert hphiTail.comp hshift using 1
      ext t
      simp [phi]
    have hdist : Tendsto (fun t => ‖sys.u t - z0‖) atTop
        (nhds (Real.sqrt (2 * L))) := by
      have htwo : Tendsto (fun t => 2 * phi t) atTop (nhds (2 * L)) :=
        tendsto_const_nhds.mul hphi
      have hsqrt := (Real.continuous_sqrt.tendsto (2 * L)).comp htwo
      convert hsqrt using 1
      ext t
      simp only [Function.comp_apply, phi]
      rw [show 2 * (1 / 2 * ‖sys.u t - z0‖ ^ 2) = ‖sys.u t - z0‖ ^ 2 by ring,
        Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hderiv0 : Tendsto (fun t => deriv phi t) atTop (nhds 0) := by
      have hprod : Tendsto (fun t => ‖sys.u t - z0‖ * ‖fderiv ℝ sys.u t 1‖)
          atTop (nhds 0) := by
        simpa using hdist.mul hvel0.norm
      apply tendsto_zero_iff_norm_tendsto_zero.mpr
      apply squeeze_zero' (Filter.Eventually.of_forall fun t => abs_nonneg _) ?_ hprod
      filter_upwards [Ioi_mem_atTop (0 : ℝ)] with t ht
      rw [show deriv phi t = ⟪sys.u t - z0, fderiv ℝ sys.u t 1⟫_ℝ by
        simpa only [phi] using (scalar_damped_distance_hasDerivAt (z0 := z0) sys ht).deriv]
      exact abs_real_inner_le_norm _ _
    let q : ℝ → ℝ := fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2
    let r : ℝ → H := fun t => fderiv ℝ (fun s => fderiv ℝ sys.u s 1) t 1 +
      gamma • fderiv ℝ sys.u t 1
    let V : ℝ := ∫ t in Set.Ici 0, q t
    have hq_nonneg : ∀ t : ℝ, 0 ≤ q t := fun t => sq_nonneg _
    have hqint : IntegrableOn q (Set.Ici 0) := by simpa only [q] using hvel2
    have hq_bound : ∀ n : ℕ, (∫ t in 1..(n + 1 : ℝ), q t) ≤ V := by
      intro n
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      rw [intervalIntegral.integral_of_le hn]
      exact setIntegral_mono_set hqint
        (Filter.Eventually.of_forall fun t => hq_nonneg t)
        (Filter.Eventually.of_forall fun t ht =>
          show t ∈ Set.Ici 0 from
            le_trans (show (0 : ℝ) ≤ 1 by norm_num) (le_of_lt ht.1))
    have hlocal : ∀ n : ℕ, IntegrableOn r (Set.Ioc 1 (n + 1 : ℝ)) := by
      intro n
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have hu : ContDiffOn ℝ 2 sys.u (Set.Icc 1 (n + 1 : ℝ)) :=
        sys.contDiff.mono (fun s hs => le_trans (by norm_num) hs.1)
      have hv : ContDiffOn ℝ 1 (fun s => fderiv ℝ sys.u s 1) (Set.Icc 1 (n + 1 : ℝ)) := by
        intro s hs
        have hlocal := sys.contDiff.contDiffAt
          (Ici_mem_nhds (lt_of_lt_of_le (by norm_num) hs.1))
        exact ((hlocal.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
          (contDiffAt_const (c := (1 : ℝ)))).contDiffWithinAt
      have ha : ContinuousOn (fun s => fderiv ℝ (fun t => fderiv ℝ sys.u t 1) s 1)
          (Set.Icc 1 (n + 1 : ℝ)) := by
        intro s hs
        have hlocal := sys.contDiff.contDiffAt
          (Ici_mem_nhds (lt_of_lt_of_le (by norm_num) hs.1))
        have hvlocal := (hlocal.fderiv_right
          (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
            (contDiffAt_const (c := (1 : ℝ)))
        exact ((hvlocal.fderiv_right (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)).clm_apply
          (contDiffAt_const (c := (1 : ℝ)))).continuousAt.continuousWithinAt
      exact (ha.add (continuousOn_const.smul hv.continuousOn)).integrableOn_Icc.mono_set
        Set.Ioc_subset_Icc_self
    have hbound : ∀ᶠ n : ℕ in atTop, (∫ t in 1..(n + 1 : ℝ), ‖r t‖) ≤
        (deriv phi 1 + 1 + V + gamma * phi 1) / rho := by
      have hTendsto' : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
        tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      have hdshift := hderiv0.comp hTendsto'
      rcases (Metric.tendsto_atTop.mp hdshift 1 zero_lt_one) with ⟨N, hN⟩
      filter_upwards [Ioi_mem_atTop N] with n hn
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hnat : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith
      have hsmall : |deriv phi ((n : ℝ) + 1)| ≤ 1 := by
        have := hN n (le_of_lt hn)
        simpa [Real.dist_eq] using this.le
      have hrad := radial_acceleration_interval_bound sys haccelIneq hnat
      have hphiT : 0 ≤ phi ((n : ℝ) + 1) := by
        dsimp [phi]
        positivity
      have hvel := hq_bound n
      apply (le_div_iff₀ hrho).2
      rw [mul_comm]
      change rho * (∫ t in 1..(n + 1 : ℝ), ‖r t‖) ≤
        deriv phi 1 + 1 + V + gamma * phi 1
      have hneg : -deriv phi ((n : ℝ) + 1) ≤ 1 := by
        linarith [neg_le_of_abs_le hsmall]
      have hgamma : 0 < gamma := sys.gamma_pos
      simpa only [r, q, phi] using (le_trans hrad (by nlinarith))
    have hTendsto : Tendsto (fun n : ℕ => (n + 1 : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
    have hrint : IntegrableOn r (Set.Ioi 1) :=
      integrableOn_Ioi_of_intervalIntegral_norm_bounded _ 1 hlocal hTendsto hbound
    have hw : Tendsto (fun t => fderiv ℝ sys.u t 1 + gamma • sys.u t) atTop
        (nhds (limUnder atTop (fun t => fderiv ℝ sys.u t 1 + gamma • sys.u t))) := by
      apply tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi (f' := r) ?_ hrint
      intro t ht
      have ht0 : 0 < t := lt_trans (by norm_num) ht
      have hu : HasDerivAt sys.u (fderiv ℝ sys.u t 1) t :=
        (dissipativeSystem_differentiableAt_pos sys ht0).hasDerivAt
      convert (dissipativeSystem_velocity_hasDerivAt_pos sys ht0).add
        ((hasDerivAt_const t gamma).smul hu) using 1
      all_goals simp [r]
    let wLim : H := limUnder atTop (fun t => fderiv ℝ sys.u t 1 + gamma • sys.u t)
    have huLim : Tendsto sys.u atTop (nhds (gamma⁻¹ • wLim)) := by
      have hsub := hw.sub hvel0
      have hscaled :=
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => (gamma⁻¹ : ℝ)) atTop
          (nhds (gamma⁻¹ : ℝ))).smul hsub
      simpa only [wLim, sub_zero, smul_sub, smul_add, smul_smul,
        inv_mul_cancel₀ (ne_of_gt sys.gamma_pos), one_smul, add_sub_cancel_left] using hscaled
    have hMin : (argmin Phi (potential_range_bddBelow hPhi)).Nonempty := ⟨z0, hz0min⟩
    rcases hweak hMin with ⟨uhat, huhat, hweakU⟩
    have huWeak : Tendsto (fun t => toWeakSpace ℝ H (sys.u t)) atTop
        (nhds (toWeakSpace ℝ H (gamma⁻¹ • wLim))) :=
      (toWeakSpaceCLM ℝ H).continuous.tendsto _ |>.comp huLim
    have heq : gamma⁻¹ • wLim = uhat :=
      (toWeakSpace ℝ H).injective (tendsto_nhds_unique huWeak hweakU)
    exact ⟨uhat, huhat, heq ▸ huLim⟩
```

## Proof explanation
The proof splits on `hcase` using `rcases hcase with hEven | hInterior`.

In the first case, $hEven$ consists of a proof $hMin$ that $\operatorname{argmin}\Phi$ is nonempty and a proof $hPhiEven$ that $\Phi$ is even. The proof then applies the previously established theorem `scalar_damped_even_strong_convergence_result`. That theorem states that if $\Phi$ is $C^1$, convex, bounded below, if the system `sys` is dissipative, if the minimizer set is nonempty, and if $\Phi$ is even, then there exists a minimizer $u_\ast$ such that $u(t)\to u_\ast$ strongly. The proof supplies exactly those hypotheses: `hPhi.contDiff` for $C^1$-smoothness, `hPhi.convex` for convexity, `hPhi.bounded_below` for boundedness below, `sys`, `hMin`, and `hPhiEven`. The `simpa only [proof_irrel_heq]` step reconciles the proof argument inside `argmin`: the bounded-below proof used by the theorem may be definitionally different from the one in the current goal, but proofs of propositions are irrelevant, so the result matches the desired conclusion.

In the second case, the hypothesis is that the interior of the minimizer set is nonempty. The theorem `interior_argmin_closedBall` is invoked. Its statement is: if $\Phi$ satisfies the potential assumption and the interior of $\operatorname{argmin}\Phi$ is nonempty, then there exist $z_0\in H$ and $\rho>0$ such that

$$
\overline{B}(z_0,\rho)\subseteq \operatorname{argmin}\Phi .
$$

Thus `obtain ⟨z0, rho, hrho, hball⟩` produces a point $z_0$ and a positive radius $\rho$ whose closed ball lies entirely in the minimizer set.

Next the proof establishes the radial gradient inequality

$$
\rho\,\|\operatorname{grad}\Phi(x)\|\le \langle \operatorname{grad}\Phi(x),x-z_0\rangle_{\mathbb R}
$$

for every $x\in H$. This is exactly the conclusion of `gradient_radial_lower_bound_of_argmin_closedBall`, applied with `hPhi`, the gradient relation `sys.is_gradient`, the positivity `hrho`, the inclusion `hball`, and the arbitrary point $x$. Mathematically, because the closed ball around $z_0$ lies in the minimizer set, the gradient direction at any point cannot point back toward that ball too strongly; rather, its inner product with $x-z_0$ dominates $\rho$ times its norm. This inequality is named `hradial`.

The theorem `scalar_damped_minimizing_property hPhi sys` is then invoked. It returns four facts:

$$
\int_0^\infty \|u'(t)\|^2\,dt<\infty,
$$

$$
u'(t)\to 0,
$$

$$
\Phi(u(t))\to \inf \Phi(H),
$$

and, if the minimizer set is nonempty, weak convergence of $u(t)$ to some minimizer in the weak space. The proof stores these as `hvel2`, `hvel0`, `hPhi0`, and `hweak`. The later argument mainly uses `hvel2`, `hvel0`, and `hweak`.

Since $z_0\in \overline{B}(z_0,\rho)$ and the closed ball is contained in $\operatorname{argmin}\Phi$, the proof obtains `hz0min : z0 ∈ argmin Phi ...`. From the definition of `argmin`, membership means

$$
\Phi(z_0)=\inf \Phi(H),
$$

which is recorded as `hz0value`.

The proof then derives the differential inequality

$$
\frac{d^2}{dt^2}\left(\frac12\|u(t)-z_0\|^2\right)
+
\gamma\frac{d}{dt}\left(\frac12\|u(t)-z_0\|^2\right)
\le
\|u'(t)\|^2
$$

for every $t>0$. First it applies `scalar_distance_damped_ineq_local`, which gives

$$
\frac{d^2}{dt^2}\left(\frac12\|u(t)-z_0\|^2\right)
+
\gamma\frac{d}{dt}\left(\frac12\|u(t)-z_0\|^2\right)
\le
\Phi(z_0)-\Phi(u(t))+\|u'(t)\|^2.
$$

Then it uses `potential_sInf_le hPhi (sys.u t)`, which says

$$
\inf \Phi(H)\le \Phi(u(t)).
$$

Since $\Phi(z_0)=\inf \Phi(H)$, the potential gap satisfies

$$
\Phi(z_0)-\Phi(u(t))\le 0.
$$

Adding this to the previous inequality gives the desired bound, and `linarith` discharges the arithmetic comparison.

With this differential inequality and the integrability `hvel2`, the theorem `shifted_distance_converges` gives the existence of a real number $L$ such that

$$
\frac12\|u(s+1)-z_0\|^2\to L
\qquad (s\to\infty).
$$

This is stored as `hphiLimit`.

The proof also records the acceleration inequality. From `radial_distance_acceleration_ineq sys hradial ht`, for every $t>0$,

$$
\rho\left\|u''(t)+\gamma u'(t)\right\|
\le
-\frac{d^2}{dt^2}\left(\frac12\|u(t)-z_0\|^2\right)
+
\|u'(t)\|^2
-
\gamma\frac{d}{dt}\left(\frac12\|u(t)-z_0\|^2\right).
$$

This inequality controls the size of the damped acceleration $u''+\gamma u'$ in terms of derivatives of the squared distance and the squared velocity.

The proof now defines

$$
\phi(t)=\frac12\|u(t)-z_0\|^2.
$$

From `hphiLimit`, the shifted function $\phi(s+1)$ converges to $L$. The proof introduces the shift $s\mapsto s-1$, which tends to infinity, and composes `hphiTail` with it. The `convert` and `ext` steps identify $\phi((s-1)+1)=\phi(s)$. Hence

$$
\phi(t)\to L.
$$

Then $2\phi(t)=\|u(t)-z_0\|^2$. Using continuity of the square root and the identity $\sqrt{x^2}=|x|$, together with nonnegativity of the norm, the proof obtains

$$
\|u(t)-z_0\|\to \sqrt{2L}.
$$

This is `hdist`.

Next the proof shows that the derivative of $\phi$ tends to zero:

$$
\phi'(t)\to 0.
$$

For $t>0$, `scalar_damped_distance_hasDerivAt` gives

$$
\phi'(t)=\langle u(t)-z_0,u'(t)\rangle_{\mathbb R}.
$$

By Cauchy–Schwarz,

$$
|\phi'(t)|\le \|u(t)-z_0\|\,\|u'(t)\|.
$$

The right-hand side is the product of a sequence tending to $\sqrt{2L}$ and a sequence tending to $0$, hence tends to $0$. The proof uses `squeeze_zero'` with this product as the dominating sequence. Thus `hderiv0` is established.

The proof then defines

$$
q(t)=\|u'(t)\|^2,
\qquad
r(t)=u''(t)+\gamma u'(t),
\qquad
V=\int_0^\infty q(t)\,dt.
$$

The function $q$ is nonnegative and, by `hvel2`, integrable on $[0,\infty)$. For every natural number $n$, the interval integral satisfies

$$
\int_1^{n+1} q(t)\,dt\le V,
$$

because $q\ge0$ and $[1,n+1]\subseteq[0,\infty)$. This is `hq_bound`.

The proof also proves local integrability of $r$ on every finite interval $(1,n+1]$. It uses the smoothness field `sys.contDiff` to obtain $C^2$-smoothness of $u$ on compact intervals, hence continuity of $u'$, $u''$, and therefore of $r$. Thus `hlocal` says that for every $n$,

$$
r\in L^1((1,n+1]).
$$

The key uniform estimate is `hbound`. It states that eventually in $n$,

$$
\int_1^{n+1}\|r(t)\|\,dt
\le
\frac{\phi'(1)+1+V+\gamma\phi(1)}{\rho}.
$$

To obtain it, the proof uses the convergence $\phi'(t)\to0$. Along the sequence $t=n+1$, for all sufficiently large $n$,

$$
|\phi'(n+1)|\le 1.
$$

For such $n$, the interval form of the acceleration inequality, `radial_acceleration_interval_bound`, gives

$$
\rho\int_1^{n+1}\|r(t)\|\,dt
\le
\phi'(1)-\phi'(n+1)
+
\int_1^{n+1} q(t)\,dt
+
\gamma\bigl(\phi(1)-\phi(n+1)\bigr).
$$

Now $-\phi'(n+1)\le1$, the $q$-integral is at most $V$, and $\phi(n+1)\ge0$, so

$$
\phi'(1)-\phi'(n+1)
+
\int_1^{n+1} q(t)\,dt
+
\gamma(\phi(1)-\phi(n+1))
\le
\phi'(1)+1+V+\gamma\phi(1).
$$

Since $\rho>0$, dividing by $\rho$ gives the displayed bound. The tactic `nlinarith` handles the final arithmetic combination of these inequalities.

From `hlocal`, the eventual uniform bound `hbound`, and the fact that $n+1\to\infty$, the theorem `integrableOn_Ioi_of_intervalIntegral_norm_bounded` yields

$$
r\in L^1((1,\infty)).
$$

That is, the damped acceleration $u''+\gamma u'$ is integrable on the tail $(1,\infty)$.

The proof then considers the function

$$
w(t)=u'(t)+\gamma u(t).
$$

For $t>1$, hence $t>0$, the theorems `dissipativeSystem_differentiableAt_pos` and `dissipativeSystem_velocity_hasDerivAt_pos` give the derivatives of $u$ and of $u'$. Specifically,

$$
u'(t)=fderiv_{\mathbb R}u(t)(1),
$$

and the velocity map $t\mapsto u'(t)$ has derivative $u''(t)$. Therefore

$$
w'(t)=u''(t)+\gamma u'(t)=r(t).
$$

Since $r\in L^1((1,\infty))$, the theorem `tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi` gives

$$
w(t)\to \operatorname{limUnder}_{t\to\infty} w(t).
$$

The proof names this limit `wLim`. Thus

$$
u'(t)+\gamma u(t)\to wLim.
$$

From `hvel0`, the velocity satisfies $u'(t)\to0$. Subtracting this limit from the convergence of $w$ gives

$$
\gamma u(t)=(u'(t)+\gamma u(t))-u'(t)\to wLim.
$$

Since $\gamma>0$, it is invertible, and multiplying by $\gamma^{-1}$ gives

$$
u(t)\to \gamma^{-1}wLim.
$$

This is `huLim`.

At this point the proof returns to the weak convergence obtained earlier. Since $z_0\in\operatorname{argmin}\Phi$, the minimizer set is nonempty, so `hweak hMin` produces some

$$
u_\ast\in\operatorname{argmin}\Phi
$$

such that

$$
\text{toWeakSpace}_{\mathbb R,H}(u(t))\to \text{toWeakSpace}_{\mathbb R,H}(u_\ast)
$$

weakly. On the other hand, the strong convergence $u(t)\to\gamma^{-1}wLim$ implies weak convergence to the same point, because the embedding `toWeakSpace ℝ H` is continuous. Therefore the weak limit $\text{toWeakSpace}_{\mathbb R,H}(\gamma^{-1}wLim)$ equals $\text{toWeakSpace}_{\mathbb R,H}(u_\ast)$. Since `toWeakSpace ℝ H` is injective, this gives

$$
\gamma^{-1}wLim=u_\ast.
$$

Rewriting the strong limit with this equality, the proof concludes

$$
u(t)\to u_\ast
$$

with $u_\ast\in\operatorname{argmin}\Phi$, which is exactly the desired strong convergence statement.

