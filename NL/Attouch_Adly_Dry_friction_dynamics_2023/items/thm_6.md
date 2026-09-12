## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/thm_6.lean`

## Lean statement
```lean
theorem theorem_4_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {s₀ r α : ℝ} (hr : 0 < r) (hα : 1 < α) (hs₀ : 0 < s₀)
    (f : H → ℝ) (hf : ContDiff ℝ 2 f)
    (x p z : ℝ → H) (hx : ContDiff ℝ 2 x) (hz : ContDiff ℝ 2 z)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgradient_lip_on_bounded : ∀ R : ℝ, ∃ L : NNReal,
      LipschitzOnWith L (gradient f) (Metric.closedBall 0 R))
    (hmin : ∃ xstar : H, ∀ u : H, f xstar ≤ f u)
    (hsolution : IsDryStarTrajectory r α s₀ f x p)
    (hsol : IsDrygradTrajectory r f z (s₀ ^ 2 / (2 * (α - 1))))
    (hbridge_initial : x s₀ = z (s₀ ^ 2 / (2 * (α - 1))))
    (hbridge_relation : ∀ s ∈ Set.Ici s₀,
      z (s ^ 2 / (2 * (α - 1))) =
        x s + (s / (α - 1)) • deriv x s)
    (hinitial : r < ‖gradient f (z (s₀ ^ 2 / (2 * (α - 1))))‖) :
    Filter.Tendsto (fun s : ℝ => s * ‖deriv x s‖) Filter.atTop (nhds 0) ∧
      MeasureTheory.IntegrableOn (fun s => ‖deriv x s‖) (Set.Ici s₀) ∧
      ∃ xLimit, Filter.Tendsto x Filter.atTop (nhds xLimit) ∧
        ‖gradient f xLimit‖ = r
```

## Statement explanation
Let \(H\) be a real Hilbert space. The theorem is stated for real parameters \(s_0,r,\alpha\in\mathbb R\) satisfying \(r>0\), \(\alpha>1\), and \(s_0>0\). The potential is a function \(f:H\to\mathbb R\), assumed to be \(C^2\), convex on all of \(H\), to have a global minimizer, and to have a gradient \(\nabla f\) that is Lipschitz on every closed ball centered at \(0\): for every real \(R\) there is a nonnegative constant \(L\) such that \(\nabla f\) is \(L\)-Lipschitz on \(\overline B(0,R)\). The hypothesis `hmin` says that there exists \(x_\star\in H\) with \(f(x_\star)\le f(u)\) for every \(u\in H\), so \(f\) has a global minimum, hence a global lower bound.

There are three curves \(x,p,z:\mathbb R\to H\), with \(x\) and \(z\) assumed \(C^2\). The hypothesis `hsolution` says that \(x,p\) form a dry-star trajectory with friction \(r\), parameter \(\alpha\), initial time \(s_0\), and potential \(f\). Its internal definition is not expanded in the proof. The hypothesis `hsol` says that \(z\) is a dry-gradient trajectory for \(f\) with friction \(r\) at the initial time
\[
t_0=\frac{s_0^2}{2(\alpha-1)}.
\]
The two bridge hypotheses connect \(x\) and \(z\). First,
\[
x(s_0)=z\!\left(\frac{s_0^2}{2(\alpha-1)}\right).
\]
Second, for every \(s\ge s_0\),
\[
z\!\left(\frac{s^2}{2(\alpha-1)}\right)
=
x(s)+\frac{s}{\alpha-1}\operatorname{deriv}x(s).
\]
Finally, the initial friction condition is
\[
r<\left\|\nabla f\!\left(z\!\left(\frac{s_0^2}{2(\alpha-1)}\right)\right)\right\|.
\]

The conclusion is the conjunction of three statements. First, the weighted velocity of \(x\) vanishes at infinity:
\[
s\|\operatorname{deriv}x(s)\|\longrightarrow 0
\quad\text{as }s\to\infty.
\]
Second, the speed \(\|\operatorname{deriv}x\|\) is integrable on \([s_0,\infty)\). Third, there exists a limit point \(x_\infty\in H\) such that
\[
x(s)\to x_\infty\quad\text{as }s\to\infty,
\]
and its gradient norm equals the friction threshold:
\[
\|\nabla f(x_\infty)\|=r.
\]
Thus the theorem says that the time-scaled bridge relation transfers the long-time behavior of the dry-gradient trajectory \(z\) to the dry-star trajectory \(x\), giving convergence of \(x\) to a point where the gradient norm is exactly \(r\).

## Lean proof
```lean
by
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hz_diff : Differentiable ℝ z := hz.differentiable (by norm_num)
  have hgradient_lip : LocallyLipschitz (gradient f) := by
    intro u
    obtain ⟨L, hL⟩ := hgradient_lip_on_bounded (‖u‖ + 1)
    refine ⟨L, Metric.ball u 1, Metric.ball_mem_nhds u zero_lt_one, hL.mono ?_⟩
    intro v hv
    have hvdist : dist v u < 1 := by simpa [Metric.mem_ball] using hv
    have hvdist' : ‖v - u‖ < 1 := by simpa [dist_eq_norm] using hvdist
    have hvnorm : ‖v‖ ≤ ‖u‖ + 1 := by
      have htri : ‖v‖ ≤ ‖v - u‖ + ‖u‖ := by
        calc
          ‖v‖ = ‖(v - u) + u‖ := by congr 1; abel
          _ ≤ ‖v - u‖ + ‖u‖ := norm_add_le _ _
      exact (lt_of_le_of_lt htri (by linarith)).le
    simpa [frictionBall, dist_zero_right] using hvnorm
  obtain ⟨xstar, hxstar⟩ := hmin
  have hlower : ∃ m : ℝ, ∀ u : H, m ≤ f u := ⟨f xstar, hxstar⟩
  have hzrate := theorem_3_1 hr f z hf hconvex hsol hlower hgradient_lip hz hinitial
  have hzmain := theorem_2_1 hr f z hf₁ hlower hgradient_lip hz_diff hinitial hsol
  obtain ⟨y, hy, haverage⟩ := reverse_time_scaling_average hα hs₀ x z hx
    hbridge_initial hbridge_relation
  obtain ⟨dy, hdy, hydrate, hydyint⟩ := time_scale_velocity_transfer
    hα hs₀ z y hz hy hzrate.2 hzmain.2.2.1
  have hxt := weighted_average_velocity_transfer hα hs₀ x y (deriv x) dy
    haverage hdy hydrate hydyint
  obtain ⟨zLimit, hzLimit, hzGrad, _⟩ := hzmain.2.2.2
  have hyLimit : Filter.Tendsto y Filter.atTop (nhds zLimit) := by
    have hden : 0 < 2 * (α - 1) := mul_pos (by norm_num) (sub_pos.mpr hα)
    have hτ : Filter.Tendsto
        (fun s : ℝ => s ^ 2 / (2 * (α - 1))) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop.2 ?_
      intro b
      filter_upwards [Filter.eventually_atTop.2
        ⟨max 1 (2 * (α - 1) * b), fun s hs => hs⟩] with s hs
      have hs1 : 1 ≤ s := le_trans (le_max_left _ _) hs
      have hsq : s ≤ s ^ 2 := by nlinarith
      have hsb : 2 * (α - 1) * b ≤ s := le_trans (le_max_right _ _) hs
      apply (le_div_iff₀ hden).2
      nlinarith
    rw [hy]
    exact hzLimit.comp hτ
  have hxLimit := weighted_average_limit_transfer hα hs₀ x y (deriv x) zLimit
    haverage hyLimit
  refine ⟨hxt.1, hxt.2, zLimit, hxLimit, ?_⟩
  exact hzGrad
```

## Proof explanation
The proof first records several consequences of the regularity hypotheses. Since \(f\) is \(C^2\), it is in particular \(C^1\); this is the purpose of the line defining `hf₁`, using the fact that \(1\le 2\). Similarly, since \(z\) is \(C^2\), it is differentiable, giving `hz_diff`. These weaker regularity facts are needed for `theorem_2_1`, which assumes only \(C^1\) for \(f\) and differentiability for \(z\).

Next, the proof derives that \(\nabla f\) is locally Lipschitz from the stronger hypothesis that it is Lipschitz on every closed ball centered at \(0\). To prove local Lipschitzness at a point \(u\), the argument applies `hgradient_lip_on_bounded` with radius \(\|u\|+1\), obtaining a nonnegative constant \(L\) and the statement that \(\nabla f\) is \(L\)-Lipschitz on \(\overline B(0,\|u\|+1)\). The neighborhood chosen around \(u\) is the open ball \(B(u,1)\). If \(v\in B(u,1)\), then
\[
\|v-u\|<1.
\]
Using \(v=(v-u)+u\) and the triangle inequality,
\[
\|v\|\le \|v-u\|+\|u\|<\|u\|+1.
\]
Hence \(v\in \overline B(0,\|u\|+1)\). The `linarith` tactic closes the final linear inequality, and the `simpa` step converts the norm inequality into membership in the closed ball, using the definition of `frictionBall` and \(dist(v,0)=\|v\|\). Thus \(\nabla f\) is locally Lipschitz. The proof also extracts a global minimizer \(x_\star\) from `hmin` and uses it to obtain the lower bound \(f(x_\star)\le f(u)\) for all \(u\).

The main analytic input for \(z\) is `theorem_3_1`, invoked as `hzrate`. In the present variables, that theorem applies to the dry-gradient trajectory \(z\) at
\[
t_0=\frac{s_0^2}{2(\alpha-1)}.
\]
It assumes \(r>0\), \(f\) convex and \(C^2\), \(z\) a dry-gradient trajectory, a lower bound for \(f\), local Lipschitzness of \(\nabla f\), \(z\) of class \(C^2\), and the initial inequality
\[
r<\|\nabla f(z(t_0))\|.
\]
Its conclusion is that \(t\mapsto\|\operatorname{deriv}z(t)\|\) is nonincreasing on \([t_0,\infty)\) and that
\[
t\|\operatorname{deriv}z(t)\|\to 0\quad\text{as }t\to\infty.
\]
The proof uses the second component, `hzrate.2`, as the weighted velocity estimate for \(z\).

The proof then invokes `theorem_2_1` as `hzmain`. This theorem assumes \(r>0\), \(f\) of class \(C^1\), a lower bound for \(f\), local Lipschitzness of \(\nabla f\), differentiability of \(z\), the dry-gradient trajectory condition, and the same initial inequality. It concludes that \(t\mapsto f(z(t))\) is nonincreasing on \([t_0,\infty)\), that \(\|\operatorname{deriv}z\|^2\) and \(\|\operatorname{deriv}z\|\) are integrable on \([t_0,\infty)\), and that there exists \(z_\infty\in H\) such that
\[
z(t)\to z_\infty\quad\text{as }t\to\infty,
\qquad
\|\nabla f(z_\infty)\|=r,
\]
together with a final alternative which is not needed here. From this result the proof later uses `hzmain.2.2.1`, the integrability of \(\|\operatorname{deriv}z\|\) on \([t_0,\infty)\), and `hzmain.2.2.2`, the existence of the limit point \(z_\infty\) with the gradient-norm equality.

Next the proof applies `reverse_time_scaling_average`. This theorem assumes \(\alpha>1\), \(s_0>0\), \(x,z\) of class \(C^2\), the initial bridge equality, and the bridge relation
\[
z\!\left(\frac{s^2}{2(\alpha-1)}\right)
=
x(s)+\frac{s}{\alpha-1}\operatorname{deriv}x(s)
\quad(s\ge s_0).
\]
It produces a curve \(y:\mathbb R\to H\) such that
\[
y=\operatorname{timeScaledTrajectory} z\!\left(s\mapsto \frac{s^2}{2(\alpha-1)}\right)
\]
and such that the weighted-average predicate
\[
\operatorname{IsWeightedAverageOn}
\left(s\mapsto \frac{s^2}{2(\alpha-1)}\right)
\left(s\mapsto \frac{s}{\alpha-1}\right)
x\,y\,(\operatorname{deriv}x)\,s_0
\]
holds. In other words, \(y(s)=z(s^2/(2(\alpha-1)))\), and this curve satisfies the weighted-average relation with \(x\) and \(\operatorname{deriv}x\).

Using this \(y\), the proof applies `time_scale_velocity_transfer`. That theorem takes \(z\), \(y\), the equality \(y=\operatorname{timeScaledTrajectory} z\,\varphi\) for
\[
\varphi(s)=\frac{s^2}{2(\alpha-1)},
\]
the weighted velocity limit for \(z\), and the integrability of \(\|\operatorname{deriv}z\|\) on the image interval \([\varphi(s_0),\infty)\). It returns a curve \(dy:\mathbb R\to H\) such that, for every \(s\ge s_0\),
\[
y\text{ has derivative }dy(s)\text{ at }s,
\]
and such that
\[
s\|dy(s)\|\to 0\quad\text{as }s\to\infty,
\]
and
\[
\|dy\|\text{ is integrable on }[s_0,\infty).
\]
This packages the derivative, weighted-speed, and integrability information for the intermediate curve \(y\).

The proof then applies `weighted_average_velocity_transfer`. Its hypotheses are the weighted-average relation between \(x\), \(y\), and \(\operatorname{deriv}x\), the derivative statement for \(y\), the weighted velocity limit for \(y\), and the integrability of \(\|dy\|\). Its conclusion transfers these estimates from \(y\) to \(x\):
\[
s\|\operatorname{deriv}x(s)\|\to 0\quad\text{as }s\to\infty,
\]
and
\[
\|\operatorname{deriv}x\|\text{ is integrable on }[s_0,\infty).
\]
This is the pair `hxt`; its first and second components will become the first two conclusions of the theorem.

Next the proof extracts from `hzmain.2.2.2` a point \(z_\infty\) such that
\[
z(t)\to z_\infty\quad\text{as }t\to\infty,
\qquad
\|\nabla f(z_\infty)\|=r.
\]
The final alternative in the conclusion of `theorem_2_1` is discarded by the underscore pattern.

The proof then proves that \(y\) also tends to this same point \(z_\infty\). Since \(y=z\circ\varphi\) with
\[
\varphi(s)=\frac{s^2}{2(\alpha-1)},
\]
it is enough to show that \(\varphi(s)\to\infty\) as \(s\to\infty\). The proof first notes that
\[
2(\alpha-1)>0,
\]
because \(\alpha>1\). To prove \(\varphi(s)\to\infty\), it verifies the usual at-top condition: for every real \(b\), eventually \(\varphi(s)\ge b\). It chooses the threshold
\[
M=\max\bigl(1,\,2(\alpha-1)b\bigr).
\]
If \(s\ge M\), then \(s\ge 1\), so
\[
s\le s^2,
\]
and also
\[
2(\alpha-1)b\le s.
\]
Therefore
\[
2(\alpha-1)b\le s\le s^2.
\]
Because \(2(\alpha-1)>0\), this is equivalent to
\[
b\le \frac{s^2}{2(\alpha-1)}=\varphi(s).
\]
Thus \(\varphi(s)\to\infty\). The tactics `filter_upwards` and `nlinarith` formalize the eventual inequality and the nonlinear arithmetic. Then the proof rewrites \(y\) using the equality \(y=z\circ\varphi\). Since \(z(t)\to z_\infty\) as \(t\to\infty\), composition with \(\varphi(s)\to\infty\) gives
\[
y(s)=z(\varphi(s))\to z_\infty\quad\text{as }s\to\infty.
\]
This is the step `hzLimit.comp hτ`.

Finally, the proof applies `weighted_average_limit_transfer`. This theorem says that under the same weighted-average relation, if \(y\to x_\infty\), then also \(x\to x_\infty\). Applied with \(x_\infty=z_\infty\), it yields
\[
x(s)\to z_\infty\quad\text{as }s\to\infty.
\]
The final `refine` assembles the three required conclusions: the weighted velocity limit from `hxt.1`, the integrability of \(\|\operatorname{deriv}x\|\) from `hxt.2`, and the limit statement with \(x_\infty=z_\infty\). The remaining goal
\[
\|\nabla f(z_\infty)\|=r
\]
is closed by `exact hzGrad`. The hypothesis `hsolution` is present in the statement but is not used anywhere in the provided proof.

