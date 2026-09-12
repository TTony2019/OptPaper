## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/thm_3.lean`

## Lean statement
```lean
theorem theorem_3_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {t₀ r : ℝ} (hr : 0 < r) (f : H → ℝ) (z : ℝ → H)
    (hf : ContDiff ℝ 2 f) (hconvex : ConvexOn ℝ Set.univ f)
    (hf_lower : ∃ m : ℝ, ∀ x : H, m ≤ f x)
    (hgradient_lip : LocallyLipschitz (gradient f))
    (hz_diff : Differentiable ℝ z) (hsol : IsDrygradTrajectory r f z t₀) :
    (∃ p : ℝ → H, ∀ t ∈ Set.Ici t₀,
      p t ∈ frictionBallProjector r (gradient f (z t)) ∧
        HasDerivAt z (p t - gradient f (z t)) t) ∧
    AntitoneOn
      (fun t => Metric.infDist (gradient f (z t)) (frictionBall r) ^ 2) (Set.Ici t₀) ∧
    Filter.Tendsto
      (fun t : ℝ => Real.sqrt t * Metric.infDist (gradient f (z t)) (frictionBall r))
      Filter.atTop (nhds 0) ∧
    ∀ gLimit : H, gLimit ∈ frictionBall r →
      AntitoneOn (dualBregmanEnergy f z gLimit) (Set.Ici t₀)
```

## Statement explanation
Let \(H\) be a complete real inner product space, i.e. a real Hilbert space. Let \(t_0,r\in\mathbb R\) with \(r>0\), let \(f:H\to\mathbb R\), and let \(z:\mathbb R\to H\). The theorem assumes:

- \(f\) is \(C^2\) over the reals;
- \(f\) is convex on all of \(H\);
- \(f\) is bounded below, i.e. there exists \(m\in\mathbb R\) such that \(m\le f(x)\) for all \(x\in H\);
- the gradient \(\nabla f\) is locally Lipschitz;
- \(z\) is differentiable;
- \(z\) is a Drygrad trajectory for the friction radius \(r\), the function \(f\), and the initial time \(t_0\), written `IsDrygradTrajectory r f z t₀`.

Write
\[
g(t)=\nabla f(z(t)),\qquad d(t)=\operatorname{infDist}\bigl(g(t),B(0,r)\bigr),
\]
where \(B(0,r)\) is the closed ball of radius \(r\) centered at \(0\), called the friction ball. The theorem has four conclusions.

First, there exists a function \(p:\mathbb R\to H\) such that for every \(t\in[t_0,\infty)\),
\[
p(t)\in \operatorname{frictionBallProjector}_r(g(t))
\]
and
\[
z \text{ has derivative } p(t)-g(t) \text{ at } t.
\]
The statement \(p(t)\in \operatorname{frictionBallProjector}_r(g(t))\) means that \(p(t)\) is a best approximation to \(g(t)\) from the friction ball: \(p(t)\in B(0,r)\) and
\[
\operatorname{dist}(g(t),p(t))=\operatorname{infDist}(g(t),B(0,r)).
\]
Thus \(p(t)\) is the metric projection of the gradient \(g(t)\) onto the ball \(B(0,r)\). The second part says
\[
\operatorname{HasDerivAt} z \bigl(p(t)-g(t)\bigr) t.
\]

Second, the squared distance from the gradient to the friction ball is nonincreasing:
\[
t\mapsto d(t)^2
\]
is antitone on \([t_0,\infty)\). Hence for \(t_0\le s\le t\),
\[
d(t)^2\le d(s)^2.
\]

Third, the distance to the friction ball decays in the following weighted sense:
\[
\sqrt{t}\,d(t)\longrightarrow 0
\qquad\text{as }t\to\infty.
\]
Equivalently \(d(t)=o(1/\sqrt t)\).

Fourth, for every \(g_\infty\in B(0,r)\), the dual Bregman energy
\[
t\mapsto \operatorname{dualBregmanEnergy}(f,z,g_\infty,t)
=f(z(t))-\langle g_\infty,z(t)\rangle
\]
is antitone on \([t_0,\infty)\). So those energies decrease along the trajectory.

## Lean proof
```lean
by
  classical
  let g : ℝ → H := fun t => gradient f (z t)
  let p : ℝ → H := fun t => frictionBallProjection r hr (g t)
  have hf_diff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfderiv_contdiff : ContDiff ℝ 1 (fderiv ℝ f) := by
    exact (contDiff_succ_iff_fderiv.mp (show ContDiff ℝ (1 + 1) f by simpa using hf)).2.2
  have hgradient_contdiff : ContDiff ℝ 1 (gradient f) := by
    simpa [gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hfderiv_contdiff
  have hgradient_diff : Differentiable ℝ (gradient f) :=
    hgradient_contdiff.differentiable (by norm_num)
  have hg_deriv : ∀ t : ℝ,
      HasDerivAt g (fderiv ℝ (gradient f) (z t) (deriv z t)) t := by
    intro t
    simpa [g, Function.comp_def] using
      (hgradient_diff (z t)).hasFDerivAt.comp_hasDerivAt t (hz_diff t).hasDerivAt
  have hp_mem : ∀ t : ℝ, p t ∈ frictionBallProjector r (g t) := by
    intro t
    exact (frictionBall_isChebyshev hr.le (g t)).choose_spec.1
  have hp_formula : ∀ t : ℝ, p t = g t - softThresholder r (g t) := by
    intro t
    exact frictionBallProjection_eq_sub_softThresholder r hr (g t)
  have hvelocity : ∀ t ∈ Set.Ici t₀, deriv z t = p t - g t := by
    intro t ht
    rw [hp_formula]
    have hv := drygrad_velocity_formula hr (hsol t ht)
    simpa using hv
  have hgnorm_deriv : ∀ t ∈ interior (Set.Ici t₀),
      HasDerivAt (fun s => ‖g s‖)
        (if g t = 0 then 0 else
          inner ℝ (fderiv ℝ (gradient f) (z t) (deriv z t)) (g t) / ‖g t‖) t := by
    intro t ht
    by_cases hgt : g t = 0
    · rw [if_pos hgt]
      have hzt : deriv z t = 0 := by
        rw [hvelocity t (interior_subset ht), hp_formula, hgt]
        simp [softThresholder_apply]
      have hg0 : HasDerivAt g 0 t := by
        simpa [hzt] using hg_deriv t
      rw [hasDerivAt_iff_isLittleO]
      simpa [hgt] using hg0.isLittleO.norm_left
    · rw [if_neg hgt]
      have hnorm_ne : ‖g t‖ ≠ 0 := norm_ne_zero_iff.mpr hgt
      have hs := (hg_deriv t).norm_sq.sqrt (pow_ne_zero 2 hnorm_ne)
      convert hs using 1
      all_goals simp [real_inner_comm, norm_nonneg]
      all_goals field_simp
  have hgnorm_deriv_nonpos : ∀ t ∈ interior (Set.Ici t₀),
      deriv (fun s => ‖g s‖) t ≤ 0 := by
    intro t ht
    rw [(hgnorm_deriv t ht).deriv]
    by_cases hgt : g t = 0
    · simp [hgt]
    · rw [if_neg hgt]
      by_cases hball : ‖g t‖ ≤ r
      · have hzt : deriv z t = 0 := by
          rw [hvelocity t (interior_subset ht), hp_formula, softThresholder_apply,
            if_neg (not_lt_of_ge hball)]
          simp
        simp [hzt]
      · have houtside : r < ‖g t‖ := lt_of_not_ge hball
        have hcoef : 0 < 1 - r / ‖g t‖ := by
          rw [sub_pos, div_lt_one (lt_trans hr houtside)]
          exact houtside
        have hzt : deriv z t = -(1 - r / ‖g t‖) • g t := by
          rw [hvelocity t (interior_subset ht), hp_formula, softThresholder_apply,
            if_pos houtside]
          module
        have hmono := gradient_derivative_inner_nonnegative f hconvex hf_diff z
          (hz_diff t).hasDerivAt (hg_deriv t)
        have hmono' : 0 ≤ -(1 - r / ‖g t‖) *
            inner ℝ (g t) (fderiv ℝ (gradient f) (z t) (deriv z t)) := by
          calc
            0 ≤ inner ℝ (deriv z t)
                (fderiv ℝ (gradient f) (z t) (deriv z t)) := hmono
            _ = -(1 - r / ‖g t‖) *
                inner ℝ (g t) (fderiv ℝ (gradient f) (z t) (deriv z t)) := by
              rw [hzt, real_inner_smul_left]
        have hinner : inner ℝ (fderiv ℝ (gradient f) (z t) (deriv z t)) (g t) ≤ 0 := by
          rw [real_inner_comm]
          nlinarith
        exact div_nonpos_of_nonpos_of_nonneg hinner (norm_nonneg _)
  have hgnorm_anti : AntitoneOn (fun t => ‖g t‖) (Set.Ici t₀) := by
    have hcont : ContinuousOn (fun t => ‖g t‖) (Set.Ici t₀) := by
      exact (hgradient_lip.continuous.comp_continuousOn
        hz_diff.continuous.continuousOn).norm
    apply antitoneOn_of_deriv_nonpos (convex_Ici t₀) hcont
    · intro t ht
      exact (hgnorm_deriv t ht).differentiableAt.differentiableWithinAt
    · exact hgnorm_deriv_nonpos
  have hdist_formula : ∀ t : ℝ,
      Metric.infDist (g t) (frictionBall r) = max (‖g t‖ - r) 0 :=
    fun t => infDist_frictionBall_eq r hr (g t)
  have hdist_anti : AntitoneOn
      (fun t => Metric.infDist (g t) (frictionBall r) ^ 2) (Set.Ici t₀) := by
    intro s hs t ht hst
    change Metric.infDist (g t) (frictionBall r) ^ 2 ≤
      Metric.infDist (g s) (frictionBall r) ^ 2
    rw [hdist_formula, hdist_formula]
    have hmax : max (‖g t‖ - r) 0 ≤ max (‖g s‖ - r) 0 := by
      exact max_le_max_right 0 (sub_le_sub_right (hgnorm_anti hs ht hst) r)
    exact pow_le_pow_left₀ (by positivity) hmax 2
  have hdist_velocity : ∀ t ∈ Set.Ici t₀,
      Metric.infDist (g t) (frictionBall r) = ‖deriv z t‖ := by
    intro t ht
    have hpdist := (hp_mem t).2
    rw [← hpdist, dist_eq_norm, hvelocity t ht]
    rw [show g t - p t = -(p t - g t) by abel, norm_neg]
  have hdist_integrable : MeasureTheory.IntegrableOn
      (fun t => Metric.infDist (g t) (frictionBall r) ^ 2 / 2) (Set.Ici t₀) := by
    by_cases hinitial : r < ‖g t₀‖
    · have hsq := (theorem_2_1 hr f z (hf.of_le (by norm_num)) hf_lower hgradient_lip
          hz_diff (by simpa [g] using hinitial) hsol).2.1
      have hsq' : MeasureTheory.IntegrableOn
          (fun t => Metric.infDist (g t) (frictionBall r) ^ 2) (Set.Ici t₀) := by
        apply hsq.congr_fun
        · intro t ht
          change ‖deriv z t‖ ^ 2 = Metric.infDist (g t) (frictionBall r) ^ 2
          rw [hdist_velocity t ht]
        · exact measurableSet_Ici
      exact hsq'.div_const 2
    · have hzero : ∀ t ∈ Set.Ici t₀,
          Metric.infDist (g t) (frictionBall r) ^ 2 / 2 = 0 := by
        intro t ht
        have hle : ‖g t‖ ≤ r :=
          (hgnorm_anti (Set.mem_Ici.mpr le_rfl) ht ht).trans (not_lt.mp hinitial)
        rw [hdist_formula, max_eq_right (sub_nonpos.mpr hle)]
        norm_num
      apply MeasureTheory.integrableOn_zero.congr_fun
      · intro t ht
        exact (hzero t ht).symm
      · exact measurableSet_Ici
  have hhalf_nonneg : ∀ t ∈ Set.Ici t₀,
      0 ≤ Metric.infDist (g t) (frictionBall r) ^ 2 / 2 := by
    intro t ht
    positivity
  have hhalf_anti : AntitoneOn
      (fun t => Metric.infDist (g t) (frictionBall r) ^ 2 / 2) (Set.Ici t₀) := by
    intro s hs t ht hst
    exact div_le_div_of_nonneg_right (hdist_anti hs ht hst) (by norm_num)
  have htail := lemma_3_1 (t₀ := t₀)
    (fun t => Metric.infDist (g t) (frictionBall r) ^ 2 / 2)
    hhalf_nonneg hhalf_anti hdist_integrable
  have hdist_sq : Filter.Tendsto
      (fun t : ℝ => t * Metric.infDist (g t) (frictionBall r) ^ 2)
      Filter.atTop (nhds 0) := by
    convert htail.const_mul 2 using 1
    · ext t
      ring
    · norm_num
  have hsqrt : Filter.Tendsto
      (fun t : ℝ => Real.sqrt (t * Metric.infDist (g t) (frictionBall r) ^ 2))
      Filter.atTop (nhds 0) := by
    simpa using Real.continuous_sqrt.tendsto 0 |>.comp hdist_sq
  have hrate : Filter.Tendsto
      (fun t : ℝ => Real.sqrt t * Metric.infDist (g t) (frictionBall r))
      Filter.atTop (nhds 0) := by
    apply hsqrt.congr'
    filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with t ht
    rw [Real.sqrt_mul ht, Real.sqrt_sq_eq_abs, abs_of_nonneg Metric.infDist_nonneg]
  have hbregman : ∀ gLimit : H, gLimit ∈ frictionBall r →
      AntitoneOn (dualBregmanEnergy f z gLimit) (Set.Ici t₀) := by
    intro gLimit hgLimit
    have hderiv : ∀ t ∈ Set.Ici t₀,
        HasDerivAt (dualBregmanEnergy f z gLimit)
          (inner ℝ (g t - gLimit) (p t - g t)) t := by
      intro t ht
      have hfz := (hf_diff (z t)).hasGradientAt.hasFDerivAt.comp_hasDerivAt
        t (hz_diff t).hasDerivAt
      have hinner := (hasDerivAt_const t gLimit).inner ℝ (hz_diff t).hasDerivAt
      convert hfz.sub hinner using 1
      rw [← hvelocity t ht]
      simp [g, inner_sub_left]
    have hcont : ContinuousOn (dualBregmanEnergy f z gLimit) (Set.Ici t₀) :=
      HasDerivAt.continuousOn hderiv
    apply antitoneOn_of_deriv_nonpos (convex_Ici t₀) hcont
    · intro t ht
      exact (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hderiv t (interior_subset ht)).deriv]
      have hp' : IsFrictionBallBestApproximation r (g t) (p t) := hp_mem t
      rw [show g t - gLimit = (g t - p t) + (p t - gLimit) by abel,
        inner_add_left]
      have hproj : inner ℝ (g t - p t) (gLimit - p t) ≤ 0 := by
        exact (norm_eq_iInf_iff_real_inner_le_zero
          (by simpa [frictionBall] using (convex_closedBall (0 : H) r)) hp'.1).mp
          (by simpa [dist_eq_norm, Metric.infDist_eq_iInf] using hp'.2) gLimit hgLimit
      have hfirst : inner ℝ (g t - p t) (p t - g t) ≤ 0 := by
        rw [show p t - g t = -(g t - p t) by abel, inner_neg_right]
        exact neg_nonpos.mpr real_inner_self_nonneg
      have hsecond : inner ℝ (p t - gLimit) (p t - g t) ≤ 0 := by
        calc
          inner ℝ (p t - gLimit) (p t - g t) =
              inner ℝ (gLimit - p t) (g t - p t) := by
                rw [show p t - gLimit = -(gLimit - p t) by abel,
                  show p t - g t = -(g t - p t) by abel,
                  inner_neg_left, inner_neg_right, neg_neg]
          _ = inner ℝ (g t - p t) (gLimit - p t) := real_inner_comm _ _
          _ ≤ 0 := hproj
      linarith
  refine ⟨⟨p, ?_⟩, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨hp_mem t, (hz_diff t).hasDerivAt.congr_deriv (hvelocity t ht)⟩
  · simpa [g] using hdist_anti
  · simpa [g] using hrate
  · exact hbregman
```

## Proof explanation
The proof starts with `classical` and then introduces the abbreviations
\[
g(t)=\nabla f(z(t)),\qquad
p(t)=\operatorname{frictionBallProjection}_r(g(t)).
\]
Here `frictionBallProjection r hr` is the single-valued nearest-point projection onto the closed ball \(B(0,r)\), obtained by choosing the unique point supplied by the Chebyshev property of the ball.

The first preparatory step is to obtain differentiability of the relevant maps. Since \(f\) is \(C^2\), it is differentiable:
\[
f \text{ is differentiable over } \mathbb R.
\]
The proof then uses that the Fréchet derivative of \(f\), namely \(\mathrm{fderiv}\,\mathbb R f\), is \(C^1\). Indeed, the theorem `contDiff_succ_iff_fderiv` is applied to \(f\) of class \(C^{1+1}=C^2\), giving that \(\mathrm{fderiv}\,\mathbb R f\) is \(C^1\). Composing with the Riesz isomorphism between \(H\) and its dual gives that the gradient \(\nabla f\) is \(C^1\), hence differentiable. Therefore \(g=\nabla f\circ z\) is differentiable as a composition of differentiable maps.

For every \(t\), the chain rule for \(g=\nabla f\circ z\) gives
\[
g'(t)=D(\nabla f)(z(t))[z'(t)],
\]
where \(D(\nabla f)(z(t))[z'(t)]\) is the Lean expression
\[
\texttt{fderiv ℝ (gradient f) (z t) (deriv z t)}.
\]
This identity is used later in computing the derivative of \(\|g(t)\|\).

Next, the proof records the projection properties of \(p(t)\). The theorem `frictionBall_isChebyshev` says that in a complete real Hilbert space, every point has a unique best approximation in the closed ball of radius \(r\) when \(r\ge0\). Since \(0<r\), the projection is well-defined. From the defining choice of `frictionBallProjection`, the proof obtains
\[
p(t)\in \operatorname{frictionBallProjector}_r(g(t)).
\]
Thus \(p(t)\in B(0,r)\) and
\[
\operatorname{dist}(g(t),p(t))
=\operatorname{infDist}(g(t),B(0,r)).
\]

The proof also uses the relation between ball projection and soft thresholding. The soft thresholder is
\[
S_r(x)=
\begin{cases}
\left(1-\dfrac r{\|x\|}\right)x, & r<\|x\|,\\[4pt]
0, & r\ge \|x\|.
\end{cases}
\]
The theorem `frictionBallProjection_eq_sub_softThresholder` gives
\[
p(t)=g(t)-S_r(g(t)).
\]
Equivalently,
\[
p(t)-g(t)=-S_r(g(t)).
\]

Now the Drygrad condition is converted into an explicit velocity formula. The hypothesis `hsol` says that \(z\) solves the Drygrad trajectory condition. For \(t\ge t_0\), the proof applies `drygrad_velocity_formula`. That result says that if \(v\) satisfies the subdifferential equation
\[
v+u+g=0
\]
with \(u\) in the subdifferential of the dry friction potential of radius \(r\) at \(v\), then
\[
v=-S_r(g).
\]
Specializing to \(v=z'(t)\) and \(g=g(t)=\nabla f(z(t))\), it follows that
\[
z'(t)=-S_r(g(t)).
\]
Combining this with \(p(t)=g(t)-S_r(g(t))\), the proof obtains
\[
z'(t)=p(t)-g(t)
\qquad(t\ge t_0).
\]
This is the explicit differential equation
\[
z'(t)=p(t)-\nabla f(z(t)).
\]

The next main step is to show that \(\|g(t)\|\) is nonincreasing. The proof computes the derivative of \(s\mapsto \|g(s)\|\). If \(g(t)=0\), then the velocity formula forces \(z'(t)=0\), and hence \(g'(t)=0\), so
\[
\frac{d}{dt}\|g(t)\|=0.
\]
If \(g(t)\ne0\), then the derivative of the norm is
\[
\frac{d}{dt}\|g(t)\|
=
\frac{\left\langle D(\nabla f)(z(t))[z'(t)],\,g(t)\right\rangle}{\|g(t)\|}.
\]

The proof then shows this quantity is \(\le0\). If \(\|g(t)\|\le r\), then soft thresholding vanishes:
\[
S_r(g(t))=0.
\]
Therefore \(z'(t)=p(t)-g(t)=0\), and the numerator in the derivative formula is \(0\), so the derivative of \(\|g(t)\|\) is \(0\).

If \(r<\|g(t)\|\), then
\[
\alpha:=1-\frac r{\|g(t)\|}>0,
\]
and the velocity formula gives
\[
z'(t)=-\alpha\,g(t).
\]
The proof invokes `gradient_derivative_inner_nonnegative`. That result says that for a convex differentiable function \(f\), if \(x\) is differentiable at \(t\) with derivative \(dx\), and if \(\nabla f\circ x\) is differentiable at \(t\) with derivative \(dv\), then
\[
0\le \langle dx,dv\rangle.
\]
Specializing to \(x=z\), \(dx=z'(t)\), and \(dv=D(\nabla f)(z(t))[z'(t)]\), the proof gets
\[
0\le \left\langle z'(t),D(\nabla f)(z(t))[z'(t)]\right\rangle.
\]
Substituting \(z'(t)=-\alpha g(t)\) yields
\[
0\le -\alpha\left\langle g(t),D(\nabla f)(z(t))[z'(t)]\right\rangle.
\]
Since \(\alpha>0\), this implies
\[
\left\langle g(t),D(\nabla f)(z(t))[z'(t)]\right\rangle\le0.
\]
By symmetry of the real inner product,
\[
\left\langle D(\nabla f)(z(t))[z'(t)],g(t)\right\rangle\le0.
\]
Dividing by \(\|g(t)\|>0\) shows that the derivative of \(\|g(t)\|\) is \(\le0\). Thus the derivative of \(\|g\|\) is nonpositive on the interior of \([t_0,\infty)\).

Continuity of \(t\mapsto \|g(t)\|\) follows from continuity of \(z\) and the local Lipschitz continuity of \(\nabla f\). The proof applies `antitoneOn_of_deriv_nonpos`: a continuous function on a convex interval whose derivative is nonpositive on the interior is antitone. Therefore
\[
t\mapsto \|g(t)\|
\]
is antitone on \([t_0,\infty)\). So for \(t_0\le s\le t\),
\[
\|g(t)\|\le\|g(s)\|.
\]

Next, the theorem `infDist_frictionBall_eq` gives the exact formula
\[
\operatorname{infDist}(g(t),B(0,r))
=
\max\bigl(\|g(t)\|-r,0\bigr).
\]
Since \(\|g\|\) is antitone and \(x\mapsto \max(x-r,0)\) is nondecreasing, the distance
\[
d(t)=\operatorname{infDist}(g(t),B(0,r))
\]
is antitone. Squaring preserves this order on nonnegative values, so
\[
t\mapsto d(t)^2
\]
is antitone on \([t_0,\infty)\). This proves the second conclusion.

To prove the decay estimate, the proof first needs integrability of
\[
t\mapsto \frac{d(t)^2}{2}.
\]
It splits into two cases.

If \(r<\|g(t_0)\|\), then the gradient starts outside the friction ball. The proof applies `theorem_2_1`. That theorem, under the same convexity and regularity hypotheses, with \(z\) differentiable, \(r<\|\nabla f(z(t_0))\|\), and \(z\) a Drygrad trajectory, concludes among other things that
\[
t\mapsto \|z'(t)\|^2
\]
is integrable on \([t_0,\infty)\). The proof also establishes that for \(t\ge t_0\),
\[
d(t)=\|z'(t)\|.
\]
Indeed, since \(p(t)\) is a best approximation,
\[
d(t)=\operatorname{dist}(g(t),p(t))=\|g(t)-p(t)\|=\|p(t)-g(t)\|=\|z'(t)\|.
\]
Therefore \(d(t)^2=\|z'(t)\|^2\), so \(d^2\) is integrable. Dividing by the constant \(2\) gives integrability of \(d(t)^2/2\).

If \(r\ge\|g(t_0)\|\), then by monotonicity of \(\|g(t)\|\), for every \(t\ge t_0\),
\[
\|g(t)\|\le\|g(t_0)\|\le r.
\]
Thus
\[
d(t)=\max(\|g(t)\|-r,0)=0.
\]
Hence \(d(t)^2/2=0\) for all \(t\ge t_0\), which is certainly integrable.

The function \(h(t)=d(t)^2/2\) is nonnegative, antitone, and integrable on \([t_0,\infty)\). The proof applies `lemma_3_1`. That lemma states that if \(h\) is nonnegative on \([t_0,\infty)\), antitone on \([t_0,\infty)\), and integrable on \([t_0,\infty)\), then
\[
t\,h(t)\longrightarrow 0
\qquad\text{as }t\to\infty.
\]
Therefore
\[
t\,\frac{d(t)^2}{2}\longrightarrow 0.
\]
Multiplying by \(2\) gives
\[
t\,d(t)^2\longrightarrow 0.
\]
Since the square root is continuous at \(0\),
\[
\sqrt{t\,d(t)^2}\longrightarrow 0.
\]
For \(t\ge0\), and using \(d(t)\ge0\),
\[
\sqrt{t\,d(t)^2}=\sqrt t\,d(t).
\]
Thus
\[
\sqrt t\,d(t)\longrightarrow 0.
\]
This proves the third conclusion.

Finally, the proof establishes monotonicity of the dual Bregman energy. Fix \(g_\infty\in B(0,r)\) and define
\[
E(t)=f(z(t))-\langle g_\infty,z(t)\rangle.
\]
For \(t\ge t_0\), differentiating and using the chain rule gives
\[
E'(t)
=
\langle \nabla f(z(t)),z'(t)\rangle-\langle g_\infty,z'(t)\rangle
=
\langle g(t)-g_\infty,z'(t)\rangle.
\]
Using \(z'(t)=p(t)-g(t)\), this becomes
\[
E'(t)=\langle g(t)-g_\infty,p(t)-g(t)\rangle.
\]
The proof rewrites
\[
g(t)-g_\infty=(g(t)-p(t))+(p(t)-g_\infty),
\]
so
\[
E'(t)
=
\langle g(t)-p(t),p(t)-g(t)\rangle
+
\langle p(t)-g_\infty,p(t)-g(t)\rangle.
\]
The first term is
\[
\langle g(t)-p(t),-(g(t)-p(t))\rangle
=
-\|g(t)-p(t)\|^2\le0.
\]
For the second term, the proof uses the nearest-point variational inequality for the convex closed ball. Since \(p(t)\) is a best approximation to \(g(t)\) in \(B(0,r)\), for every \(y\in B(0,r)\),
\[
\langle g(t)-p(t),y-p(t)\rangle\le0.
\]
The proof derives this from `norm_eq_iInf_iff_real_inner_le_zero`, a standard characterization of nearest points in a closed convex set, applied to the closed ball and to the point \(p(t)\). Taking \(y=g_\infty\), which lies in \(B(0,r)\) by hypothesis, gives
\[
\langle g(t)-p(t),g_\infty-p(t)\rangle\le0.
\]
Using antisymmetry of the real inner product, this is exactly
\[
\langle p(t)-g_\infty,p(t)-g(t)\rangle\le0.
\]
Therefore both terms in the formula for \(E'(t)\) are nonpositive, so
\[
E'(t)\le0.
\]
The energy \(E\) is continuous on \([t_0,\infty)\), and its derivative is nonpositive on the interior. Applying `antitoneOn_of_deriv_nonpos` again shows that
\[
t\mapsto f(z(t))-\langle g_\infty,z(t)\rangle
\]
is antitone on \([t_0,\infty)\). This proves the fourth conclusion.

At the end, the proof assembles the results. It returns the function \(p\) and uses the projection property \(p(t)\in\operatorname{frictionBallProjector}_r(g(t))\) together with the velocity identity to obtain the derivative statement. The previously proved antitone statement for \(d(t)^2\), the weighted limit \(\sqrt t\,d(t)\to0\), and the Bregman-energy monotonicity are then exactly the remaining conclusions of `theorem_3_2`. The Lean tactics `intro`, `rw`, and `simp` introduce variables and hypotheses and perform the algebraic rewrites, while `exact` supplies the named results and `linarith` or `nlinarith` combines the resulting inequalities.

