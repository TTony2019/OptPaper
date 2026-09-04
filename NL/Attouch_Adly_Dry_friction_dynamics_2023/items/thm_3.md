## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/thm_3.lean`

## Lean statement
```lean
theorem theorem_3_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {t₀ r : ℝ} (hr : 0 < r) (f : H → ℝ) (hf : Differentiable ℝ f) (z : ℝ → H)
    (fstar : H → ℝ) (gradFstar : H → H) (p : ℝ → H)
    (hp : ∀ t : ℝ, p t ∈ frictionBallProjector r (gradient f (z t)))
    (hdual : ∀ t ∈ Set.Ici t₀,
      HasDerivAt (fun u => gradFstar (gradient f (z u))) (p t - gradient f (z t)) t)
    (hdist : ∀ t : ℝ,
      HasDerivAt (fun u => Metric.infDist (gradient f (z u)) (frictionBall r) ^ 2)
        (inner ℝ (gradient f (z t) - p t) (p t - gradient f (z t))) t)
    (hint : MeasureTheory.IntegrableOn
      (fun t => Metric.infDist (gradient f (z t)) (frictionBall r) ^ 2 / 2) (Set.Ici t₀))
    (hbregman : ∀ gLimit : H, gLimit ∈ frictionBall r → ∀ t : ℝ,
      HasDerivAt
        (fun u => dualBregmanDistance fstar gradFstar (gradient f (z u)) gLimit)
        (inner ℝ (gradient f (z t) - p t) (gLimit - gradient f (z t))) t) :
    (∀ t ∈ Set.Ici t₀,
      p t ∈ frictionBallProjector r (gradient f (z t)) ∧
      HasDerivAt (fun u => gradFstar (gradient f (z u))) (p t - gradient f (z t)) t) ∧
    AntitoneOn (fun t => Metric.infDist (gradient f (z t)) (frictionBall r) ^ 2) (Set.Ici t₀) ∧
      Filter.Tendsto (fun t : ℝ => Real.sqrt t * Metric.infDist (gradient f (z t)) (frictionBall r))
        Filter.atTop (nhds 0) ∧
      ∀ gLimit : H, gLimit ∈ frictionBall r →
        AntitoneOn (fun t => dualBregmanDistance fstar gradFstar (gradient f (z t)) gLimit)
          (Set.Ici t₀)
```

## Statement explanation
The theorem is set in a real Hilbert space \(H\): it has a normed additive group structure, a real inner product space structure, and is complete. The parameters are a time \(t_0 \in \mathbb R\), a radius \(r>0\), a differentiable function \(f:H\to\mathbb R\), a curve \(z:\mathbb R\to H\), auxiliary functions \(f^\star:H\to\mathbb R\) and \(\operatorname{gradFstar}:H\to H\), and a curve \(p:\mathbb R\to H\).

The assumptions are as follows. For every real \(t\), \(p(t)\) belongs to \(\operatorname{frictionBallProjector} r (\nabla f(z(t)))\), meaning \(p(t)\) is a projection of the gradient point \(\nabla f(z(t))\) onto the friction ball of radius \(r\). For every \(t\geq t_0\), the function
\[
u \mapsto \operatorname{gradFstar}(\nabla f(z(u)))
\]
has derivative at \(t\) equal to
\[
p(t)-\nabla f(z(t)).
\]
For every real \(t\), the squared distance from \(\nabla f(z(t))\) to the friction ball of radius \(r\),
\[
u \mapsto \operatorname{dist}\bigl(\nabla f(z(u)), \operatorname{frictionBall} r\bigr)^2,
\]
has derivative at \(t\) equal to
\[
\bigl\langle \nabla f(z(t))-p(t),\, p(t)-\nabla f(z(t))\bigr\rangle.
\]
The half squared distance
\[
t \mapsto \frac12 \operatorname{dist}\bigl(\nabla f(z(t)), \operatorname{frictionBall} r\bigr)^2
\]
is assumed to be Lebesgue integrable on the interval \([t_0,\infty)\). Finally, for every limit point \(g_{\mathrm{limit}}\in \operatorname{frictionBall} r\) and every real \(t\), the dual Bregman distance
\[
u \mapsto \operatorname{dualBregmanDistance}
  f^\star \operatorname{gradFstar} \bigl(\nabla f(z(u))\bigr) g_{\mathrm{limit}}
\]
has derivative at \(t\) equal to
\[
\bigl\langle \nabla f(z(t))-p(t),\, g_{\mathrm{limit}}-\nabla f(z(t))\bigr\rangle.
\]

The conclusion has four parts. First, for every \(t\geq t_0\), \(p(t)\) is still a friction-ball projection of \(\nabla f(z(t))\), and the function \(u\mapsto \operatorname{gradFstar}(\nabla f(z(u)))\) has derivative \(p(t)-\nabla f(z(t))\) at \(t\). Second, the squared distance to the friction ball,
\[
t \mapsto \operatorname{dist}\bigl(\nabla f(z(t)), \operatorname{frictionBall} r\bigr)^2,
\]
is antitone, or nonincreasing, on \([t_0,\infty)\). Third,
\[
\sqrt{t}\, \operatorname{dist}\bigl(\nabla f(z(t)), \operatorname{frictionBall} r\bigr)
\to 0
\]
as \(t\to\infty\). Fourth, for every \(g_{\mathrm{limit}}\in \operatorname{frictionBall} r\), the dual Bregman distance
\[
t \mapsto \operatorname{dualBregmanDistance}
  f^\star \operatorname{gradFstar} \bigl(\nabla f(z(t))\bigr) g_{\mathrm{limit}}
\]
is antitone on \([t_0,\infty)\).

## Lean proof
```lean
by
  let g : ℝ → H := fun t => gradient f (z t)
  have hdist_nonpos : ∀ t : ℝ,
      inner ℝ (g t - p t) (p t - g t) ≤ 0 := by
    intro t
    rw [show p t - g t = -(g t - p t) by abel, inner_neg_right]
    exact neg_nonpos.mpr real_inner_self_nonneg
  have hdist_anti : Antitone (fun t => Metric.infDist (g t) (frictionBall r) ^ 2) := by
    apply antitone_of_deriv_nonpos (fun t => (hdist t).differentiableAt)
    intro t
    rw [(hdist t).deriv]
    exact hdist_nonpos t
  have hhalf_nonneg : ∀ t ∈ Set.Ici t₀,
      0 ≤ Metric.infDist (g t) (frictionBall r) ^ 2 / 2 := by
    intro t ht
    positivity
  have hhalf_anti : AntitoneOn
      (fun t => Metric.infDist (g t) (frictionBall r) ^ 2 / 2) (Set.Ici t₀) := by
    intro s hs t ht hst
    exact div_le_div_of_nonneg_right (hdist_anti hst) (by norm_num)
  have htail := lemma_3_1 (t₀ := t₀)
    (fun t => Metric.infDist (g t) (frictionBall r) ^ 2 / 2)
    hhalf_nonneg hhalf_anti hint
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
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨hp t, hdual t ht⟩
  · simpa [g] using hdist_anti.antitoneOn (Set.Ici t₀)
  · simpa [g] using hrate
  · intro gLimit hgLimit
    have hanti : Antitone
        (fun t => dualBregmanDistance fstar gradFstar (g t) gLimit) := by
      apply antitone_of_deriv_nonpos
      · intro t
        exact (hbregman gLimit hgLimit t).differentiableAt
      · intro t
        rw [(hbregman gLimit hgLimit t).deriv]
        have hp' : IsFrictionBallBestApproximation r (g t) (p t) := hp t
        rw [show gLimit - g t = (gLimit - p t) + (p t - g t) by abel,
          inner_add_right]
        have hproj : inner ℝ (g t - p t) (gLimit - p t) ≤ 0 := by
          exact (norm_eq_iInf_iff_real_inner_le_zero
            (by simpa [frictionBall] using (convex_closedBall (0 : H) r)) hp'.1).mp
            (by simpa [dist_eq_norm, Metric.infDist_eq_iInf] using hp'.2) gLimit hgLimit
        rw [show p t - g t = -(g t - p t) by abel, inner_neg_right]
        nlinarith [real_inner_self_nonneg (x := g t - p t)]
    change AntitoneOn (fun t => dualBregmanDistance fstar gradFstar (g t) gLimit) (Set.Ici t₀)
    exact hanti.antitoneOn _
```

## Proof explanation
The proof introduces the gradient curve \(g(t)=\nabla f(z(t))\) to simplify notation.

First it proves that for every \(t\),
\[
\langle g(t)-p(t), p(t)-g(t)\rangle \leq 0.
\]
This is done by rewriting \(p(t)-g(t)\) as \(-(g(t)-p(t))\), using bilinearity of the inner product, and observing that the expression becomes
\[
-\langle g(t)-p(t), g(t)-p(t)\rangle,
\]
the negative of a squared norm. Since real inner self-products are nonnegative, this is nonpositive.

Using the derivative assumption `hdist`, the derivative of the squared distance
\[
\operatorname{dist}(g(t), \operatorname{frictionBall} r)^2
\]
is exactly the nonpositive inner product just computed. The proof applies `antitone_of_deriv_nonpos` to conclude that this squared distance is globally antitone. The command `rw` replaces the derivative with the formula supplied by `hdist`, and `exact` closes the goal using the nonpositivity result.

Next, the proof shows that half of this squared distance is nonnegative on \([t_0,\infty)\). The tactic `positivity` proves this because it is a square divided by \(2\). It also shows the half squared distance is antitone on \([t_0,\infty)\) by dividing the monotonic inequality for the full squared distance by the positive number \(2\).

The imported lemma `lemma_3_1` is then applied to the nonnegative, antitone, integrable function
\[
\frac12 \operatorname{dist}(g(t), \operatorname{frictionBall} r)^2.
\]
In this application it gives
\[
t\cdot \frac12 \operatorname{dist}(g(t), \operatorname{frictionBall} r)^2 \to 0
\]

