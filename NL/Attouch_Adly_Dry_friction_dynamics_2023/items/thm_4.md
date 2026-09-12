## Source file
`Attouch_Adly_Dry_friction_dynamics_2023/items/thm_4.lean`

## Lean statement
```lean
theorem theorem_3_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [FiniteDimensional ℝ H] [Nontrivial H]
    {t₀ r : ℝ} (hr : 0 < r) (A : H →L[ℝ] H) (f : H → ℝ)
    (hsymm : A.IsSymmetric) (hpos : ∀ x ≠ 0, 0 < inner ℝ (A x) x)
    (g p : ℝ → H)
    (hf_quadratic : ∀ x : H, f x = inner ℝ (A x) x / 2)
    (hg : Differentiable ℝ g)
    (hdualFlow : ∀ t, p t ∈ frictionBallProjector r (g t) ∧
      fderiv ℝ (gradient (fun q =>
        (ERealFunction.conjugate (fun x => (f x : EReal)) q).toReal))
        (g t) (deriv g t) + g t - p t = 0)
    (hinitial : r < ‖g t₀‖) :
    ∃ Cupper Clower μ ν : ℝ, 0 < Cupper ∧ 0 < Clower ∧ 0 < μ ∧ 0 < ν ∧
      (∀ t ∈ Set.Ici t₀, Metric.infDist (g t) (frictionBall r) ≤ Cupper * Real.exp (-μ * t)) ∧
      (∀ t ∈ Set.Ici t₀, Clower * Real.exp (-ν * t) ≤ Metric.infDist (g t) (frictionBall r)) ∧
      ∀ t ∈ Set.Ici t₀, g t ∉ frictionBall r
```

## Statement explanation
The declaration `theorem_3_3` is a theorem about a real inner product space \(H\) that is complete, finite dimensional, and nontrivial. It fixes \(t_0,r\in\mathbb R\) with \(r>0\), a continuous linear operator \(A\colon H\to H\), a function \(f\colon H\to\mathbb R\), and two curves \(g,p\colon \mathbb R\to H\). The operator \(A\) is assumed symmetric, meaning it is self-adjoint for the inner product, and positive definite, meaning
\[
\langle Ax,x\rangle>0
\]
for every nonzero \(x\in H\). The function \(f\) is assumed to be the associated quadratic form
\[
f(x)=\frac12\langle Ax,x\rangle .
\]
The curve \(g\) is assumed differentiable. The hypothesis `hdualFlow` says that for every \(t\in\mathbb R\), \(p(t)\) is a friction-ball projection of \(g(t)\) onto the closed ball
\[
\operatorname{frictionBall} r=\overline B(0,r)=\{y\in H:\|y\|\le r\},
\]
and that the dual-flow equation holds:
\[
D\!\left(\nabla \varphi^*\right)(g(t))\bigl[g'(t)\bigr]+g(t)-p(t)=0,
\]
where \(\varphi\) is the extended-real version of \(f\) and \(\varphi^*\) is its Fenchel conjugate. In the presence of the quadratic form and positive definiteness, this equation is equivalent to
\[
A^{-1}g'(t)+g(t)-p(t)=0,
\]
or equivalently
\[
g'(t)=A\bigl(p(t)-g(t)\bigr).
\]
The initial condition \(r<\|g(t_0)\|\) says that \(g(t_0)\) lies outside the closed ball \(\overline B(0,r)\).

The conclusion is that there exist positive constants \(C_{\mathrm{upper}},C_{\mathrm{lower}},\mu,\nu\) such that, writing
\[
d(t)=\operatorname{infDist}\bigl(g(t),\operatorname{frictionBall} r\bigr),
\]
one has for every \(t\ge t_0\)
\[
d(t)\le C_{\mathrm{upper}}e^{-\mu t},
\]
and
\[
C_{\mathrm{lower}}e^{-\nu t}\le d(t),
\]
and also
\[
g(t)\notin \operatorname{frictionBall} r.
\]
Thus the distance from the trajectory \(g(t)\) to the friction ball is bounded above by a decaying exponential and below by another decaying exponential for all future times, and the trajectory never enters the ball. The upper bound expresses exponential convergence to the ball; the lower bound prevents convergence faster than an exponential rate.

## Lean proof
```lean
by
  obtain ⟨μ, ν, hμ, hν, hquad⟩ := coercive_bounds_of_posdef_finiteDim A hpos
  have hi := isInvertible_of_posdef_finiteDim A hpos
  have hHessian := hessian_quadratic_conjugate A hsymm hpos
  have hvel : ∀ t : ℝ, deriv g t = A (p t - g t) := by
    intro t
    have hflow := hdualFlow t |>.2
    have hH := congrFun hHessian (g t)
    have hsum : A.inverse (deriv g t) + g t = p t := by
      have hz : A.inverse (deriv g t) + g t - p t = 0 := by
        rw [← hH]
        simpa only [hf_quadratic] using hflow
      exact sub_eq_zero.mp hz
    have hinv : A.inverse (deriv g t) = p t - g t :=
      (eq_sub_iff_add_eq).2 hsum
    have happly := congrArg A hinv
    simpa [A.map_sub, hi.self_apply_inverse] using happly
  let E : ℝ → ℝ := fun t => Metric.infDist (g t) (frictionBall r) ^ 2 / 2
  have hd0 : 0 < Metric.infDist (g t₀) (frictionBall r) :=
    frictionBall_not_mem_initial_infDist_pos (le_of_lt hr) hinitial
  have hEderiv : ∀ t, HasDerivAt E
      (- inner ℝ (g t - p t) (A (g t - p t))) t := by
    intro t
    have hdist_formula : ∀ s : ℝ,
        Metric.infDist (g s) (frictionBall r) = max (‖g s‖ - r) 0 :=
      fun s => infDist_frictionBall_eq r hr (g s)
    have hE_formula : E = fun s => max (‖g s‖ - r) 0 ^ 2 / 2 := by
      funext s
      simp [E, hdist_formula s]
    rw [hE_formula]
    by_cases hzero : g t = 0
    · have hnorm_cont : Tendsto (fun s => ‖g s‖) (nhds t) (nhds (0 : ℝ)) := by
        simpa [hzero] using ((hg t).continuousAt.norm.tendsto)
      have hlt : ∀ᶠ s in nhds t, ‖g s‖ < r := by
        filter_upwards [hnorm_cont.eventually (eventually_lt_nhds hr)] with s hs
        exact hs
      have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
      have hzero' : HasDerivAt (fun s => max (‖g s‖ - r) 0 ^ 2 / 2) 0 t := by
        have hz := hconst.congr_of_eventuallyEq
          (show (fun s => max (‖g s‖ - r) 0 ^ 2) =ᶠ[nhds t] (fun _ => (0 : ℝ)) by
            filter_upwards [hlt] with s hs
            rw [max_eq_right (sub_nonpos.mpr hs.le)]
            norm_num)
        simpa [div_eq_mul_inv, mul_comm] using hz.const_mul (1 / 2 : ℝ)
      have hp_eq : p t = 0 := by
        have hpdist := (hdualFlow t).1.2
        simp [hzero, infDist_frictionBall_eq r hr] at hpdist
        apply norm_eq_zero.mp
        simpa [hr.le] using hpdist
      convert hzero' using 1
      rw [hzero, hp_eq]
      simp
    · have hnorm_ne : ‖g t‖ ≠ 0 := norm_ne_zero_iff.mpr hzero
      have hgderiv : HasDerivAt g (deriv g t) t := (hg t).hasDerivAt
      have hnorm_deriv : HasDerivAt (fun s => ‖g s‖)
          (inner ℝ (g t) (deriv g t) / ‖g t‖) t := by
        have hs := hgderiv.norm_sq.sqrt (pow_ne_zero 2 hnorm_ne)
        convert hs using 1
        all_goals simp [norm_nonneg]
        all_goals field_simp
      have hu : HasDerivAt (fun s => ‖g s‖ - r)
          (inner ℝ (g t) (deriv g t) / ‖g t‖) t := hnorm_deriv.sub_const r
      by_cases hout : r < ‖g t‖
      · have hpos : ∀ᶠ s in nhds t, 0 < ‖g s‖ - r := by
          have hcont : Tendsto (fun s => ‖g s‖ - r) (nhds t) (nhds (‖g t‖ - r)) :=
            hu.continuousAt
          filter_upwards [hcont.eventually (eventually_gt_nhds (sub_pos.mpr hout))] with s hs
          exact hs
        have hsq' : HasDerivAt (fun s => max (‖g s‖ - r) 0 ^ 2 / 2)
            ((‖g t‖ - r) * (inner ℝ (g t) (deriv g t) / ‖g t‖)) t := by
          have hsq := (hu.pow 2).const_mul (1 / 2 : ℝ)
          have hsq0 := hsq.congr_of_eventuallyEq
            (show (fun s => max (‖g s‖ - r) 0 ^ 2 / 2) =ᶠ[nhds t]
                (fun s => (1 / 2 : ℝ) * (‖g s‖ - r) ^ 2) by
              filter_upwards [hpos] with s hs
              rw [max_eq_left hs.le]
              ring)
          convert hsq0 using 1; ring
        have hp_eq : p t = (r / ‖g t‖) • g t := by
          have hp_can : p t = frictionBallProjection r hr (g t) := by
            exact (frictionBall_isChebyshev hr.le (g t)).choose_spec.2 _ (hdualFlow t).1
          rw [hp_can, frictionBallProjection_eq_sub_softThresholder r hr,
            softThresholder_apply, if_pos hout]
          module
        have hvel_inner : inner ℝ (g t - p t) (A (g t - p t)) =
            -((‖g t‖ - r) * (inner ℝ (g t) (deriv g t) / ‖g t‖)) := by
          have hvel_t := hvel t
          have hA : A (g t - p t) = -deriv g t := by
            rw [show g t - p t = -(p t - g t) by abel, map_neg, hvel_t]
          rw [hA, inner_neg_right, hp_eq]
          rw [show g t - ((r / ‖g t‖) • g t) =
            (1 - r / ‖g t‖) • g t by module]
          rw [real_inner_smul_left]
          field_simp
        convert hsq' using 1
        rw [hvel_inner]
        ring
      · have hle : ‖g t‖ ≤ r := not_lt.mp hout
        have hp_eq : p t = g t := by
          have hpdist := (hdualFlow t).1.2
          rw [infDist_frictionBall_eq r hr (g t), max_eq_right (sub_nonpos.mpr hle)] at hpdist
          have : dist (g t) (p t) = 0 := hpdist
          exact (sub_eq_zero.mp (by simpa [dist_eq_norm] using this)).symm
        have hvel_zero : deriv g t = 0 := by
          rw [hvel t, hp_eq, sub_self]
          simp
        have hconst : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 t := hasDerivAt_const t 0
        have hzero' : HasDerivAt (fun s => max (‖g s‖ - r) 0 ^ 2 / 2) 0 t := by
          by_cases heq : ‖g t‖ = r
          · have hz := hasDerivAt_max_sq_zero (hu := hu) (by linarith)
            simpa [div_eq_mul_inv, mul_comm] using hz.const_mul (1 / 2 : ℝ)
          · have hlt : ‖g t‖ < r := lt_of_le_of_ne hle heq
            have hpos : ∀ᶠ s in nhds t, ‖g s‖ - r < 0 := by
              filter_upwards [hu.continuousAt.eventually
                (eventually_lt_nhds (sub_neg.mpr hlt))] with s hs
              exact hs
            have hz := hconst.congr_of_eventuallyEq
              (show (fun s => max (‖g s‖ - r) 0 ^ 2) =ᶠ[nhds t] (fun _ => (0 : ℝ)) by
                filter_upwards [hpos] with s hs
                rw [max_eq_right hs.le]
                norm_num)
            simpa [div_eq_mul_inv, mul_comm] using hz.const_mul (1 / 2 : ℝ)
        convert hzero' using 1
        rw [hp_eq]
        simp
  have hupperDiff : ∀ t, deriv E t + 2 * μ * E t ≤ 0 := by
    intro t
    have hq := (hquad (g t - p t)).1
    have hdist := (hdualFlow t).1.2
    have hnorm : ‖g t - p t‖ = Metric.infDist (g t) (frictionBall r) := by
      simpa [dist_eq_norm] using hdist
    rw [hnorm] at hq
    rw [(hEderiv t).deriv]
    rw [real_inner_comm (A (g t - p t)) (g t - p t)]
    dsimp [E]
    nlinarith
  have hlowerDiff : ∀ t, 0 ≤ deriv E t + 2 * ν * E t := by
    intro t
    have hq := (hquad (g t - p t)).2
    have hdist := (hdualFlow t).1.2
    have hnorm : ‖g t - p t‖ = Metric.infDist (g t) (frictionBall r) := by
      simpa [dist_eq_norm] using hdist
    rw [hnorm] at hq
    rw [(hEderiv t).deriv]
    rw [real_inner_comm (A (g t - p t)) (g t - p t)]
    dsimp [E]
    nlinarith
  have hEderiv' : ∀ t, HasDerivAt E (deriv E t) t := by
    intro t
    convert hEderiv t using 1
    exact (hEderiv t).deriv
  have hlowerDistance : ∀ t ∈ Set.Ici t₀,
      Metric.infDist (g t₀) (frictionBall r) * Real.exp (-ν * (t - t₀)) ≤
        Metric.infDist (g t) (frictionBall r) := by
    intro t ht
    have henergy : E t₀ * Real.exp (-(2 * ν) * (t - t₀)) ≤ E t := by
      have hdiv : (Real.exp (2 * ν * t₀) * E t₀) / Real.exp (2 * ν * t) ≤ E t :=
        (div_le_iff₀ (Real.exp_pos _)).mpr
          (by simpa [mul_comm] using weighted_energy_monotone hEderiv' hlowerDiff ht)
      calc
        E t₀ * Real.exp (-(2 * ν) * (t - t₀)) =
            E t₀ * (Real.exp (2 * ν * t₀) / Real.exp (2 * ν * t)) := by
              rw [← Real.exp_sub]
              congr 2; ring
        _ = (Real.exp (2 * ν * t₀) * E t₀) / Real.exp (2 * ν * t) := by ring
        _ ≤ E t := hdiv
    have hsq : Metric.infDist (g t₀) (frictionBall r) ^ 2 *
        Real.exp (-(2 * ν) * (t - t₀)) ≤ Metric.infDist (g t) (frictionBall r) ^ 2 := by
      dsimp [E] at henergy
      nlinarith
    have hident : (Metric.infDist (g t₀) (frictionBall r) *
        Real.exp (-ν * (t - t₀))) ^ 2 =
        Metric.infDist (g t₀) (frictionBall r) ^ 2 * Real.exp (-(2 * ν) * (t - t₀)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2; ring
    exact (sq_le_sq₀ (mul_nonneg Metric.infDist_nonneg (le_of_lt (Real.exp_pos _)))
      Metric.infDist_nonneg).mp (by rwa [hident])
  refine ⟨Metric.infDist (g t₀) (frictionBall r) * Real.exp (μ * t₀),
    Metric.infDist (g t₀) (frictionBall r) * Real.exp (ν * t₀), μ, ν,
    mul_pos hd0 (Real.exp_pos _), mul_pos hd0 (Real.exp_pos _), hμ, hν, ?_, ?_, ?_⟩
  · intro t ht
    have henergy : E t ≤ E t₀ * Real.exp (-(2 * μ) * (t - t₀)) := by
      have hdiv : E t ≤ (Real.exp (2 * μ * t₀) * E t₀) / Real.exp (2 * μ * t) :=
        (le_div_iff₀ (Real.exp_pos _)).mpr
          (by simpa [mul_comm] using weighted_energy_antitone hEderiv' hupperDiff ht)
      calc
        E t ≤ (Real.exp (2 * μ * t₀) * E t₀) / Real.exp (2 * μ * t) := hdiv
        _ = E t₀ * (Real.exp (2 * μ * t₀) / Real.exp (2 * μ * t)) := by ring
        _ = E t₀ * Real.exp (2 * μ * t₀ - 2 * μ * t) := by rw [Real.exp_sub]
        _ = E t₀ * Real.exp (-(2 * μ) * (t - t₀)) := by congr 2; ring
    have hsq : Metric.infDist (g t) (frictionBall r) ^ 2 ≤
        Metric.infDist (g t₀) (frictionBall r) ^ 2 * Real.exp (-(2 * μ) * (t - t₀)) := by
      dsimp [E] at henergy
      nlinarith
    have hident : (Metric.infDist (g t₀) (frictionBall r) *
        Real.exp (-μ * (t - t₀))) ^ 2 =
        Metric.infDist (g t₀) (frictionBall r) ^ 2 * Real.exp (-(2 * μ) * (t - t₀)) := by
      rw [mul_pow, ← Real.exp_nat_mul]
      congr 2; ring
    have hdist : Metric.infDist (g t) (frictionBall r) ≤
        Metric.infDist (g t₀) (frictionBall r) * Real.exp (-μ * (t - t₀)) :=
      (sq_le_sq₀ Metric.infDist_nonneg
        (mul_nonneg Metric.infDist_nonneg (le_of_lt (Real.exp_pos _)))).mp
        (by rwa [hident])
    convert hdist using 1
    calc
      Metric.infDist (g t₀) (frictionBall r) * Real.exp (μ * t₀) * Real.exp (-μ * t) =
          Metric.infDist (g t₀) (frictionBall r) *
            (Real.exp (μ * t₀) * Real.exp (-μ * t)) := by ring
      _ = Metric.infDist (g t₀) (frictionBall r) * Real.exp (μ * t₀ + -μ * t) := by
        rw [← Real.exp_add]
      _ = Metric.infDist (g t₀) (frictionBall r) * Real.exp (-μ * (t - t₀)) := by congr 2; ring
  · intro t ht
    have hdist := hlowerDistance t ht
    convert hdist using 1
    calc
      Metric.infDist (g t₀) (frictionBall r) * Real.exp (ν * t₀) * Real.exp (-ν * t) =
          Metric.infDist (g t₀) (frictionBall r) *
            (Real.exp (ν * t₀) * Real.exp (-ν * t)) := by ring
      _ = Metric.infDist (g t₀) (frictionBall r) * Real.exp (ν * t₀ + -ν * t) := by
        rw [← Real.exp_add]
      _ = Metric.infDist (g t₀) (frictionBall r) * Real.exp (-ν * (t - t₀)) := by congr 2; ring
  · intro t ht hmem
    have hlower := hlowerDistance t ht
    have hposdist : 0 < Metric.infDist (g t) (frictionBall r) :=
      lt_of_lt_of_le (mul_pos hd0 (Real.exp_pos _)) hlower
    have hzero := Metric.infDist_zero_of_mem hmem
    linarith
```

## Proof explanation
The proof begins by applying `coercive_bounds_of_posdef_finiteDim` to the positive definite operator \(A\). This theorem states that on a finite-dimensional real inner product space, a positive definite continuous linear operator satisfies a two-sided coercivity estimate: there exist \(\mu,\nu>0\) such that for every \(\xi\in H\),
\[
\mu\|\xi\|^2\le \langle A\xi,\xi\rangle\le \nu\|\xi\|^2.
\]
These constants \(\mu,\nu\) will become the exponents in the upper and lower exponential bounds.

Next, the proof invokes `isInvertible_of_posdef_finiteDim`, which says that a positive definite continuous linear operator on such a space is invertible. The only concrete consequence used later is that \(A(A^{-1}y)=y\) for every \(y\in H\), allowing the inverse of \(A\) to be cancelled.

The proof then uses `hessian_quadratic_conjugate`. This result says that the derivative of the gradient of the conjugate of the quadratic function
\[
q\mapsto \frac12\langle Aq,q\rangle
\]
is the constant operator \(A^{-1}\). In other words, the Hessian of the conjugate is \(A^{-1}\). Consequently, the dual-flow equation supplied by `hdualFlow` can be rewritten as
\[
A^{-1}g'(t)+g(t)-p(t)=0.
\]
From this, the proof derives the velocity relation. For a fixed \(t\), rearranging gives
\[
A^{-1}g'(t)=p(t)-g(t).
\]
Applying \(A\) to both sides and using \(A(A^{-1}g'(t))=g'(t)\) yields
\[
g'(t)=A\bigl(p(t)-g(t)\bigr).
\]
This is the central differential relation used throughout the rest of the proof.

The proof then defines the energy
\[
E(t)=\frac12\operatorname{infDist}\bigl(g(t),\operatorname{frictionBall} r\bigr)^2.
\]
The initial distance is positive: by `frictionBall_not_mem_initial_infDist_pos`, since \(0\le r\) and \(r<\|g(t_0)\|\), we have
\[
0<\operatorname{infDist}\bigl(g(t_0),\operatorname{frictionBall} r\bigr).
\]
This positivity will be needed for the constants and for the final non-membership conclusion.

The next major step computes the derivative of \(E\). The proof uses `infDist_frictionBall_eq`, which says that for \(r>0\),
\[
\operatorname{infDist}\bigl(\xi,\operatorname{frictionBall} r\bigr)
=\max(\|\xi\|-r,0).
\]
Hence
\[
E(t)=\frac12\max(\|g(t)\|-r,0)^2.
\]
The proof then differentiates this expression. If \(g(t)=0\), continuity of \(g\) and \(r>0\) imply that \(\|g(s)\|<r\) eventually, so \(E\) is locally constant \(0\); the projection condition also gives \(p(t)=0\), so both sides of the derivative formula vanish. If \(g(t)\ne0\), the proof differentiates the norm using
\[
\frac{d}{ds}\|g(s)\|\Big|_{s=t}
=\frac{\langle g(t),g'(t)\rangle}{\|g(t)\|}.
\]
When \(r<\|g(t)\|\), the point is outside the ball. The proof identifies the projection \(p(t)\) by using the uniqueness part of `frictionBall_isChebyshev`, then `frictionBallProjection_eq_sub_softThresholder` and `softThresholder_apply`. Since \(r<\|g(t)\|\), the soft threshold is
\[
\left(1-\frac{r}{\|g(t)\|}\right)g(t),
\]
so the projection is
\[
p(t)=\frac{r}{\|g(t)\|}g(t).
\]
Substituting this into the velocity relation gives
\[
g(t)-p(t)=\left(1-\frac{r}{\|g(t)\|}\right)g(t),
\]
and a direct chain-rule computation yields
\[
E'(t)=-\bigl\langle g(t)-p(t),A(g(t)-p(t))\bigr\rangle.
\]
When \(\|g(t)\|\le r\), the proof shows \(p(t)=g(t)\), hence \(g'(t)=0\), and the derivative of \(E\) is again \(0\). At the boundary \(\|g(t)\|=r\), the nonsmooth point of \(\max(u,0)^2\) is handled by `hasDerivAt_max_sq_zero`, which states that if \(u\) is differentiable at \(t\) and \(u(t)=0\), then \(s\mapsto \max(u(s),0)^2\) has derivative \(0\) at \(t\). Thus in all cases,
\[
E'(t)=-\bigl\langle g(t)-p(t),A(g(t)-p(t))\bigr\rangle.
\]

The proof then combines this derivative formula with the coercive bounds. Since \(p(t)\) is a best approximation in the ball, one has
\[
\|g(t)-p(t)\|=\operatorname{infDist}\bigl(g(t),\operatorname{frictionBall} r\bigr).
\]
Applying the lower coercivity bound with \(\xi=g(t)-p(t)\) gives
\[
\mu\|g(t)-p(t)\|^2\le \bigl\langle A(g(t)-p(t)),g(t)-p(t)\bigr\rangle.
\]
Because
\[
E(t)=\frac12\|g(t)-p(t)\|^2,
\]
this implies
\[
E'(t)+2\mu E(t)\le 0.
\]
Similarly, applying the upper coercivity bound gives
\[
0\le E'(t)+2\nu E(t).
\]
These two differential inequalities are the input to the weighted energy lemmas.

For the upper bound, the proof uses `weighted_energy_antitone`. That theorem says that if \(E\) is differentiable at every point and
\[
E'(t)+aE(t)\le 0
\]
for all \(t\), then
\[
t\mapsto e^{at}E(t)
\]
is antitone. Taking \(a=2\mu\), for every \(t\ge t_0\) one gets
\[
e^{2\mu t}E(t)\le e^{2\mu t_0}E(t_0),
\]
so
\[
E(t)\le E(t_0)e^{-2\mu(t-t_0)}.
\]
Taking square roots, using nonnegativity of the distance, yields
\[
\operatorname{infDist}\bigl(g(t),\operatorname{frictionBall} r\bigr)
\le \operatorname{infDist}\bigl(g(t_0),\operatorname{frictionBall} r\bigr)e^{-\mu(t-t_0)}.
\]
Rewriting the right-hand side as
\[
\left(\operatorname{infDist}\bigl(g(t_0),\operatorname{frictionBall} r\bigr)e^{\mu t_0}\right)e^{-\mu t}
\]
gives the claimed upper bound with
\[
C_{\mathrm{upper}}
=\operatorname{infDist}\bigl(g(t_0),\operatorname{frictionBall} r\bigr)e^{\mu t_0}.
\]

For the lower bound, the proof uses `weighted_energy_monotone`. That theorem says that if \(E\) is differentiable at every point and
\[
0\le E'(t)+aE(t)
\]
for all \(t\), then
\[
t\mapsto e^{at}E(t)
\]
is monotone. Taking \(a=2\nu\), for every \(t\ge t_0\) one gets
\[
e^{2\nu t_0}E(t_0)\le e^{2\nu t}E(t),
\]
hence
\[
E(t_0)e^{-2\nu(t-t_0)}\le E(t).
\]
Taking square roots gives
\[
\operatorname{infDist}\bigl(g(t_0),\operatorname{frictionBall} r\bigr)
e^{-\nu(t-t_0)}
\le \operatorname{infDist}\bigl(g(t),\operatorname{frictionBall} r\bigr).
\]
Rewriting the left-hand side as
\[
\left(\operatorname{infDist}\bigl(g(t_0),\operatorname{frictionBall} r\bigr)e^{\nu t_0}\right)e^{-\nu t}
\]
gives the claimed lower bound with
\[
C_{\mathrm{lower}}
=\operatorname{infDist}\bigl(g(t_0),\operatorname{frictionBall} r\bigr)e^{\nu t_0}.
\]

Finally, the proof shows that \(g(t)\) never enters the friction ball. If \(g(t)\in\operatorname{frictionBall} r\), then by `Metric.infDist_zero_of_mem` one has
\[
\operatorname{infDist}\bigl(g(t),\operatorname{frictionBall} r\bigr)=0.
\]
But the lower bound already gives
\[
\operatorname{infDist}\bigl(g(t_0),\operatorname{frictionBall} r\bigr)e^{-\nu(t-t_0)}
\le \operatorname{infDist}\bigl(g(t),\operatorname{frictionBall} r\bigr),
\]
and the left-hand side is strictly positive because the initial distance is positive and the exponential is positive. This contradiction yields
\[
g(t)\notin \operatorname{frictionBall} r
\]
for every \(t\ge t_0\).

Throughout the proof, tactics such as `intro` introduce a fixed time or a hypothesis \(t\in \text{Set.Ici }t_0\), `rw` rewrites using the velocity relation, the distance formula, and exponential identities, `simp` unfolds definitions and elementary facts, `exact` closes goals by previously established results, and `linarith` or `nlinarith` combine the coercive quadratic inequalities with the energy expression to produce the differential inequalities and the final contradiction.

