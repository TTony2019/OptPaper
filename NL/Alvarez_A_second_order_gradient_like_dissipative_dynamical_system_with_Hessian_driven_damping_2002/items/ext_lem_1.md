## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/ext_lem_1.lean`

## Lean statement
```lean
theorem exists_rpow_abs_le_abs_deriv (h : ℝ → ℝ) (h0 : h 0 = 0) (han : AnalyticAt ℝ h 0) :
    ∃ σ θ : ℝ, 0 < σ ∧ 0 < θ ∧ θ < 1 / 2 ∧
      ∀ t : ℝ, |t| < σ → |h t| ^ (1 - θ) ≤ |deriv h t|
```

## Statement explanation
The theorem `exists_rpow_abs_le_abs_deriv` is a statement about a real-valued function of one real variable. Its data are a function $h:\mathbb R\to\mathbb R$, together with the hypotheses $h(0)=0$ and that $h$ is real-analytic at $0$. The conclusion is that there exist real numbers $\sigma$ and $\theta$ such that

$$
0<\sigma,\qquad 0<\theta,\qquad \theta<\frac12,
$$

and for every $t\in\mathbb R$,

$$
|t|<\sigma \quad\Longrightarrow\quad |h(t)|^{1-\theta}\le |h'(t)|.
$$

Here $h'(t)$ is Lean's one-dimensional derivative `deriv h t`. Since $\theta<1/2$, the exponent $1-\theta$ is greater than $1/2$, hence positive. Thus the theorem gives a local reverse-Hölder-type estimate saying that, near the origin, a positive real power of $|h|$ is bounded above by the absolute value of the derivative. The inequality is only asserted inside the small interval $(-\sigma,\sigma)$. If $h$ vanishes in an entire neighborhood of $0$, the statement is trivial because both sides vanish; otherwise the proof uses the analytic factorization of $h$ by its order of vanishing at $0$.

## Lean proof
```lean
by
  by_cases hz : ∀ᶠ z in 𝓝 (0 : ℝ), h z = 0
  · -- `h` vanishes in a neighbourhood of `0`
    rcases Metric.mem_nhds_iff.mp hz with ⟨ρ, hρ, hsub⟩
    refine ⟨ρ, 1 / 4, hρ, by norm_num, by norm_num, ?_⟩
    intro t ht
    have hht : h t = 0 := hsub (by simpa [Metric.mem_ball, Real.dist_eq, sub_zero] using ht)
    have hev : ∀ᶠ y in 𝓝 t, h y = 0 := by
      rw [Metric.eventually_nhds_iff]
      refine ⟨ρ - |t|, by linarith, ?_⟩
      intro y hy
      apply hsub
      rw [Metric.mem_ball, Real.dist_eq, sub_zero]
      have hy' : |y - t| < ρ - |t| := by simpa [Real.dist_eq] using hy
      calc |y| = |y - t + t| := by ring_nf
        _ ≤ |y - t| + |t| := abs_add_le _ _
        _ < ρ := by linarith
    have hdt : deriv h t = 0 := by
      rw [Filter.EventuallyEq.deriv_eq hev]
      simp
    rw [hht, hdt]
    simp only [abs_zero]
    rw [Real.zero_rpow (by norm_num : (1 : ℝ) - 1 / 4 ≠ 0)]
  · -- main case: `h` has a nontrivial local factorisation `t ↦ t ^ n * u t`
    obtain ⟨n, u, hu_an, hu_ne, hu_eq⟩ := han.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hz
    rcases Metric.mem_nhds_iff.mp hu_eq with ⟨ρ₁, hρ₁, hsub₁⟩
    have hn1 : 1 ≤ n := by
      by_contra hn
      have hn0 : n = 0 := by omega
      subst hn0
      have heq : h =ᶠ[𝓝 (0 : ℝ)] u := by
        filter_upwards [hu_eq] with z hzv
        simpa using hzv
      have key := heq.eq_of_nhds
      rw [h0] at key
      exact hu_ne key.symm
    set c : ℝ := |u 0| with hc
    have hcpos : 0 < c := by rw [hc]; exact abs_pos.mpr hu_ne
    -- continuity data for `u` and for `deriv u`
    obtain ⟨δu, hδu, hδusub⟩ :=
      Metric.continuousAt_iff.mp hu_an.continuousAt (c / 2) (by linarith)
    have hdu_cont : ContinuousAt (deriv u) 0 := by
      have h1 : ContinuousAt (fun z : ℝ => (fderiv ℝ u z) (1 : ℝ)) 0 :=
        (hu_an.fderiv.continuousAt).clm_apply continuousAt_const
      simpa only [fderiv_apply_one_eq_deriv] using h1
    set M : ℝ := |deriv u 0| + 1 with hM
    have hMpos : 0 < M := by rw [hM]; positivity
    obtain ⟨δd, hδd, hδdsub⟩ := Metric.continuousAt_iff.mp hdu_cont M hMpos
    have hev_an : ∀ᶠ t in 𝓝 (0 : ℝ), AnalyticAt ℝ u t :=
      (isOpen_analyticAt ℝ u).mem_nhds hu_an
    have hev_ud : ∀ᶠ t in 𝓝 (0 : ℝ), DifferentiableAt ℝ u t :=
      hev_an.mono fun t ht => (ht.contDiffAt (n := 1)).differentiableAt_one
    have hev_hd : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ᶠ y in 𝓝 t, h y = y ^ n * u y := by
      rw [Metric.eventually_nhds_iff]
      refine ⟨ρ₁, hρ₁, ?_⟩
      intro t ht
      rw [Metric.eventually_nhds_iff]
      refine ⟨ρ₁ - dist t 0, by linarith, ?_⟩
      intro y hy
      have hρ : dist y 0 < ρ₁ := by linarith [dist_triangle y t 0]
      simpa [smul_eq_mul] using hsub₁ (by simpa [Metric.mem_ball] using hρ)
    -- the exponent
    set θ : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hθ
    have hθpos : 0 < θ := by rw [hθ]; positivity
    have hθhalf : θ < 1 / 2 := by
      rw [hθ]
      have h2 : (2 : ℝ) < 2 * ((n : ℝ) + 1) := by
        have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        linarith
      have h := one_div_lt_one_div_of_lt (show (0 : ℝ) < 2 by norm_num) h2
      simpa using h
    have hθn : (n : ℝ) * θ < 1 := by
      rw [hθ, mul_one_div, div_lt_one (by positivity)]
      have hn : (1 : ℝ) ≤ n := by exact_mod_cast hn1
      linarith
    have h1nθ : 0 < 1 - (n : ℝ) * θ := by linarith
    -- the constants
    set A : ℝ := 3 * c / 2 with hA
    have hApos : 0 < A := by rw [hA]; linarith
    set B : ℝ := n * c / 4 with hB
    have hBpos : 0 < B := by rw [hB]; positivity
    set η₂ : ℝ := n * c / (8 * M) with hη₂
    have hη₂pos : 0 < η₂ := by rw [hη₂]; positivity
    set η₁ : ℝ := (B / A ^ (1 - θ)) ^ (1 / (1 - (n : ℝ) * θ)) with hη₁
    have hη₁pos : 0 < η₁ := by
      rw [hη₁]
      exact Real.rpow_pos_of_pos (div_pos hBpos (Real.rpow_pos_of_pos hApos _)) _
    have hδu_ev : ∀ᶠ t in 𝓝 (0 : ℝ), dist (u t) (u 0) < c / 2 := by
      rw [Metric.eventually_nhds_iff]
      exact ⟨δu, hδu, fun y hy => hδusub hy⟩
    have hδd_ev : ∀ᶠ t in 𝓝 (0 : ℝ), dist (deriv u t) (deriv u 0) < M := by
      rw [Metric.eventually_nhds_iff]
      exact ⟨δd, hδd, fun y hy => hδdsub hy⟩
    have hη₁_ev : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < η₁ := by
      rw [Metric.eventually_nhds_iff]
      refine ⟨η₁, hη₁pos, ?_⟩
      intro y hy
      rwa [Real.dist_eq, sub_zero] at hy
    have hη₂_ev : ∀ᶠ t in 𝓝 (0 : ℝ), |t| < η₂ := by
      rw [Metric.eventually_nhds_iff]
      refine ⟨η₂, hη₂pos, ?_⟩
      intro y hy
      rwa [Real.dist_eq, sub_zero] at hy
    have hev_ineq : ∀ᶠ t in 𝓝 (0 : ℝ), |h t| ^ (1 - θ) ≤ |deriv h t| := by
      filter_upwards [hu_eq, hδu_ev, hδd_ev, hev_ud, hev_hd, hη₁_ev, hη₂_ev]
        with t ht_eq ht_u ht_du ht_ud ht_hd ht_η₁ ht_η₂
      by_cases ht0 : t = 0
      · subst ht0
        simp [h0, abs_zero, Real.zero_rpow (by linarith : (1 : ℝ) - θ ≠ 0)]
      · have htabs : 0 < |t| := abs_pos.mpr ht0
        have hht : h t = t ^ n * u t := by simpa [smul_eq_mul] using ht_eq
        -- derivative formula
        have hprod : HasDerivAt (fun z : ℝ => z ^ n * u z)
            (n * t ^ (n - 1) * u t + t ^ n * deriv u t) t := by
          have h1 : HasDerivAt (fun z : ℝ => z ^ n) (n * t ^ (n - 1)) t := by
            simpa using hasDerivAt_pow n t
          exact h1.mul ht_ud.hasDerivAt
        have hderivh : deriv h t = n * t ^ (n - 1) * u t + t ^ n * deriv u t := by
          rw [Filter.EventuallyEq.deriv_eq ht_hd, hprod.deriv]
        have hfac : n * t ^ (n - 1) * u t + t ^ n * deriv u t
            = t ^ (n - 1) * (n * u t + t * deriv u t) := by
          have hpow : t ^ n = t ^ (n - 1) * t := by
            conv_lhs => rw [← Nat.sub_add_cancel hn1, pow_succ]
          rw [hpow]; ring
        -- bounds on `u t` in terms of `c`
        have hut_lo : c / 2 ≤ |u t| := by
          have h := ht_u
          rw [Real.dist_eq] at h
          have h' := abs_sub_abs_le_abs_sub (u 0) (u t)
          rw [← hc, abs_sub_comm] at h'
          linarith [le_abs_self (c - |u t|)]
        have hut_hi : |u t| ≤ A := by
          have h := ht_u
          rw [Real.dist_eq] at h
          have h2 : |u t| ≤ |u 0| + |u t - u 0| := by
            have h'' := abs_sub_abs_le_abs_sub (u t) (u 0)
            linarith [le_abs_self (|u t| - |u 0|)]
          rw [← hc] at h2
          rw [hA]
          linarith
        have hdu_hi : |deriv u t| ≤ 2 * M := by
          have h := ht_du
          rw [Real.dist_eq] at h
          have hM1 : |deriv u 0| = M - 1 := by rw [hM]; ring
          have h2 : |deriv u t| ≤ |deriv u 0| + |deriv u t - deriv u 0| := by
            have h'' := abs_sub_abs_le_abs_sub (deriv u t) (deriv u 0)
            linarith [le_abs_self (|deriv u t| - |deriv u 0|)]
          rw [hM1] at h2
          linarith
        have hsmall : |t| * |deriv u t| ≤ n * c / 4 := by
          have h1 : |t| * |deriv u t| ≤ η₂ * (2 * M) :=
            mul_le_mul (le_of_lt ht_η₂) hdu_hi (abs_nonneg _) (le_of_lt hη₂pos)
          have h2 : η₂ * (2 * M) = n * c / 4 := by
            rw [hη₂]; field_simp; ring
          linarith [h1, h2.le]
        -- lower bound on `|n * u t + t * deriv u t|`
        have hnt : B ≤ |n * u t + t * deriv u t| := by
          have hsplit : |n * u t| - |t * deriv u t| ≤ |n * u t + t * deriv u t| := by
            have h3 : |n * u t| ≤ |n * u t + t * deriv u t| + |t * deriv u t| := by
              calc |n * u t| = |(n * u t + t * deriv u t) + (-(t * deriv u t))| := by
                    congr 1; ring
                _ ≤ |n * u t + t * deriv u t| + |-(t * deriv u t)| := abs_add_le _ _
                _ = |n * u t + t * deriv u t| + |t * deriv u t| := by rw [abs_neg]
            linarith
          have h1 : |n * u t| = (n : ℝ) * |u t| := by
            rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
          have h2 : |t * deriv u t| = |t| * |deriv u t| := abs_mul _ _
          have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          have h3 : (n : ℝ) * (c / 2) ≤ (n : ℝ) * |u t| := mul_le_mul_of_nonneg_left hut_lo hn0
          have h4 : (n : ℝ) * (c / 2) = n * c / 2 := by ring
          have h5 : n * c / 2 - n * c / 4 = n * c / 4 := by ring
          rw [hB]
          linarith
        have hlower : |t| ^ (n - 1) * B ≤ |deriv h t| := by
          rw [hderivh, hfac, abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left hnt (by positivity)
        -- upper bound via `|h t| ≤ |t| ^ n * A`
        have hupper : |h t| ^ (1 - θ)
            ≤ |t| ^ (n - 1) * (|t| ^ (1 - (n : ℝ) * θ) * A ^ (1 - θ)) := by
          have hht' : |h t| ≤ |t| ^ (n : ℝ) * A := by
            rw [hht, abs_mul, abs_pow, ← Real.rpow_natCast |t| n]
            exact mul_le_mul_of_nonneg_left hut_hi (Real.rpow_nonneg (abs_nonneg t) (n : ℝ))
          have h1 : |h t| ^ (1 - θ)
              ≤ (|t| ^ (n : ℝ) * A) ^ (1 - θ) :=
            Real.rpow_le_rpow (abs_nonneg _) hht' (by linarith)
          have h2 : (|t| ^ (n : ℝ) * A) ^ (1 - θ)
              = (|t| ^ (n : ℝ)) ^ (1 - θ) * A ^ (1 - θ) :=
            Real.mul_rpow (Real.rpow_nonneg (abs_nonneg t) (n : ℝ)) hApos.le
          have h3 : (|t| ^ (n : ℝ)) ^ (1 - θ)
              = |t| ^ ((n : ℝ) * (1 - θ)) :=
            (Real.rpow_mul (abs_nonneg t) (n : ℝ) (1 - θ)).symm
          have h4 : |t| ^ ((n : ℝ) * (1 - θ))
              = |t| ^ ((n : ℝ) - 1) * |t| ^ (1 - (n : ℝ) * θ) := by
            have hs : (n : ℝ) * (1 - θ) = ((n : ℝ) - 1) + (1 - (n : ℝ) * θ) := by ring
            rw [hs, Real.rpow_add (abs_pos.mpr ht0)]
          have h5 : |t| ^ ((n : ℝ) - 1) = |t| ^ (n - 1) := by
            have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
              rw [Nat.cast_sub hn1]; norm_num
            rw [← hcast, Real.rpow_natCast]
          calc |h t| ^ (1 - θ) ≤ (|t| ^ (n : ℝ) * A) ^ (1 - θ) := h1
            _ = (|t| ^ (n : ℝ)) ^ (1 - θ) * A ^ (1 - θ) := h2
            _ = |t| ^ ((n : ℝ) * (1 - θ)) * A ^ (1 - θ) := by rw [h3]
            _ = (|t| ^ ((n : ℝ) - 1) * |t| ^ (1 - (n : ℝ) * θ)) * A ^ (1 - θ) := by rw [h4]
            _ = |t| ^ (n - 1) * (|t| ^ (1 - (n : ℝ) * θ) * A ^ (1 - θ)) := by
                  rw [h5]; ring
        -- the smallness condition fixes the exponent
        have hη₁' : |t| ^ (1 - (n : ℝ) * θ) ≤ B / A ^ (1 - θ) := by
          have hxpos : 0 < B / A ^ (1 - θ) :=
            div_pos hBpos (Real.rpow_pos_of_pos hApos (1 - θ))
          have h1 : |t| ^ (1 - (n : ℝ) * θ) < η₁ ^ (1 - (n : ℝ) * θ) :=
            Real.rpow_lt_rpow (abs_nonneg t) ht_η₁ h1nθ
          have h2 : η₁ ^ (1 - (n : ℝ) * θ) = B / A ^ (1 - θ) := by
            rw [hη₁, ← Real.rpow_mul hxpos.le, one_div, inv_mul_cancel₀ (ne_of_gt h1nθ),
              Real.rpow_one]
          linarith [h1, h2.le]
        have hfinal : |h t| ^ (1 - θ) ≤ |t| ^ (n - 1) * B := by
          have hA_nn : 0 ≤ A ^ (1 - θ) := Real.rpow_nonneg hApos.le (1 - θ)
          have h1 : |t| ^ (1 - (n : ℝ) * θ) * A ^ (1 - θ)
              ≤ (B / A ^ (1 - θ)) * A ^ (1 - θ) :=
            mul_le_mul_of_nonneg_right hη₁' hA_nn
          have h2 : (B / A ^ (1 - θ)) * A ^ (1 - θ) = B :=
            div_mul_cancel₀ B (ne_of_gt (Real.rpow_pos_of_pos hApos (1 - θ)))
          rw [h2] at h1
          exact le_trans hupper (mul_le_mul_of_nonneg_left h1 (by positivity))
        exact le_trans hfinal hlower
    rw [Metric.eventually_nhds_iff] at hev_ineq
    obtain ⟨σ, hσ, hσsub⟩ := hev_ineq
    refine ⟨σ, θ, hσ, hθpos, hθhalf, ?_⟩
    intro t ht
    exact hσsub (by rw [Real.dist_eq, sub_zero]; exact ht)
```

## Proof explanation
The proof begins with `by_cases hz`, splitting on whether

$$
\forallᶠ z\in \mathcal N(0),\quad h(z)=0,
$$

meaning that $h$ is eventually equal to $0$ near the origin.

In the first case, where $h$ vanishes in a neighborhood of $0$, the proof uses `Metric.mem_nhds_iff.mp hz` to extract a radius $\rho>0$ such that $h(z)=0$ whenever $\operatorname{dist}(z,0)<\rho$. In ordinary terms, $h$ is identically zero on the ball $B(0,\rho)$. The proof chooses

$$
\sigma=\rho,\qquad \theta=\frac14.
$$

Then $0<\rho$, $0<1/4$, and $1/4<1/2$, verified by `norm_num`. For $t$ with $|t|<\rho$, the value $h(t)$ is zero. To see that the derivative is also zero at such a $t$, the proof shows that $h$ is eventually equal to $0$ near $t$: because $t$ lies inside the open ball $B(0,\rho)$, there is a small neighborhood of $t$ still contained in that ball, where $h$ vanishes. The lemma `Filter.EventuallyEq.deriv_eq` then gives

$$
h'(t)=0,
$$

because the derivative depends only on the germ of the function at $t$, and the zero function has derivative $0$. The goal becomes

$$
|0|^{1-1/4}\le |0|.
$$

The left side is $0^{3/4}$, and `Real.zero_rpow` gives $0^{3/4}=0$ since $3/4\ne0$. Both sides are $0$, so the inequality holds.

In the main case, $h$ is not eventually zero at $0$. The analyticity hypothesis `han` is then used through the result `han.exists_eventuallyEq_pow_smul_nonzero_iff.mpr hz`. Specialized to this situation, it says that there exist a natural number $n$ and a real-valued function $u$, analytic at $0$, such that

$$
u(0)\ne0
$$

and

$$
h(z)=z^n u(z)
$$

for all $z$ in some neighborhood of $0$. This is the standard factorization of an analytic function according to the order of vanishing at $0$. The proof extracts a radius $\rho_1>0$ on which this factorization is valid.

The proof then shows $n\ge1$. If $n=0$, then $z^n u(z)=u(z)$, so $h$ is eventually equal to $u$ near $0$. Since eventual equality at a point implies equality at that point, one gets $h(0)=u(0)$. But $h(0)=0$ and $u(0)\ne0$, a contradiction. Hence $n\ge1$.

Next, let

$$
c=|u(0)|.
$$

Because $u(0)\ne0$, one has $c>0$. Continuity of $u$ at $0$, obtained from its analyticity, gives a radius $\delta_u>0$ such that if $|z|<\delta_u$, then

$$
|u(z)-u(0)|<\frac c2.
$$

This will later imply both a lower and an upper bound for $|u(t)|$.

The proof also needs control of $u'$ near $0$. Since $u$ is analytic at $0$, its derivative $u'$ is continuous at $0$. Using this continuity with the positive number

$$
M=|u'(0)|+1,
$$

one obtains a radius $\delta_d>0$ such that if $|z|<\delta_d$, then

$$
|u'(z)-u'(0)|<M.
$$

This later yields $|u'(t)|\le 2M$.

Because the set of points at which $u$ is analytic is open, $u$ is analytic at every $t$ sufficiently close to $0$. Hence $u$ is differentiable at those $t$. The proof also records that, for $t$ sufficiently close to $0$, the factorization $h(y)=y^n u(y)$ remains valid for all $y$ sufficiently close to $t$, by the triangle inequality.

The exponent is chosen as

$$
\theta=\frac{1}{2(n+1)}.
$$

Since $n\ge1$, this gives $0<\theta<1/2$. It also gives

$$
n\theta<1,
$$

so $1-n\theta>0$, and certainly $1-\theta>0$. The proof defines the positive constants

$$
A=\frac{3c}{2},\qquad B=\frac{nc}{4},
$$

and

$$
\eta_2=\frac{nc}{8M},\qquad
\eta_1=\left(\frac{B}{A^{1-\theta}}\right)^{1/(1-n\theta)}.
$$

These are all positive: $A>0$ because $c>0$, $B>0$ because $n\ge1$ and $c>0$, $\eta_2>0$ because $M>0$, and $\eta_1>0$ by positivity of real powers of positive numbers.

The proof then gathers the eventual facts: eventually $|t|<\eta_1$, eventually $|t|<\eta_2$, eventually $|u(t)-u(0)|<c/2$, and eventually $|u'(t)-u'(0)|<M$. The tactic `filter_upwards` combines these eventual statements and introduces a single $t$ satisfying all of them.

For such a $t$, the proof first treats the case $t=0$. Then $h(0)=0$, so the left side is $0^{1-\theta}$, which is $0$ because $1-\theta\ne0$, while the right side is $|h'(0)|\ge0$. The inequality is immediate.

Now assume $t\ne0$, so $|t|>0$. From the factorization,

$$
h(t)=t^n u(t).
$$

The product rule is applied to the function $z\mapsto z^n u(z)$. The derivative of $z^n$ at $t$ is $n t^{n-1}$, and the derivative of $u$ at $t$ is $u'(t)$, so

$$
\frac{d}{dz}\bigl(z^n u(z)\bigr)\Big|_{z=t}
=
n t^{n-1}u(t)+t^n u'(t).
$$

Since $h$ is eventually equal to this product near $t$, the derivative of $h$ at $t$ equals the same expression:

$$
h'(t)=n t^{n-1}u(t)+t^n u'(t).
$$

This factors as

$$
h'(t)=t^{n-1}\bigl(n u(t)+t u'(t)\bigr).
$$

The bounds on $u(t)$ are obtained from $|u(t)-u(0)|<c/2$. Since $c=|u(0)|$, one gets

$$
\frac c2\le |u(t)|\le \frac{3c}{2}=A.
$$

The bound on $u'(t)$ is obtained from $|u'(t)-u'(0)|<M$. Since $M=|u'(0)|+1$, this gives

$$
|u'(t)|\le 2M.
$$

Together with $|t|<\eta_2$, this implies

$$
|t|\,|u'(t)|\le \eta_2(2M)=\frac{nc}{4}.
$$

Also,

$$
|n u(t)|=n|u(t)|\ge n\frac c2=\frac{nc}{2}.
$$

Using the triangle inequality in the form

$$
|n u(t)|-|t u'(t)|\le |n u(t)+t u'(t)|,
$$

one obtains

$$
|n u(t)+t u'(t)|\ge \frac{nc}{2}-\frac{nc}{4}=\frac{nc}{4}=B.
$$

Therefore,

$$
|h'(t)|
=
|t^{n-1}|\,|n u(t)+t u'(t)|
=
|t|^{n-1}|n u(t)+t u'(t)|
\ge |t|^{n-1}B.
$$

This is the lower bound on $|h'(t)|$.

For the upper bound, first note that

$$
|h(t)|=|t^n u(t)|=|t|^n|u(t)|\le |t|^n A.
$$

Since $1-\theta>0$, the real-power function $x\mapsto x^{1-\theta}$ is increasing on nonnegative reals, so

$$
|h(t)|^{1-\theta}
\le
\bigl(|t|^n A\bigr)^{1-\theta}.
$$

Using the real-power identities, this becomes

$$
\bigl(|t|^n A\bigr)^{1-\theta}
=
|t|^{n(1-\theta)}A^{1-\theta}
=
|t|^{n-1}|t|^{1-n\theta}A^{1-\theta}.
$$

Here one uses

$$
n(1-\theta)=(n-1)+(1-n\theta).
$$

Because $|t|<\eta_1$ and $1-n\theta>0$, monotonicity of real powers gives

$$
|t|^{1-n\theta}<\eta_1^{1-n\theta}.
$$

By the definition of $\eta_1$,

$$
\eta_1^{1-n\theta}
=
\frac{B}{A^{1-\theta}}.
$$

Hence

$$
|t|^{1-n\theta}A^{1-\theta}\le B.
$$

Multiplying by $|t|^{n-1}\ge0$ yields

$$
|h(t)|^{1-\theta}\le |t|^{n-1}B.
$$

Combining this with the earlier lower bound

$$
|t|^{n-1}B\le |h'(t)|
$$

gives exactly

$$
|h(t)|^{1-\theta}\le |h'(t)|.
$$

Thus the desired inequality holds eventually near $0$.

Finally, the proof rewrites the eventual statement using `Metric.eventually_nhds_iff`. This says that an eventually true property near $0$ is true on some ball $B(0,\sigma)$ with $\sigma>0$. The proof extracts this $\sigma$. The same $\theta$ from above is used. The final `refine` packages

$$
\sigma,\quad \theta,\quad 0<\sigma,\quad 0<\theta,\quad \theta<\frac12,
$$

and leaves the universal inequality as the remaining goal. The last `intro t ht` introduces an arbitrary real $t$ satisfying $|t|<\sigma$, and the eventual ball statement gives the required inequality for that $t$. This completes the theorem.

