## Source file
`Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002/items/thm_2.lean`

## Lean statement
```lean
theorem analytic_bounded_din_converges {N : Type*} [Fintype N]
    (Φ : EuclideanSpace ℝ N → ℝ)
    (x : ℝ → EuclideanSpace ℝ N)
    (hΦ : AssumptionH (EuclideanSpace ℝ N) Φ)
    (hanalytic : AnalyticOnNhd ℝ Φ Set.univ)
    (hLoj : HasLojasiewiczGradientInequality Φ)
    (hsol : IsDINTrajectory (EuclideanSpace ℝ N) Φ α β x)
    (hxreg : ContDiff ℝ 2 x)
    (hbounded : Bornology.IsBounded (Set.range x)) :
    MeasureTheory.IntegrableOn (deriv x) (Set.Ioi (0 : ℝ)) MeasureTheory.volume ∧
    ∃ a, gradient Φ a = 0 ∧ Tendsto x atTop (nhds a)
```

## Statement explanation
The statement concerns a finite-dimensional Euclidean space $E=\mathbb R^N$ with $N$ finite, a potential $\Phi:E\to\mathbb R$, a curve $x:\mathbb R\to E$, and real parameters $\alpha,\beta$ appearing in the trajectory hypothesis. The assumptions are:

- `AssumptionH` for $\Phi$: the proof uses in particular that $\Phi$ is twice continuously differentiable, $C^2$. The full content of `AssumptionH` is not given in the excerpt, so only its visible consequences are used below.
- $\Phi$ is real analytic on all of $E$, expressed by $`\mathrm{AnalyticOnNhd}\mathbb R\,\Phi\,\mathrm{Set.univ}`$.
- $\Phi$ satisfies a Lojasiewicz gradient inequality, `HasLojasiewiczGradientInequality Φ`. The proof only uses this through the theorem `connected_critical_set_lojasiewicz`, which extracts a concrete exponent and constant near a compact connected critical set.
- $x$ is a trajectory of the DIN dynamical system with parameters $\alpha,\beta$, `IsDINTrajectory E Φ α β x`. From this hypothesis the proof first extracts $\alpha\gt 0$ and $\beta\gt 0$.
- $x$ is $C^2$ as a function of time, `ContDiff ℝ 2 x`.
- The range of $x$ is bounded, `Bornology.IsBounded (Set.range x)`, i.e. the whole trajectory $`\{x(t):t\in\mathbb R\}`$is bounded in$E$.

The conclusion has two parts. First,

$$
\mathrm{deriv}x \in L^1((0,\infty),E),
$$

meaning that the velocity of the trajectory is integrable on the positive half-line with respect to Lebesgue measure. Second, there exists a point $a\in E$ such that

$$
\nabla\Phi(a)=0
\qquad\text{and}\qquad
x(t)\to a \quad\text{as }t\to\infty.
$$

Thus the theorem says that a bounded $C^2$ DIN trajectory for an analytic potential satisfying the Lojasiewicz inequality has integrable velocity and converges to a critical point of $\Phi$.

## Lean proof
```lean
by
  classical
  have hα : 0 < α := hsol.1
  have hβ : 0 < β := hsol.2.1
  have hΦC2 : ContDiff ℝ 2 Φ := hΦ.twice_continuously_differentiable
  have hΦC1 : ContDiff ℝ 1 Φ := hΦC2.of_le (by norm_num)
  have hgradF : ∀ z, HasFDerivAt Φ (innerSL ℝ (gradient Φ z)) z := by
    intro z
    simpa [innerSL] using (hΦC1.differentiable (by norm_num) z).hasGradientAt.hasFDerivAt
  have hgradC1 : ContDiff ℝ 1 (gradient Φ) := by
    have hΦderivC1 : ContDiff ℝ 1 (fderiv ℝ Φ) := by
      exact (contDiff_succ_iff_fderiv.mp
        (show ContDiff ℝ (1 + 1) Φ by simpa using hΦC2)).2.2
    simpa [gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ N)).symm.contDiff.comp hΦderivC1
  have hcont : Continuous x ∧ Continuous (deriv x) :=
    din_trajectory_continuous Φ α β x hsol hxreg
  have hpartii := din_global_properties_part_ii Φ hΦ α β hα hβ (x 0) (deriv x 0) x
    rfl rfl hsol hxreg
  have hpartiii := din_global_properties_part_iii Φ hΦ α β hα hβ (x 0) (deriv x 0) x
    rfl rfl hsol hxreg (by
      apply hbounded.subset
      rintro q ⟨t, ht, rfl⟩
      exact ⟨t, rfl⟩)
  obtain ⟨hEprops, hvL2, hgL2, hΦlim, hreslim⟩ := hpartii
  obtain ⟨hvbound, haccbound, hgBound, hhessBound, hvlim, haccLim, hgLim⟩ := hpartiii
  let xI : Set.Ici (0 : ℝ) → EuclideanSpace ℝ N := fun t => x (t : ℝ)
  have hboundedI : Bornology.IsBounded (Set.range xI) := by
    apply hbounded.subset
    rintro q ⟨t, rfl⟩
    exact ⟨t, rfl⟩
  let φ : ℝ → EuclideanSpace ℝ N → EuclideanSpace ℝ N :=
    fun s _ => x (max s 0)
  have hφcont : Continuous (Function.uncurry φ) := by
    simpa [φ, Function.uncurry] using hcont.1.comp (continuous_fst.max continuous_const)
  have hcoe : Tendsto (fun t : Set.Ici (0 : ℝ) => (t : ℝ)) atTop atTop := by
    refine tendsto_atTop.2 fun R => ?_
    let q : Set.Ici (0 : ℝ) := ⟨max R 0, show (0 : ℝ) ≤ max R 0 from le_max_right _ _⟩
    filter_upwards [Ici_mem_atTop q] with t ht
    exact (le_max_left R 0).trans ht
  have hgradI : Tendsto (fun t : Set.Ici (0 : ℝ) => gradient Φ (xI t)) atTop (nhds 0) := by
    simpa [xI, Function.comp_def] using hgLim.comp hcoe
  have hΩ := omega_limit_properties Φ (gradient Φ) hΦC1 hgradF
    hgradC1.continuous xI ⟨φ, hφcont, (0 : EuclideanSpace ℝ N), by
      intro t
      simp [xI, φ, max_eq_left (show (t : ℝ) ≥ 0 from t.property)]⟩ hboundedI
      (fun t => deriv x (t : ℝ))
      (by simpa using hvlim.comp hcoe) hgradI
  obtain ⟨hAnon, hAcomp, hAconn, hdist, hAcrit⟩ := hΩ
  have hlojall := connected_critical_set_lojasiewicz
    (Set.univ : Set (EuclideanSpace ℝ N)) (omegaLimit xI) Φ hΦC2 isOpen_univ
    ⟨isOpen_univ, hanalytic⟩ hLoj (Set.subset_univ _) hAnon hAcrit hAconn
  obtain ⟨c0, hc⟩ := hlojall.1
  obtain ⟨σ, θ, c1, hσ, hθ, hθhalf, hconst1, hcθineq⟩ := hlojall.2 hAcomp
  have hc1 : c1 = c0 := by
    obtain ⟨z, hz⟩ := hAnon
    exact (hconst1 z hz).symm.trans (hc z hz)
  have hconst : ∀ (y : EuclideanSpace ℝ N),
      Metric.infDist y (omegaLimit xI) < σ →
        |Φ y - c0| ^ (1 - θ) ≤ ‖gradient Φ y‖ := by
    intro y hy
    simpa [hc1] using hcθineq y hy
  obtain ⟨lΦ, hlΦ⟩ := hΦlim
  have hc_lΦ : c0 = lΦ := by
    obtain ⟨z, hz⟩ := hAnon
    have hzA := hz
    rcases hz with ⟨s, hs, hsz⟩
    have hp1 : Tendsto (fun n => Φ (xI (s n))) atTop (nhds lΦ) :=
      hlΦ.comp hs
    have hp2 : Tendsto (fun n => Φ (xI (s n))) atTop (nhds (Φ z)) :=
      (hΦC1.continuous.tendsto z).comp hsz
    have : lΦ = Φ z := tendsto_nhds_unique hp1 hp2
    exact (hc z hzA).symm.trans this.symm
  let k : ℝ := α * β + 1
  let E : ℝ → ℝ := dinForwardEnergy Φ β k x
  have hk : 0 < k := by dsimp [k]; positivity
  have hsqrt : (Real.sqrt (α * β)) ^ 2 = α * β := Real.sq_sqrt (mul_nonneg hα.le hβ.le)
  have hElow : (1 - Real.sqrt (α * β)) ^ 2 ≤ k := by
    dsimp [k]
    nlinarith [Real.sqrt_nonneg (α * β)]
  have hEhigh : k ≤ (1 + Real.sqrt (α * β)) ^ 2 := by
    dsimp [k]
    nlinarith [Real.sqrt_nonneg (α * β)]
  obtain ⟨lE, hEanti, hElower, hElim⟩ := hEprops k hElow hEhigh
  have hElim' : Tendsto E atTop (nhds lE) := by simpa [E] using hElim
  have hEcalc : Tendsto E atTop (nhds (k * lΦ)) := by
    have hpot : Tendsto (fun t => k * Φ (x t)) atTop (nhds (k * lΦ)) :=
      tendsto_const_nhds.mul hlΦ
    have hkin : Tendsto
        (fun t => (1 / 2 : ℝ) * ‖deriv x t + β • gradient Φ (x t)‖ ^ 2)
        atTop (nhds 0) := by
      have := (hreslim.norm.pow 2).const_mul (1 / 2 : ℝ)
      simpa using this
    change Tendsto (fun t => k * Φ (x t) +
      (1 / 2 : ℝ) * ‖deriv x t + β • gradient Φ (x t)‖ ^ 2)
      atTop (nhds (k * lΦ))
    simpa using hpot.add hkin
  have hlE : lE = k * c0 := by
    have := tendsto_nhds_unique hElim' hEcalc
    rw [hc_lΦ]
    exact this
  let e : ℝ → ℝ := fun t => E t - lE
  have helim : Tendsto e atTop (nhds 0) := by
    simpa [e] using hElim'.sub
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => lE) atTop (nhds lE))
  have he_nonneg : ∀ t, 0 ≤ t → 0 ≤ e t := by
    intro t ht
    have hlower_t : lE ≤ E t := by
      apply le_of_tendsto hElim'
      filter_upwards [eventually_ge_atTop t] with s hts
      exact hEanti ht (ht.trans hts) hts
    exact sub_nonneg.mpr hlower_t
  let q : ℝ → Set.Ici (0 : ℝ) := fun t =>
    ⟨max t 0, show (0 : ℝ) ≤ max t 0 from le_max_right _ _⟩
  have hqtop : Tendsto q atTop atTop := by
    refine tendsto_atTop.2 fun r => ?_
    filter_upwards [eventually_ge_atTop (r : ℝ)] with t ht
    exact ht.trans (le_max_left _ _)
  have hdistReal : Tendsto
      (fun t : ℝ => Metric.infDist (x t) (omegaLimit xI)) atTop (nhds 0) := by
    have hraw := hdist.comp hqtop
    apply hraw.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    change Metric.infDist (x (max t 0)) (omegaLimit xI) =
      Metric.infDist (x t) (omegaLimit xI)
    rw [max_eq_left ht]
  have hdistEventually : ∀ᶠ t in atTop,
      Metric.infDist (x t) (omegaLimit xI) < σ := by
    rcases (Metric.tendsto_atTop.1 hdistReal) σ hσ with ⟨R, hR⟩
    filter_upwards [eventually_ge_atTop R] with t ht
    simpa only [Real.dist_eq, sub_zero, abs_of_nonneg (Metric.infDist_nonneg)] using hR t ht
  have hvEventually : ∀ᶠ t in atTop, ‖deriv x t‖ ≤ 1 := by
    have h := (Metric.tendsto_atTop.1 hvlim) 1 zero_lt_one
    rcases h with ⟨R, hR⟩
    filter_upwards [eventually_ge_atTop R] with t ht
    simpa [Real.dist_eq] using (le_of_lt (hR t ht))
  have hgEventually : ∀ᶠ t in atTop, ‖gradient Φ (x t)‖ ≤ 1 := by
    have h := (Metric.tendsto_atTop.1 hgLim) 1 zero_lt_one
    rcases h with ⟨R, hR⟩
    filter_upwards [eventually_ge_atTop R] with t ht
    simpa [Real.dist_eq] using (le_of_lt (hR t ht))
  have htail : ∀ᶠ t in atTop, 1 ≤ t ∧
      Metric.infDist (x t) (omegaLimit xI) < σ ∧
      ‖deriv x t‖ ≤ 1 ∧ ‖gradient Φ (x t)‖ ≤ 1 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ), hdistEventually, hvEventually,
      hgEventually] with t ht hd hv hg
    exact ⟨ht, hd, hv, hg⟩
  obtain ⟨T, hT⟩ := eventually_atTop.1 htail
  have hTpos : 0 < T := lt_of_lt_of_le zero_lt_one (hT T le_rfl).1
  let C : ℝ := k + 1 + β ^ 2
  have hC : 0 < C := by dsimp [C]; positivity
  let D : ℝ := 2 * C ^ (1 - θ)
  have hD : 0 < D := by
    dsimp [D]
    positivity
  have he_formula (t : ℝ) : e t =
      k * (Φ (x t) - c0) + (1 / 2) * ‖deriv x t + β • gradient Φ (x t)‖ ^ 2 := by
    simp only [e, E, dinForwardEnergy]
    rw [hlE]
    ring
  have hEderiv_at (s : ℝ) (hs : 0 ≤ s) : HasDerivAt E
      (-α * ‖deriv x s‖ ^ 2 - β * ‖gradient Φ (x s)‖ ^ 2) s := by
    simpa only [E, k] using din_energy_hasDerivAt Φ α β x hΦ hsol hxreg s hs
  have he_upper (t : ℝ) (ht : T ≤ t) :
      e t ^ (1 - θ) ≤ D * (‖deriv x t‖ + ‖gradient Φ (x t)‖) := by
    have htailt := hT t ht
    have ht0 : 0 ≤ t := hTpos.le.trans ht
    let v : ℝ := ‖deriv x t‖
    let g : ℝ := ‖gradient Φ (x t)‖
    let p : ℝ := |Φ (x t) - c0|
    have hv0 : 0 ≤ v := norm_nonneg _
    have hg0 : 0 ≤ g := norm_nonneg _
    have hp0 : 0 ≤ p := abs_nonneg _
    have hv1 : v ≤ 1 := htailt.2.2.1
    have hg1 : g ≤ 1 := htailt.2.2.2
    have hloj : p ^ (1 - θ) ≤ g := hconst (x t) htailt.2.1
    have hr : ‖deriv x t + β • gradient Φ (x t)‖ ≤ v + |β| * g := by
      calc
        ‖deriv x t + β • gradient Φ (x t)‖ ≤
            ‖deriv x t‖ + ‖β • gradient Φ (x t)‖ := norm_add_le _ _
        _ = v + |β| * g := by simp [v, g, norm_smul, Real.norm_eq_abs]
    have hrsq : ‖deriv x t + β • gradient Φ (x t)‖ ^ 2 ≤
        2 * (v ^ 2 + β ^ 2 * g ^ 2) := by
      have hs := sq_sum_le_two_sq_sum v (|β| * g)
      have hsq := pow_le_pow_left₀ (norm_nonneg _) hr 2
      calc
        ‖deriv x t + β • gradient Φ (x t)‖ ^ 2 ≤ (v + |β| * g) ^ 2 := hsq
        _ ≤ 2 * (v ^ 2 + (|β| * g) ^ 2) := hs
        _ = 2 * (v ^ 2 + β ^ 2 * g ^ 2) := by rw [mul_pow, sq_abs]
    have heplain : e t ≤ C * (p + v ^ 2 + g ^ 2) := by
      have habs : Φ (x t) - c0 ≤ p := le_abs_self _
      have hform := he_formula t
      have hk0 : 0 ≤ k := hk.le
      have hβsq : 0 ≤ β ^ 2 := sq_nonneg β
      have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
      have hg2 : 0 ≤ g ^ 2 := sq_nonneg g
      have hpot := mul_le_mul_of_nonneg_left habs hk0
      dsimp [C]
      nlinarith [hrsq, mul_nonneg hβsq hg2, mul_nonneg hk0 hp0]
    have he0 : 0 ≤ e t := he_nonneg t ht0
    have hsum0 : 0 ≤ p + v ^ 2 + g ^ 2 := by positivity
    have hepow := Real.rpow_le_rpow he0 heplain (by linarith [hθhalf] : 0 ≤ 1 - θ)
    have hmul : (C * (p + v ^ 2 + g ^ 2)) ^ (1 - θ) =
        C ^ (1 - θ) * (p + v ^ 2 + g ^ 2) ^ (1 - θ) :=
      Real.mul_rpow hC.le hsum0
    rw [hmul] at hepow
    have hsumPow : (p + v ^ 2 + g ^ 2) ^ (1 - θ) ≤
        p ^ (1 - θ) + (v ^ 2) ^ (1 - θ) + (g ^ 2) ^ (1 - θ) := by
      have hpExp0 : 0 ≤ 1 - θ := by linarith
      have hpExp1 : 1 - θ ≤ 1 := by linarith
      calc
        (p + v ^ 2 + g ^ 2) ^ (1 - θ) = ((p + v ^ 2) + g ^ 2) ^ (1 - θ) := by ring_nf
        _ ≤ (p + v ^ 2) ^ (1 - θ) + (g ^ 2) ^ (1 - θ) :=
          Real.rpow_add_le_add_rpow (by positivity) (by positivity) hpExp0 hpExp1
        _ ≤ (p ^ (1 - θ) + (v ^ 2) ^ (1 - θ)) + (g ^ 2) ^ (1 - θ) := by
          gcongr
          exact Real.rpow_add_le_add_rpow hp0 (by positivity) hpExp0 hpExp1
    have hExp : (1 : ℝ) ≤ 2 * (1 - θ) := by
      norm_num at hθhalf ⊢
      linarith
    have hvpow : (v ^ 2) ^ (1 - θ) ≤ v := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hv0]
      apply Real.rpow_le_self_of_le_one hv0 hv1
      exact hExp
    have hgpow : (g ^ 2) ^ (1 - θ) ≤ g := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul hg0]
      apply Real.rpow_le_self_of_le_one hg0 hg1
      exact hExp
    have hpowbound : (p + v ^ 2 + g ^ 2) ^ (1 - θ) ≤ 2 * (v + g) := by
      calc
        _ ≤ p ^ (1 - θ) + (v ^ 2) ^ (1 - θ) + (g ^ 2) ^ (1 - θ) := hsumPow
        _ ≤ g + v + g := by
          exact add_le_add (add_le_add hloj hvpow) hgpow
        _ ≤ 2 * (v + g) := by nlinarith [hv0]
    calc
      e t ^ (1 - θ) ≤ C ^ (1 - θ) * (p + v ^ 2 + g ^ 2) ^ (1 - θ) := hepow
      _ ≤ C ^ (1 - θ) * (2 * (v + g)) :=
        mul_le_mul_of_nonneg_left hpowbound (Real.rpow_nonneg hC.le _)
      _ = D * (‖deriv x t‖ + ‖gradient Φ (x t)‖) := by
        simp [D, v, g]
        ring
  have hrescont : Continuous (fun t => deriv x t + β • gradient Φ (x t)) := by
    exact hcont.2.add ((hgradC1.continuous.comp hcont.1).const_smul β)
  have hEcont : Continuous E := by
    dsimp [E, dinForwardEnergy]
    exact ((hΦC1.continuous.comp hcont.1).const_mul k).add
      ((hrescont.norm.pow 2).const_mul (1 / 2 : ℝ))
  have hecont : Continuous e := hEcont.sub continuous_const
  have hsumcont : Continuous (fun t => ‖deriv x t‖ + ‖gradient Φ (x t)‖) := by
    exact hcont.2.norm.add (hgradC1.continuous.comp hcont.1).norm
  by_cases hzero : ∃ t, T ≤ t ∧ e t = 0
  · obtain ⟨t0, ht0T, het0⟩ := hzero
    have ht00 : 0 ≤ t0 := hTpos.le.trans ht0T
    have hEt0 : E t0 = lE := by
      dsimp [e] at het0
      exact sub_eq_zero.mp het0
    have hEeq : ∀ s, t0 ≤ s → E s = lE := by
      intro s hs
      have hlow : lE ≤ E s := by
        have h := he_nonneg s (ht00.trans hs)
        change 0 ≤ E s - lE at h
        exact sub_nonneg.mp h
      have hupp : E s ≤ E t0 := hEanti ht00 (ht00.trans hs) hs
      exact le_antisymm (by rw [← hEt0]; exact hupp) hlow
    have hEderivzero : ∀ s, t0 ≤ s → deriv E s = 0 := by
      intro s hs
      have hEd := hEderiv_at s (ht00.trans hs)
      by_cases hst : s = t0
      · subst s
        have hEqW : E =ᶠ[nhdsWithin t0 (Set.Ici t0)] (fun _ => lE) := by
          filter_upwards [self_mem_nhdsWithin] with u hu
          exact hEeq u hu
        have hconstW : HasDerivWithinAt (fun _ : ℝ => lE) 0
            (Set.Ici t0) t0 := (hasDerivAt_const t0 lE).hasDerivWithinAt
        have hEW : HasDerivWithinAt E 0 (Set.Ici t0) t0 :=
          hconstW.congr_of_eventuallyEq hEqW hEt0
        have hu := UniqueDiffWithinAt.eq_deriv (Set.Ici t0)
          (uniqueDiffOn_Ici t0 t0 Set.self_mem_Ici) hEW hEd.hasDerivWithinAt
        calc
          deriv E t0 = -α * ‖deriv x t0‖ ^ 2 - β * ‖gradient Φ (x t0)‖ ^ 2 := hEd.deriv
          _ = 0 := hu.symm
      · have hst' : t0 < s := lt_of_le_of_ne hs (Ne.symm hst)
        have hEq : E =ᶠ[nhds s] (fun _ => lE) := by
          filter_upwards [Ioi_mem_nhds hst'] with u hu
          exact hEeq u hu.le
        have hconst : HasDerivAt (fun _ : ℝ => lE) 0 s := hasDerivAt_const s lE
        have hEc : HasDerivAt E 0 s := hconst.congr_of_eventuallyEq hEq
        calc
          deriv E s = -α * ‖deriv x s‖ ^ 2 - β * ‖gradient Φ (x s)‖ ^ 2 := hEd.deriv
          _ = 0 := hEd.unique hEc
    have hvgradzero : ∀ s, t0 ≤ s →
        deriv x s = 0 ∧ gradient Φ (x s) = 0 := by
      intro s hs
      have hEd := hEderiv_at s (ht00.trans hs)
      have hval := hEderivzero s hs
      rw [hEd.deriv] at hval
      have hvsq : ‖deriv x s‖ ^ 2 = 0 := by
        nlinarith [sq_nonneg ‖deriv x s‖, sq_nonneg ‖gradient Φ (x s)‖]
      have hgsq : ‖gradient Φ (x s)‖ ^ 2 = 0 := by
        nlinarith [sq_nonneg ‖deriv x s‖, sq_nonneg ‖gradient Φ (x s)‖]
      exact ⟨norm_eq_zero.mp (sq_eq_zero_iff.mp hvsq),
        norm_eq_zero.mp (sq_eq_zero_iff.mp hgsq)⟩
    have hxconst : ∀ s, t0 ≤ s → x s = x t0 := by
      intro s hs
      apply (convex_Ici t0).is_const_of_fderivWithin_eq_zero
        ((hxreg.differentiable (by norm_num)).differentiableOn)
      · intro u hu
        rw [fderivWithin_eq_fderiv (uniqueDiffOn_Ici t0 u hu)
          (hxreg.differentiable (by norm_num) u)]
        rw [← toSpanSingleton_deriv]
        simp [hvgradzero u hu |>.1]
      · exact hs
      · exact Set.self_mem_Ici
    have htailint : MeasureTheory.IntegrableOn (deriv x) (Set.Ici t0) := by
      exact (MeasureTheory.integrableOn_zero (s := Set.Ici t0)).congr_fun
        (fun u hu => (hvgradzero u hu).1.symm) measurableSet_Ici
    have hfinint : MeasureTheory.IntegrableOn (deriv x) (Set.Ioc 0 t0) := by
      exact (hcont.2.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hcover : Set.Ioi (0 : ℝ) ⊆ Set.Ioc 0 t0 ∪ Set.Ici t0 := by
      intro s hs
      by_cases hst : s ≤ t0
      · exact Or.inl ⟨hs, hst⟩
      · exact Or.inr (le_of_not_ge hst)
    have hderivint : MeasureTheory.IntegrableOn (deriv x) (Set.Ioi (0 : ℝ)) :=
      (hfinint.union htailint).mono_set hcover
    have hxlim : Tendsto x atTop (nhds (x t0)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop t0] with s hs
      exact (hxconst s hs).symm
    exact ⟨hderivint, ⟨x t0, (hvgradzero t0 le_rfl).2, hxlim⟩⟩
  · have hnonzero : ∀ t, T ≤ t → e t ≠ 0 := by
      intro t ht hzt
      exact hzero ⟨t, ht, hzt⟩
    let F : ℝ → ℝ := fun t => e t ^ θ
    have hFcont : Continuous F := by
      dsimp [F]
      exact hecont.rpow continuous_const (fun _ => Or.inr hθ)
    have hFlim : Tendsto F atTop (nhds 0) := by
      have h := helim.rpow_const (Or.inr hθ.le)
      simpa [F, Real.zero_rpow hθ.ne'] using h
    have hFderiv : ∀ t, T ≤ t →
        HasDerivAt F
          ((-α * ‖deriv x t‖ ^ 2 - β * ‖gradient Φ (x t)‖ ^ 2) * θ *
            e t ^ (θ - 1)) t := by
      intro t ht
      have heD : HasDerivAt e
          (-α * ‖deriv x t‖ ^ 2 - β * ‖gradient Φ (x t)‖ ^ 2) t := by
        simpa only [e] using (hEderiv_at t (hTpos.le.trans ht)).sub_const lE
      simpa [F] using heD.rpow_const (Or.inl (hnonzero t ht))
    have hFderivInt : MeasureTheory.IntegrableOn (deriv F) (Set.Ioi T) := by
      apply MeasureTheory.integrableOn_Ioi_deriv_of_nonpos'
        (a := T) (g := F) (g' := deriv F)
      · intro t ht
        have hd := hFderiv t ht
        exact hd.congr_deriv hd.deriv.symm
      · intro t ht
        have hfd := (hFderiv t ht.le).deriv
        rw [hfd]
        have hdiss : -α * ‖deriv x t‖ ^ 2 - β * ‖gradient Φ (x t)‖ ^ 2 ≤ 0 := by
          nlinarith [sq_nonneg ‖deriv x t‖, sq_nonneg ‖gradient Φ (x t)‖]
        have hp : 0 ≤ e t ^ (θ - 1) := Real.rpow_nonneg
          (he_nonneg t (hTpos.le.trans ht.le)) _
        exact mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg hdiss hθ.le) hp
      · exact hFlim
    let m : ℝ := min α β
    let A : ℝ := θ * m / (2 * D)
    have hm : 0 < m := by dsimp [m]; exact lt_min hα hβ
    have hA : 0 < A := by dsimp [A]; positivity
    have hpoint : ∀ t, T ≤ t → A *
        (‖deriv x t‖ + ‖gradient Φ (x t)‖) ≤ -deriv F t := by
      intro t ht
      let v : ℝ := ‖deriv x t‖
      let g : ℝ := ‖gradient Φ (x t)‖
      have hv0 : 0 ≤ v := norm_nonneg _
      have hg0 : 0 ≤ g := norm_nonneg _
      have hs0 : 0 ≤ v + g := by positivity
      have hepos : 0 < e t := lt_of_le_of_ne
        (he_nonneg t (hTpos.le.trans ht)) (Ne.symm (hnonzero t ht))
      have hep : 0 < e t ^ (1 - θ) := Real.rpow_pos_of_pos hepos _
      have hdiss : m / 2 * (v + g) ^ 2 ≤ α * v ^ 2 + β * g ^ 2 := by
        have hmva : m * v ^ 2 ≤ α * v ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_left α β) (sq_nonneg v)
        have hmgb : m * g ^ 2 ≤ β * g ^ 2 :=
          mul_le_mul_of_nonneg_right (min_le_right α β) (sq_nonneg g)
        have hsq := sq_sum_le_two_sq_sum v g
        nlinarith
      have hcross : A * (v + g) * e t ^ (1 - θ) ≤
          θ * (α * v ^ 2 + β * g ^ 2) := by
        have hmul := mul_le_mul_of_nonneg_left (he_upper t ht)
          (mul_nonneg (le_of_lt hA) hs0)
        calc
          A * (v + g) * e t ^ (1 - θ) ≤
              A * (v + g) * (D * (v + g)) := hmul
          _ = θ * (m / 2 * (v + g) ^ 2) := by
            dsimp [A]
            field_simp
          _ ≤ θ * (α * v ^ 2 + β * g ^ 2) :=
            mul_le_mul_of_nonneg_left hdiss hθ.le
      have hfd := (hFderiv t ht).deriv
      have hprod : (-deriv F t) * e t ^ (1 - θ) =
          θ * (α * v ^ 2 + β * g ^ 2) := by
        rw [hfd]
        calc
          -((-α * v ^ 2 - β * g ^ 2) * θ * e t ^ (θ - 1)) *
                e t ^ (1 - θ) =
              θ * (α * v ^ 2 + β * g ^ 2) *
                (e t ^ (θ - 1) * e t ^ (1 - θ)) := by ring
          _ = θ * (α * v ^ 2 + β * g ^ 2) := by
            rw [← Real.rpow_add hepos]
            norm_num
      have hmul := hcross.trans_eq hprod.symm
      exact le_of_mul_le_mul_right (by simpa [v, g] using hmul) hep
    have hderivtail : MeasureTheory.IntegrableOn (deriv x) (Set.Ioi T) := by
      apply integrableOn_of_norm_interval_tail_bound
        (deriv x) T (F T / A) hcont.2
      intro R hTR
      have hleft : IntervalIntegrable
          (fun s => A * (‖deriv x s‖ + ‖gradient Φ (x s)‖))
          MeasureTheory.volume T R :=
        (hsumcont.const_mul A).intervalIntegrable T R
      have hFint : IntervalIntegrable (deriv F) MeasureTheory.volume T R := by
        apply (intervalIntegrable_iff).2
        rw [Set.uIoc_of_le hTR]
        exact hFderivInt.mono_set (by
          intro s hs
          exact hs.1)
      have hright : IntervalIntegrable (fun s => -deriv F s)
          MeasureTheory.volume T R := by
        simpa only [Pi.neg_apply] using hFint.neg
      have hmono := intervalIntegral.integral_mono_on hTR hleft hright (by
        intro s hs
        exact hpoint s hs.1)
      have hfund : ∫ s in T..R, deriv F s = F R - F T :=
        intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun s hs => by
          rw [Set.uIcc_of_le hTR] at hs
          have hd := hFderiv s hs.1
          exact hd.congr_deriv hd.deriv.symm) hFint
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg,
        hfund] at hmono
      have hFR : 0 ≤ F R := by
        dsimp [F]
        exact Real.rpow_nonneg (he_nonneg R (hTpos.le.trans hTR)) _
      have hsumBound : ∫ s in T..R,
          (‖deriv x s‖ + ‖gradient Φ (x s)‖) ≤ F T / A := by
        apply (le_div_iff₀ hA).2
        nlinarith
      have hnormle := intervalIntegral.integral_mono_on hTR
        (hcont.2.norm.intervalIntegrable (μ := MeasureTheory.volume) T R)
        (hsumcont.intervalIntegrable (μ := MeasureTheory.volume) T R)
        (fun s _ => le_add_of_nonneg_right (norm_nonneg _))
      exact hnormle.trans hsumBound
    have hfinint : MeasureTheory.IntegrableOn (deriv x) (Set.Ioc 0 T) := by
      exact (hcont.2.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
    have hcover : Set.Ioi (0 : ℝ) ⊆ Set.Ioc 0 T ∪ Set.Ioi T := by
      intro s hs
      by_cases hst : s ≤ T
      · exact Or.inl ⟨hs, hst⟩
      · exact Or.inr (not_le.mp hst)
    have hderivint : MeasureTheory.IntegrableOn (deriv x) (Set.Ioi (0 : ℝ)) :=
      (hfinint.union hderivtail).mono_set hcover
    let a : EuclideanSpace ℝ N := Filter.atTop.limUnder x
    have hxlim : Tendsto x atTop (nhds a) :=
      MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi
        (f := x) (f' := deriv x) (a := 0)
        (fun t ht => (hxreg.differentiable (by norm_num) t).hasDerivAt) hderivint
    have hgradxlim : Tendsto (fun t => gradient Φ (x t)) atTop
        (nhds (gradient Φ a)) :=
      (hgradC1.continuous.tendsto a).comp hxlim
    have hgrad_a : gradient Φ a = 0 := tendsto_nhds_unique hgradxlim hgLim
    exact ⟨hderivint, ⟨a, hgrad_a, hxlim⟩⟩
```

## Proof explanation
The proof begins by extracting the positivity of the damping parameters from the trajectory hypothesis. From

```math
\text{hsol}:\mathrm{IsDINTrajectory} E\,\Phi\,\alpha\,\beta\,x
```

the proof obtains

$$
\alpha>0,\qquad \beta>0.
$$

It also weakens the $C^2$ regularity of $\Phi$ supplied by `AssumptionH` to $C^1$, and then records that the gradient of $\Phi$ represents its Fréchet derivative:

$$
\forall z\in E,\qquad
\Phi \text{ has Fréchet derivative }
h\mapsto \langle \nabla\Phi(z),h\rangle
\text{ at }z.
$$

This is the meaning of the line producing `hgradF`; the identifier `innerSL` is the continuous linear identification of the inner product with the dual space. The proof also shows that the gradient map

$$
\nabla\Phi:E\to E
$$

is $C^1$. The command `simp` and `simpa` unfold the definition of `gradient` and use the continuous linear equivalence between $E$ and its dual, so that the $C^1$ regularity of $`fderiv\,\Phi`$transfers to$\nabla\Phi$.

Next, the lemma `din_trajectory_continuous` is applied to $x$. Its conclusion gives

$$
x \text{ is continuous},\qquad \mathrm{deriv}x \text{ is continuous}.
$$

The proof then invokes the two global DIN estimates `din_global_properties_part_ii` and `din_global_properties_part_iii`. The first theorem, applied with $\Phi,\alpha,\beta,x(0),\mathrm{deriv}x(0)$, gives four families of conclusions. For every $\ell$ satisfying

$$
(1-\sqrt{\alpha\beta})^2\le \ell\le (1+\sqrt{\alpha\beta})^2,
$$

the forward energy

```math
E_\ell(t)
=\ell\,\Phi(x(t))
+\frac12\left\|\mathrm{deriv}x(t)+\beta\nabla\Phi(x(t))\right\|^2
```

is antitone on $t\ge0$, bounded below, and convergent as $t\to\infty$. In addition,

$$
\mathrm{deriv}x\in L^2((0,\infty)),
\qquad
\nabla\Phi(x(\cdot))\in L^2((0,\infty)),
$$

the scalar function $\Phi(x(t))$ has a limit as $t\to\infty$, and

$$
\mathrm{deriv}x(t)+\beta\nabla\Phi(x(t))\to 0
$$

as $t\to\infty$. The second global theorem, applied under the boundedness hypothesis, yields in particular

$$
\mathrm{deriv}x(t)\to 0,\qquad
\nabla\Phi(x(t))\to 0
$$

as $t\to\infty$. The proof extracts these limits as `hvlim` and `hgLim`.

The trajectory is then restricted to nonnegative times by defining

$$
x_I(t)=x(t),\qquad t\in[0,\infty).
$$

The boundedness of the full range of $x$ implies that the range of $x_I$ is bounded. The proof also defines a continuous semiflow by

$$
\varphi(s,y)=x(\max(s,0)).
$$

This is continuous because $x$ is continuous and $(s,y)\mapsto \max(s,0)$ is continuous. Thus $x_I(t)=\varphi(t,0)$ for $t\ge0$, so the hypotheses of `omega_limit_properties` are satisfied. The coercion map $t\mapsto (t:\mathbb R)$ from $[0,\infty)$ to $\mathbb R$ tends to infinity, so the already established limits for $\mathrm{deriv}x(t)$ and $\nabla\Phi(x(t))$ transfer to the restricted trajectory.

Applying `omega_limit_properties` gives the following facts about the omega-limit set

```math
\omega(x_I)
=\{a\in E:\exists t_n\ge0,\ t_n\to\infty,\ x(t_n)\to a\}.
```

The set $\omega(x_I)$ is nonempty, compact, and connected; the distance

$$
\mathrm{infDist}(x_I(t),\omega(x_I))
$$

tends to $0$ as $t\to\infty$; and every point of $\omega(x_I)$ is a critical point of $\Phi$, i.e.

$$
\forall z\in\omega(x_I),\qquad \nabla\Phi(z)=0.
$$

Now the proof applies `connected_critical_set_lojasiewicz` with $\Omega=\mathrm{Set.univ}$ and $A=\omega(x_I)$. This theorem states that for a $C^2$ and real-analytic potential on an open set, satisfying the Lojasiewicz gradient inequality, any nonempty connected critical set $A$ lying in the open set has constant value of $\Phi$ on $A$. Moreover, if $A$ is compact, then there exist constants $\sigma\gt 0$, $\theta\in(0,1/2)$, and $c$ such that $\Phi=c$ on $A$ and, for every $y$ with

$$
\mathrm{infDist}(y,A)<\sigma,
$$

one has the concrete Lojasiewicz inequality

```math
|\Phi(y)-c|^{1-\theta}\le \|\nabla\Phi(y)\|.
```

In the present proof, this gives a value $c_0$ with $\Phi=c_0$ on $\omega(x_I)$, and constants $\sigma,\theta,c_1$ with $0\lt \sigma$, $0\lt \theta\lt 1/2$, $\Phi=c_1$ on $\omega(x_I)$, and

```math
\mathrm{infDist}(y,\omega(x_I))<\sigma
\implies
|\Phi(y)-c_0|^{1-\theta}\le \|\nabla\Phi(y)\|.
```

The proof reconciles $c_1=c_0$ by choosing a point of $\omega(x_I)$. It also shows that $c_0$ equals the limit $l_\Phi$ of $\Phi(x(t))$. Indeed, if $z\in\omega(x_I)$ and $x(t_n)\to z$, then $\Phi(x(t_n))\to l_\Phi$ by the already established limit, and $\Phi(x(t_n))\to \Phi(z)$ by continuity of $\Phi$. Uniqueness of limits gives $l_\Phi=\Phi(z)=c_0$.

The proof then sets

$$
k=\alpha\beta+1,\qquad E(t)=E_k(t).
$$

The value $k$ lies in the admissible interval

$$
(1-\sqrt{\alpha\beta})^2\le k\le (1+\sqrt{\alpha\beta})^2,
$$

so the energy conclusions from `din_global_properties_part_ii` apply to $E$. Hence $E$ is antitone on $t\ge0$, bounded below, and converges to some $l_E$. But $E$ can also be evaluated from its definition:

```math
E(t)
=k\,\Phi(x(t))
+\frac12\left\|\mathrm{deriv}x(t)+\beta\nabla\Phi(x(t))\right\|^2.
```

Since $\Phi(x(t))\to l_\Phi=c_0$ and the residual term tends to $0$, one gets

$$
E(t)\to k c_0.
$$

Therefore $l_E=k c_0$. The proof defines

$$
e(t)=E(t)-l_E.
$$

Then $e(t)\to0$, and because $E$ is antitone and has limit $l_E$, one has $e(t)\ge0$ for $t\ge0$.

Next, the proof chooses a time $T$ so that for all $t\ge T$,

```math
t\ge1,\qquad
\mathrm{infDist}(x(t),\omega(x_I))<\sigma,\qquad
\|\mathrm{deriv}x(t)\|\le1,\qquad
\|\nabla\Phi(x(t))\|\le1.
```

The first condition is just eventual positivity, the second follows from the attraction property of the omega-limit set, and the last two follow from the limits of velocity and gradient to $0$.

Let

$$
C=k+1+\beta^2,\qquad D=2C^{1-\theta}.
$$

For $t\ge T$, write

```math
v=\|\mathrm{deriv}x(t)\|,\qquad
g=\|\nabla\Phi(x(t))\|,\qquad
p=|\Phi(x(t))-c_0|.
```

By the Lojasiewicz inequality, since $\mathrm{infDist}(x(t),\omega(x_I))\lt \sigma$,

$$
p^{1-\theta}\le g.
$$

The triangle inequality gives

```math
\left\|\mathrm{deriv}x(t)+\beta\nabla\Phi(x(t))\right\|
\le v+|\beta|g.
```

Using the elementary inequality

$$
(a+b)^2\le 2(a^2+b^2),
$$

which is exactly `sq_sum_le_two_sq_sum`, one obtains

```math
\left\|\mathrm{deriv}x(t)+\beta\nabla\Phi(x(t))\right\|^2
\le 2(v^2+\beta^2g^2).
```

Combining this with $\Phi(x(t))-c_0\le p$ gives

$$
e(t)\le C(p+v^2+g^2).
$$

Raising both sides to the nonnegative power $1-\theta$ and using subadditivity of $x\mapsto x^{1-\theta}$ on nonnegative numbers, namely

$$
(a+b)^{1-\theta}\le a^{1-\theta}+b^{1-\theta}
$$

for $\theta\lt 1$, yields

$$
(p+v^2+g^2)^{1-\theta}
\le
p^{1-\theta}+(v^2)^{1-\theta}+(g^2)^{1-\theta}.
$$

Because $v\le1$, $g\le1$, and $2(1-\theta)\ge1$, one has

$$
(v^2)^{1-\theta}\le v,\qquad
(g^2)^{1-\theta}\le g.
$$

Together with $p^{1-\theta}\le g$, this gives

$$
(p+v^2+g^2)^{1-\theta}\le 2(v+g).
$$

Therefore

```math
e(t)^{1-\theta}\le D(v+g)
=D\bigl(\|\mathrm{deriv}x(t)\|+\|\nabla\Phi(x(t))\|\bigr).
```

This is the key estimate on the tail $t\ge T$.

The proof then establishes continuity of the residual

$$
t\mapsto \mathrm{deriv}x(t)+\beta\nabla\Phi(x(t)),
$$

of the energy $E$, of $e$, and of

```math
t\mapsto \|\mathrm{deriv}x(t)\|+\|\nabla\Phi(x(t))\|.
```

These continuity facts are needed for the later integration arguments.

A case split is then made.

Case 1: suppose there exists $t_0\ge T$ with $e(t_0)=0$. Then $E(t_0)=l_E$. Since $E$ is antitone and $e(t)\ge0$, for every $s\ge t_0$ one has

$$
l_E\le E(s)\le E(t_0)=l_E,
$$

so $E(s)=l_E$ on $[t_0,\infty)$. Hence the derivative of $E$ is zero on that tail. By `din_energy_hasDerivAt`, for $s\ge0$,

```math
\mathrm{deriv}E(s)
=-\alpha\|\mathrm{deriv}x(s)\|^2
-\beta\|\nabla\Phi(x(s))\|^2.
```

For $s\ge t_0$, the left-hand side is $0$. Since $\alpha\gt 0$, $\beta\gt 0$, and both squared norms are nonnegative, this forces

$$
\mathrm{deriv}x(s)=0,\qquad
\nabla\Phi(x(s))=0
$$

for all $s\ge t_0$. In particular, $\nabla\Phi(x(t_0))=0$.

Because $\mathrm{deriv}x=0$ on $[t_0,\infty)$, the curve $x$ is constant there: the proof uses the fact that a differentiable function on the convex interval $[t_0,\infty)$ with zero Fréchet derivative throughout is constant. Thus

$$
x(s)=x(t_0)\qquad(s\ge t_0).
$$

Consequently $x(t)\to x(t_0)$ as $t\to\infty$. For integrability, the tail integral on $[t_0,\infty)$ vanishes because $\mathrm{deriv}x=0$ there, while $[0,t_0]$ is finite and $\mathrm{deriv}x$ is continuous, hence integrable. Covering $(0,\infty)$ by these two pieces gives

$$
\mathrm{deriv}x\in L^1((0,\infty),E).
$$

Together with $\nabla\Phi(x(t_0))=0$, this proves the desired conclusion in this case.

Case 2: suppose $e(t)\ne0$ for every $t\ge T$. Since $e(t)\ge0$, actually $e(t)\gt 0$ on the tail. Define

$$
F(t)=e(t)^\theta.
$$

Then $F$ is continuous, and $F(t)\to0$ because $e(t)\to0$ and $\theta\gt 0$. Using the derivative of $E$ and hence of $e$, the proof obtains

```math
\mathrm{deriv}F(t)
=\left(
-\alpha\|\mathrm{deriv}x(t)\|^2
-\beta\|\nabla\Phi(x(t))\|^2
\right)
\theta\,e(t)^{\theta-1}.
```

The bracketed term is nonpositive because it is the negative sum of nonnegative terms, and $e(t)^{\theta-1}\gt 0$, so $\mathrm{deriv}F(t)\le0$. Thus $F$ is nonincreasing on the tail. The proof invokes `integrableOn_Ioi_deriv_of_nonpos'`, which says that if a function has a nonpositive derivative on a tail and tends to $0$ at infinity, then its derivative is integrable on that tail. Hence

$$
\mathrm{deriv}F\in L^1((T,\infty)).
$$

Now set

$$
m=\min(\alpha,\beta),\qquad
A=\frac{\theta m}{2D}.
$$

Both are positive. The proof proves the pointwise inequality

```math
A\bigl(\|\mathrm{deriv}x(t)\|+\|\nabla\Phi(x(t))\|\bigr)
\le
-\mathrm{deriv}F(t)
```

for all $t\ge T$. To see this, again write $`v=\|\mathrm{deriv}x(t)\|`$and$`g=\|\nabla\Phi(x(t))\|`$. From$m\le\alpha$,$m\le\beta$, and$(v+g)^2\le 2(v^2+g^2)$, one gets

$$
\frac m2(v+g)^2\le \alpha v^2+\beta g^2.
$$

On the other hand, the bound $e(t)^{1-\theta}\le D(v+g)$ implies

$$
A(v+g)e(t)^{1-\theta}
\le
A D(v+g)^2
=\frac{\theta m}{2}(v+g)^2
\le
\theta(\alpha v^2+\beta g^2).
$$

But differentiating $F$ gives

$$
(-\mathrm{deriv}F(t))e(t)^{1-\theta}
=\theta(\alpha v^2+\beta g^2),
$$

using $e(t)^{\theta-1}e(t)^{1-\theta}=e(t)^0=1$. Dividing by the positive number $e(t)^{1-\theta}$ yields the desired inequality.

Integrating this inequality from $T$ to $R\ge T$ gives

```math
A\int_T^R
\bigl(\|\mathrm{deriv}x(s)\|+\|\nabla\Phi(x(s))\|\bigr)\,ds
\le
F(T)-F(R)
\le
F(T),
```

because $F(R)\ge0$. Since

```math
\|\mathrm{deriv}x(s)\|
\le
\|\mathrm{deriv}x(s)\|+\|\nabla\Phi(x(s))\|,
```

one obtains

```math
\int_T^R \|\mathrm{deriv}x(s)\|\,ds
\le
\frac{F(T)}{A}.
```

This is a uniform tail bound. The lemma `integrableOn_of_norm_interval_tail_bound` then applies, because $\mathrm{deriv}x$ is continuous, and yields

$$
\mathrm{deriv}x\in L^1((T,\infty),E).
$$

On the finite interval $(0,T]$, integrability follows from continuity of $\mathrm{deriv}x$. Covering $(0,\infty)$ by $(0,T]$ and $(T,\infty)$ gives

$$
\mathrm{deriv}x\in L^1((0,\infty),E).
$$

Finally, the proof defines

$$
a=\lim_{t\to\infty} x(t)
$$

as the `limUnder` of $x$ at infinity. It applies `MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi`: since $x$ is differentiable with derivative $\mathrm{deriv}x$, and since $\mathrm{deriv}x$ is integrable on $(0,\infty)$, the curve $x(t)$ has a limit at infinity, and that limit is the `limUnder`. Thus

$$
x(t)\to a \qquad(t\to\infty).
$$

Because $\nabla\Phi$ is continuous and $x(t)\to a$, we also have

$$
\nabla\Phi(x(t))\to \nabla\Phi(a).
$$

But the global DIN estimate already gave

$$
\nabla\Phi(x(t))\to 0.
$$

By uniqueness of limits,

$$
\nabla\Phi(a)=0.
$$

Therefore $a$ is a critical point and $x(t)\to a$, completing the proof of

$$
\mathrm{deriv}x\in L^1((0,\infty),E)
\quad\text{and}\quad
\exists a,\ \nabla\Phi(a)=0,\ x(t)\to a.
$$

Throughout the proof, the tactic `intro` introduces arbitrary points or indices when proving universally quantified statements; `rw` and `simp` unfold definitions such as the forward energy and rewrite algebraic identities; `exact` closes goals by applying the cited theorem or hypothesis with the required arguments; and `linarith` or `nlinarith` handles the arithmetic and order inequalities, such as positivity of $k$, nonnegativity of squares, and the comparison between $m/2(v+g)^2$ and $\alpha v^2+\beta g^2$.

