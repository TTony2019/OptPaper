## Source file
`Alvarez_Minimizing_property_second_order_dissipative_2000/items/ext_thm_2.lean`

## Lean statement
```lean
theorem scalar_damped_even_strong_convergence_result {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (hPhiDiff : ContDiff ℝ 1 Phi)
    (hPhiConvex : ConvexOn ℝ Set.univ Phi)
    (hPhiBoundedBelow : ∃ m : ℝ, ∀ x : H, m ≤ Phi x)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0)
    (hMin : (argmin Phi (by
      rcases hPhiBoundedBelow with ⟨m, hm⟩
      exact ⟨m, by rintro _ ⟨x, rfl⟩; exact hm x⟩)).Nonempty)
    (hEven : IsEvenFunction Phi) :
    ∃ uhat ∈ argmin Phi (by
      rcases hPhiBoundedBelow with ⟨m, hm⟩
      exact ⟨m, by rintro _ ⟨x, rfl⟩; exact hm x⟩), Tendsto sys.u atTop (nhds uhat)
```

## Statement explanation
The theorem is a strong-convergence result for a second-order damped trajectory associated with an even convex potential.

Let $H$ be a real inner-product space which is complete, so $H$ is a real Hilbert space. The data are a dissipation coefficient $\gamma \in \mathbb R$, a potential $\Phi : H \to \mathbb R$, a gradient map $\mathrm{gradPhi} : H \to H$, initial position and velocity $u_0,v_0 \in H$, and a dissipative system

$$
\mathrm{sys} : \mathrm{DissipativeSystem}(\gamma,\Phi,\mathrm{gradPhi},u_0,v_0)
$$

whose position trajectory is denoted by $\mathrm{sys.u}$. The theorem assumes that $\Phi$ is globally $C^1$, that $\Phi$ is convex on all of $H$, that $\Phi$ is bounded below, and that the minimizer set of $\Phi$ is nonempty. It also assumes that $\Phi$ is even, i.e. $\Phi(-x)=\Phi(x)$ for all $x\in H$.

The minimizer set is written using the local definition of $\mathrm{argmin}$. For a bounded-below function $F$,

$$
\mathrm{argmin} F = \left\{x \mid F(x)=\inf F(H)\right\},
$$

where the Lean statement uses $\mathrm{sInf}(\mathrm{Set.range} F)$. Thus membership in $\mathrm{argmin}\Phi$ means exactly that $\Phi(x)$ equals the infimum of the values of $\Phi$.

The assumption `hMin` says that this minimizer set is nonempty. The conclusion is that there exists a point $\hat u\in \mathrm{argmin}\Phi$ such that the whole trajectory $\mathrm{sys.u}$ converges strongly to $\hat u$ as time tends to infinity:

$$
\exists \hat u\in \mathrm{argmin}\Phi,\qquad
\mathrm{sys.u}(t)\underset{t\to\infty}{\longrightarrow}\hat u.
$$

The convergence is in the norm topology of $H$, not merely weak convergence. The proof obtains weak convergence to a minimizer from a general minimizing property, then upgrades it to strong convergence by proving a uniform Cauchy estimate for the tail of the trajectory.

## Lean proof
```lean
by
  rcases hPhiBoundedBelow with ⟨m, hm⟩
  let hBdd : BddBelow (Set.range Phi) := ⟨m, by
    rintro _ ⟨x, rfl⟩
    exact hm x⟩
  have hZeroMin : (0 : H) ∈ argmin Phi hBdd :=
    even_convex_zero_mem_argmin hPhiConvex hEven hBdd
  have hMin' : (argmin Phi hBdd).Nonempty := by
    simpa only [proof_irrel_heq] using hMin
  let hPhi : HasPotentialAssumption Phi :=
    ⟨hPhiDiff, hPhiConvex, ⟨m, hm⟩⟩
  have hBdd' : potential_range_bddBelow hPhi = hBdd := by
    apply Subsingleton.elim
  have hMin'' : (argmin Phi (potential_range_bddBelow hPhi)).Nonempty := by
    simpa only [hBdd'] using hMin'
  obtain ⟨hvel2, hvel0, hPhi0, hweak⟩ :=
    scalar_damped_minimizing_property hPhi sys
  obtain ⟨uhat, hUhatMin, hUhatWeak⟩ := hweak hMin''
  have hUhatValue : Phi uhat = sInf (Set.range Phi) := hUhatMin
  have hDistanceIneq : ∀ ⦃t : ℝ⦄, 0 < t →
      deriv (deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - uhat‖ ^ 2)) t +
          gamma * deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s - uhat‖ ^ 2) t ≤
        ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
    intro t ht
    have h := even_distance_damped_ineq hPhi sys uhat ht
    have hgap : Phi uhat - Phi (sys.u t) ≤ 0 := by
      rw [hUhatValue]
      linarith [potential_sInf_le hPhi (sys.u t)]
    linarith
  have hZeroValue : Phi (0 : H) = sInf (Set.range Phi) := hZeroMin
  have hZeroDistanceIneq : ∀ ⦃t : ℝ⦄, 0 < t →
      deriv (deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s‖ ^ 2)) t +
          gamma * deriv (fun s => (1 / 2 : ℝ) * ‖sys.u s‖ ^ 2) t ≤
        ‖fderiv ℝ sys.u t 1‖ ^ 2 := by
    intro t ht
    have h := even_distance_damped_ineq hPhi sys (0 : H) ht
    have hgap : Phi (0 : H) - Phi (sys.u t) ≤ 0 := by
      rw [hZeroValue]
      linarith [potential_sInf_le hPhi (sys.u t)]
    simpa using (h.trans (by linarith :
      Phi (0 : H) - Phi (sys.u t) + ‖fderiv ℝ sys.u t 1‖ ^ 2 ≤
        ‖fderiv ℝ sys.u t 1‖ ^ 2))
  -- Work on the positive-time tail.  Shifting by one lets the two scalar
  -- convergence lemmas be applied without ever differentiating at the
  -- one-sided endpoint `0` of the trajectory.
  let theta : ℝ → ℝ := fun t => (1 / 2 : ℝ) * ‖sys.u (t + 1)‖ ^ 2
  have htheta : ContDiffOn ℝ 2 theta (Set.Ici 0) := by
    have hu : ContDiffOn ℝ 2 (fun t : ℝ => sys.u (t + 1)) (Set.Ici 0) := by
      exact sys.contDiff.comp
        ((contDiff_id.add contDiff_const).contDiffOn)
        (fun t ht => by
          change 0 ≤ t at ht
          simpa only [Set.mem_Ici] using add_nonneg ht (by norm_num))
    exact contDiffOn_const.mul (ContDiffOn.norm_sq ℝ hu)
  have hthetaDiff : ∀ t ∈ Set.Ici (0 : ℝ), DifferentiableAt ℝ theta t := by
    intro t ht
    change 0 ≤ t at ht
    have hu : DifferentiableAt ℝ (fun s : ℝ => sys.u (s + 1)) t :=
      (dissipativeSystem_differentiableAt_pos sys (by nlinarith : 0 < t + 1)).comp t
        (differentiableAt_id.add_const 1)
    simpa [theta] using (differentiableAt_const (c := (1 / 2 : ℝ))).mul (hu.norm_sq ℝ)
  have homega : ContDiffOn ℝ 1 (fun t => deriv theta t) (Set.Ici 0) := by
    have hwithin : ContDiffOn ℝ 1 (derivWithin theta (Set.Ici 0)) (Set.Ici 0) :=
      htheta.derivWithin (uniqueDiffOn_Ici 0) (by norm_num)
    exact hwithin.congr fun t ht => by
      rw [deriv, derivWithin,
        fderivWithin_eq_fderiv ((uniqueDiffOn_Ici 0) t ht) (hthetaDiff t ht)]
  have hthetaDeriv : ∀ s : ℝ, -1 < s →
      deriv theta s = deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r‖ ^ 2) (s + 1) := by
    intro s hs
    have hspos : 0 < s + 1 := by linarith
    have hphiDiff : DifferentiableAt ℝ (fun r => (1 / 2 : ℝ) * ‖sys.u r‖ ^ 2) (s + 1) := by
      have hu := dissipativeSystem_differentiableAt_pos sys hspos
      simpa using (differentiableAt_const (c := (1 / 2 : ℝ))).mul (hu.norm_sq ℝ)
    change deriv ((fun r => (1 / 2 : ℝ) * ‖sys.u r‖ ^ 2) ∘ fun r : ℝ => r + 1) s = _
    convert deriv_comp s hphiDiff (differentiableAt_id.add_const 1) using 1 <;> simp
  have hthetaSecond : ∀ s ∈ Set.Ici (0 : ℝ),
      deriv (deriv theta) s =
        deriv (deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r‖ ^ 2)) (s + 1) := by
    intro s hs
    have hspos : 0 < s + 1 := by
      change 0 ≤ s at hs
      linarith
    have hderivDiff : DifferentiableAt ℝ
        (deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r‖ ^ 2)) (s + 1) := by
      have hcd : ContDiffAt ℝ 2 (fun r => (1 / 2 : ℝ) * ‖sys.u r‖ ^ 2) (s + 1) := by
        have hu : ContDiffOn ℝ 2 sys.u (Set.Ioi 0) :=
          sys.contDiff.mono Set.Ioi_subset_Ici_self
        exact (contDiffOn_const.mul (ContDiffOn.norm_sq ℝ hu)).contDiffAt
          (Ioi_mem_nhds hspos)
      exact (hcd.derivWithin (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have hevent : deriv theta =ᶠ[nhds s] fun r =>
        deriv (fun q => (1 / 2 : ℝ) * ‖sys.u q‖ ^ 2) (r + 1) := by
      filter_upwards [Ioi_mem_nhds (by linarith : -1 < s)] with r hr
      exact hthetaDeriv r hr
    rw [Filter.EventuallyEq.deriv_eq hevent]
    convert deriv_comp s hderivDiff (differentiableAt_id.add_const 1) using 1 <;> simp
  have hforce : IntegrableOn (fun s : ℝ => ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2)
      (Set.Ici 0) := by
    have heq := (measurePreserving_add_right volume (1 : ℝ)).integrableOn_comp_preimage
      (Homeomorph.addRight (1 : ℝ)).isClosedEmbedding.measurableEmbedding
        (f := fun t : ℝ => ‖fderiv ℝ sys.u t 1‖ ^ 2) (s := Set.Ici 0)
    rw [Set.preimage_add_const_Ici] at heq
    have hfull : IntegrableOn ((fun t : ℝ => ‖fderiv ℝ sys.u t 1‖ ^ 2) ∘
        fun s : ℝ => s + 1) (Set.Ici (0 - 1)) := heq.mpr hvel2
    exact hfull.mono_set (Set.Ici_subset_Ici.mpr (by norm_num : (0 - 1 : ℝ) ≤ 0))
  have hineq : ∀ s ∈ Set.Ici (0 : ℝ),
      deriv (deriv theta) s + gamma * deriv theta s ≤
        ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2 := by
    intro s hs
    rw [hthetaSecond s hs, hthetaDeriv s (by
      change 0 ≤ s at hs
      linarith)]
    exact hZeroDistanceIneq (by
      change 0 ≤ s at hs
      linarith)
  have hpositive : IntegrableOn (fun s => max (deriv theta s) 0) (Set.Ici 0) :=
    positive_part_integrable_of_damped_inequality (fun s => deriv theta s)
      (fun s => ‖fderiv ℝ sys.u (s + 1) 1‖ ^ 2) gamma homega sys.gamma_pos hineq hforce
  obtain ⟨normTailLimit, hNormSqTail⟩ :=
    converges_of_integrable_positive_derivative theta (htheta.of_le (by norm_num))
      (by
        refine ⟨0, ?_⟩
        intro s hs
        dsimp [theta]
        positivity) hpositive
  have hNormSqShift : Tendsto (fun s : ℝ => ‖sys.u (s + 1)‖ ^ 2) atTop
      (nhds (2 * normTailLimit)) := by
    have hscaled := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (2 : ℝ)) atTop (nhds 2)).mul
      hNormSqTail
    simpa [theta] using hscaled
  have hNormSq : Tendsto (fun t : ℝ => ‖sys.u t‖ ^ 2) atTop
      (nhds (2 * normTailLimit)) := by
    have hshift : Tendsto (fun t : ℝ => t - 1) atTop atTop := by
      simpa [sub_eq_add_neg] using
        (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
    convert hNormSqShift.comp hshift using 1
    ext t
    congr 2
    ring
  -- The causal error term from the paper is now available as a genuine
  -- convergent primitive.  The remaining task is to connect it to the
  -- moving-endpoint differential estimate (2.9).
  obtain ⟨Herr, hCausalError⟩ := even_causal_error_converges sys hvel2
  let Herror : ℝ → ℝ := fun r => (3 / 2 : ℝ) *
    ∫ theta in 1..r, ∫ s in 0..theta,
      Real.exp (-gamma * (theta - s)) * ‖fderiv ℝ sys.u s 1‖ ^ 2
  have hHerror : Tendsto Herror atTop (nhds Herr) := by
    simpa [Herror] using hCausalError
  -- The coefficient of the initial derivative in the two-time integrating
  -- factor estimate is nonnegative.  Together with the uniform endpoint
  -- bound above, this is the tail estimate needed after that estimate is
  -- integrated.
  obtain ⟨C, hCnonneg, hCtail⟩ :=
    eventually_bounded_even_endpoint_deriv sys hNormSq
  have hEndpointTerm : ∀ ⦃t T : ℝ⦄, 1 ≤ t → t ≤ T →
      (Real.exp (-gamma * (t - 1)) - Real.exp (-gamma * (T - 1))) / gamma ≥ 0 ∧
      ∀ᶠ T in atTop,
        ((Real.exp (-gamma * (t - 1)) - Real.exp (-gamma * (T - 1))) / gamma) *
          deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
            (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2) 1 ≤
          ((Real.exp (-gamma * (t - 1)) - Real.exp (-gamma * (T - 1))) / gamma) * C := by
    intro t T ht hle
    have hneg : -gamma * (T - 1) ≤ -gamma * (t - 1) := by
      nlinarith [sys.gamma_pos]
    have hexp : Real.exp (-gamma * (T - 1)) ≤ Real.exp (-gamma * (t - 1)) :=
      Real.exp_le_exp.mpr hneg
    have hcoef : 0 ≤
        (Real.exp (-gamma * (t - 1)) - Real.exp (-gamma * (T - 1))) / gamma := by
      exact div_nonneg (sub_nonneg.mpr hexp) (le_of_lt sys.gamma_pos)
    refine ⟨hcoef, ?_⟩
    filter_upwards [hCtail, eventually_ge_atTop T] with S hS hTS
    have hnegS : -gamma * (S - 1) ≤ -gamma * (t - 1) := by
      nlinarith [sys.gamma_pos]
    have hcoefS : 0 ≤
        (Real.exp (-gamma * (t - 1)) - Real.exp (-gamma * (S - 1))) / gamma := by
      exact div_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hnegS))
        (le_of_lt sys.gamma_pos)
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans hS) hcoefS
  let vfun : ℝ → H := fun s => fderiv ℝ sys.u s 1
  let qfun : ℝ → ℝ := fun s => (3 / 2 : ℝ) * ‖vfun s‖ ^ 2
  have hvOn : ContinuousOn vfun (Set.Ici (1 : ℝ)) := by
    intro s hs
    have hlocal : ContDiffAt ℝ 2 sys.u s :=
      sys.contDiff.contDiffAt (Ici_mem_nhds (lt_of_lt_of_le (by norm_num) hs))
    have hv : ContDiffAt ℝ 1 vfun s := by
      simpa [vfun] using
        (hlocal.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).clm_apply
          (contDiffAt_const (c := (1 : ℝ)))
    exact hv.continuousAt.continuousWithinAt
  have hqOn : ContinuousOn qfun (Set.Ici (1 : ℝ)) := by
    have hn : ContinuousOn (fun s : ℝ => ‖vfun s‖) (Set.Ici (1 : ℝ)) :=
      continuous_norm.continuousOn.comp hvOn (fun _ _ => Set.mem_univ _)
    simpa [qfun] using continuousOn_const.mul (hn.pow 2)
  let vext : ℝ → H := fun s => vfun (max s 1)
  let qext : ℝ → ℝ := fun s => qfun (max s 1)
  have hvext : Continuous vext := by
    apply ContinuousOn.comp_continuous hvOn (continuous_id.max continuous_const)
    intro s
    exact show 1 ≤ max s 1 from le_max_right _ _
  have hqext : Continuous qext := by
    apply ContinuousOn.comp_continuous hqOn (continuous_id.max continuous_const)
    intro s
    exact show 1 ≤ max s 1 from le_max_right _ _
  have hq_eq : ∀ s : ℝ, 1 ≤ s → qext s = qfun s := by
    intro s hs
    simp [qext, qfun, max_eq_left hs]
  have hNestedInt : ∀ {t T : ℝ}, 1 ≤ t → t ≤ T →
      IntervalIntegrable (fun theta => ∫ s in (1 : ℝ)..theta,
        Real.exp (-gamma * (theta - s)) * qfun s) volume t T := by
    intro t T ht hT
    let F : ℝ → ℝ → ℝ := fun theta s =>
      Real.exp (-gamma * (theta - s)) * qext s
    have hFcont : Continuous (Function.uncurry F) := by
      dsimp [F]
      fun_prop
    have hJcont : Continuous (fun theta : ℝ =>
        ∫ s in (1 : ℝ)..theta, F theta s) := by
      simpa [F] using
        (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
          (a₀ := (1 : ℝ)) hFcont continuous_id)
    have hJint : IntervalIntegrable (fun theta : ℝ =>
        ∫ s in (1 : ℝ)..theta, F theta s) volume t T :=
      hJcont.continuousOn.intervalIntegrable_of_Icc hT
    refine hJint.congr ?_
    intro theta htheta
    apply intervalIntegral.integral_congr_ae
    simp only [Set.uIoc_of_le hT] at htheta
    have htheta1 : 1 ≤ theta := le_trans ht htheta.1.le
    simp only [Set.uIoc_of_le htheta1] at *
    filter_upwards with s hs
    have hs1 : 1 ≤ s := by
      exact hs.1.le
    simp [F, hq_eq s hs1]
  have hGDiff : ∀ T : ℝ, ContDiffOn ℝ 2
      (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
        (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2) (Set.Ici (1 : ℝ)) := by
    intro T
    have hu : ContDiffOn ℝ 2 sys.u (Set.Ici (1 : ℝ)) :=
      sys.contDiff.mono (Set.Ici_subset_Ici.mpr (by norm_num))
    have hc : ContDiffOn ℝ 2 (fun _ : ℝ => ‖sys.u T‖ ^ 2) (Set.Ici (1 : ℝ)) :=
      contDiffOn_const
    have hu_sub : ContDiffOn ℝ 2 (fun r : ℝ => sys.u r - sys.u T)
        (Set.Ici (1 : ℝ)) := hu.sub contDiffOn_const
    exact ((ContDiffOn.norm_sq ℝ hu).sub hc).sub
      (contDiffOn_const.mul (ContDiffOn.norm_sq ℝ hu_sub))
  have hGDerivDiff : ∀ T : ℝ, ContDiffOn ℝ 1 (deriv
      (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
        (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2)) (Set.Ici (1 : ℝ)) := by
    intro T
    have hG2 := hGDiff T
    have hwithin := hG2.derivWithin (m := 1) (uniqueDiffOn_Ici 1) (by norm_num)
    refine hwithin.congr ?_
    intro s hs
    rw [deriv, derivWithin,
      fderivWithin_eq_fderiv ((uniqueDiffOn_Ici 1) s hs)]
    have hu : DifferentiableAt ℝ sys.u s :=
      dissipativeSystem_differentiableAt_pos sys (lt_of_lt_of_le (by norm_num) hs)
    have hGdiff : DifferentiableAt ℝ
        (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
          (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2) s := by
      have hc : DifferentiableAt ℝ (fun _ : ℝ => ‖sys.u T‖ ^ 2) s :=
        differentiableAt_const (c := ‖sys.u T‖ ^ 2)
      have hsquare : DifferentiableAt ℝ
          (fun r : ℝ => (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2) s :=
        (differentiableAt_const (c := (1 / 2 : ℝ))).mul
          ((hu.sub_const (sys.u T)).norm_sq ℝ)
      exact (hu.norm_sq ℝ).sub hc |>.sub hsquare
    exact hGdiff
  have hTwo : ∀ {t T : ℝ}, 1 ≤ t → t ≤ T →
      (1 / 2 : ℝ) * ‖sys.u t - sys.u T‖ ^ 2 ≤
        ‖sys.u t‖ ^ 2 - ‖sys.u T‖ ^ 2 +
          ((Real.exp (-gamma * (t - 1)) - Real.exp (-gamma * (T - 1))) / gamma) *
            deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
              (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2) 1 +
          ∫ theta in t..T, ∫ s in 1..theta,
            Real.exp (-gamma * (theta - s)) * qfun s := by
    intro t T ht hT
    have hT1 : 1 ≤ T := ht.trans hT
    have hqcont : ContinuousOn qfun (Set.Icc (1 : ℝ) T) :=
      hqOn.mono (Set.Icc_subset_Ici_self)
    have hbase := damped_two_time_integral_bound
      (g := fun r => ‖sys.u r‖ ^ 2 - ‖sys.u T‖ ^ 2 -
        (1 / 2 : ℝ) * ‖sys.u r - sys.u T‖ ^ 2)
      (q := qfun) gamma 1 t T ((hGDiff T).of_le (by norm_num)) (hGDerivDiff T)
      hqcont (hNestedInt ht hT) sys.gamma_pos ht hT
      (fun s hs => by
        simpa [qfun] using even_moving_endpoint_damped_ineq hPhi sys hEven hT1
          ⟨hs.1, hs.2.le⟩)
    have hG_T : (‖sys.u T‖ ^ 2 - ‖sys.u T‖ ^ 2 -
        (1 / 2 : ℝ) * ‖sys.u T - sys.u T‖ ^ 2) = 0 := by simp
    have hG_t : (‖sys.u t‖ ^ 2 - ‖sys.u T‖ ^ 2 -
        (1 / 2 : ℝ) * ‖sys.u t - sys.u T‖ ^ 2) =
        ‖sys.u t‖ ^ 2 - ‖sys.u T‖ ^ 2 -
          (1 / 2 : ℝ) * ‖sys.u t - sys.u T‖ ^ 2 := by rfl
    dsimp at hbase
    simp only [sub_self, norm_zero, zero_mul, sub_zero] at hbase
    linarith
  have hJ0int : IntegrableOn (fun theta : ℝ =>
      ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * ‖vfun s‖ ^ 2)
      (Set.Ici (0 : ℝ)) := by
    have h := causal_exp_convolution_integrable_local
      (fun s : ℝ => ‖vfun s‖ ^ 2) gamma sys.gamma_pos hvel2
    apply h.congr
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with theta htheta
    apply intervalIntegral.integral_congr_ae
    filter_upwards with s hs
    rw [abs_of_nonneg (by positivity : 0 ≤ ‖vfun s‖ ^ 2)]
  have hJ0intIcc : ∀ {t T : ℝ}, 1 ≤ t → t ≤ T →
      IntervalIntegrable (fun theta : ℝ =>
        ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * ‖vfun s‖ ^ 2)
        volume t T := by
    intro t T ht hT
    have hset : Set.uIcc t T ⊆ Set.Ici (0 : ℝ) := by
      rw [Set.uIcc_of_le hT]
      intro x hx
      exact le_trans (by linarith [ht]) hx.1
    exact (hJ0int.mono_set hset).intervalIntegrable
  have hNestedLe : ∀ {t T : ℝ}, 1 ≤ t → t ≤ T →
      (∫ theta in t..T, ∫ s in 1..theta,
        Real.exp (-gamma * (theta - s)) * qfun s) ≤ Herror T - Herror t := by
    intro t T ht hT
    have hT1 : 1 ≤ T := ht.trans hT
    have hpoint : ∀ theta ∈ Set.Icc t T,
        (∫ s in 1..theta, Real.exp (-gamma * (theta - s)) * qfun s) ≤
          (3 / 2 : ℝ) * (∫ s in 0..theta,
            Real.exp (-gamma * (theta - s)) * ‖vfun s‖ ^ 2) := by
      intro theta htheta
      have htheta1 : 1 ≤ theta := ht.trans htheta.1
      let K : ℝ → ℝ := fun s => Real.exp (-gamma * (theta - s)) *
        ‖vfun s‖ ^ 2
      have hKnonneg : ∀ s : ℝ, 0 ≤ K s := by
        intro s
        exact mul_nonneg (le_of_lt (Real.exp_pos _)) (sq_nonneg _)
      have hKint01 : IntervalIntegrable K volume 0 1 := by
        have hKcont : ContinuousOn
            (fun s : ℝ => Real.exp (-gamma * (theta - s))) (Set.Icc 0 1) := by
          fun_prop
        have hgint : IntegrableOn (fun s : ℝ => ‖vfun s‖ ^ 2) (Set.Icc 0 1) :=
          hvel2.mono_set Set.Icc_subset_Ici_self
        apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr
        exact hgint.continuousOn_mul hKcont isCompact_Icc
      have hKint1 : IntervalIntegrable K volume 1 theta := by
        have hcont : ContinuousOn K (Set.Icc 1 theta) := by
          dsimp [K]
          have hvnorm : ContinuousOn (fun s : ℝ => ‖vfun s‖ ^ 2)
              (Set.Icc 1 theta) := by
            simpa only [Function.comp_apply] using
              ((continuous_norm.continuousOn.comp hvOn
                (fun _ _ => Set.mem_univ _)).pow 2).mono
                Set.Icc_subset_Ici_self
          exact (Real.continuous_exp.comp (continuous_const.mul
            (continuous_const.sub continuous_id))).continuousOn.mul hvnorm
        exact hcont.intervalIntegrable_of_Icc htheta1
      have hadd := intervalIntegral.integral_add_adjacent_intervals hKint01 hKint1
      have hnonneg : 0 ≤ ∫ s in 0..1, K s :=
        intervalIntegral.integral_nonneg (by norm_num) (fun s hs => hKnonneg s)
      dsimp [qfun, vfun, K]
      rw [show (fun s : ℝ => Real.exp (-gamma * (theta - s)) *
          ((3 / 2 : ℝ) * ‖vfun s‖ ^ 2)) =
          fun s => (3 / 2 : ℝ) *
            (Real.exp (-gamma * (theta - s)) * ‖vfun s‖ ^ 2) by
        funext s; ring, intervalIntegral.integral_const_mul]
      rw [← hadd]
      linarith
    have hleft := hNestedInt ht hT
    have hright := (hJ0intIcc ht hT).const_mul (3 / 2 : ℝ)
    have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hT hleft hright
      (fun theta htheta => hpoint theta ⟨le_of_lt htheta.1, le_of_lt htheta.2⟩)
    rw [intervalIntegral.integral_const_mul] at hmono
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (hJ0intIcc (by norm_num) ht) (hJ0intIcc ht hT)
    dsimp [Herror]
    rw [show (∫ theta in 1..T, ∫ s in 0..theta,
        Real.exp (-gamma * (theta - s)) * ‖vfun s‖ ^ 2) =
        (∫ theta in 1..t, ∫ s in 0..theta,
          Real.exp (-gamma * (theta - s)) * ‖vfun s‖ ^ 2) +
          ∫ theta in t..T, ∫ s in 0..theta,
            Real.exp (-gamma * (theta - s)) * ‖vfun s‖ ^ 2 by
      exact hsplit.symm]
    linarith

  have hUniform : ∀ ε : ℝ, 0 < ε → ∃ N : ℝ, ∀ s t : ℝ,
      N ≤ s → N ≤ t → dist (sys.u s) (sys.u t) < ε := by
    intro ε hε
    let δ : ℝ := ε ^ 2 / 12
    have hδ : 0 < δ := by
      dsimp [δ]
      positivity
    rcases Metric.tendsto_atTop.1 hNormSq δ hδ with ⟨Nnorm, hNnorm⟩
    rcases Metric.tendsto_atTop.1 hHerror δ hδ with ⟨Nerr, hNerr⟩
    have hexp0 : Tendsto (fun r : ℝ => Real.exp (-gamma * (r - 1))) atTop
        (nhds 0) := by
      apply Real.tendsto_exp_atBot.comp
      have hshift : Tendsto (fun r : ℝ => r - 1) atTop atTop := by
        simpa [sub_eq_add_neg] using
          (tendsto_atTop_add_const_right atTop (-1 : ℝ) tendsto_id)
      convert (tendsto_id.const_mul_atTop_of_neg
        (by linarith [sys.gamma_pos] : -gamma < 0)).comp hshift using 1 <;> ring
    have hexpC : Tendsto (fun r : ℝ => (C / gamma) *
        Real.exp (-gamma * (r - 1))) atTop (nhds 0) := by
      simpa using hexp0.const_mul (C / gamma)
    rcases Metric.tendsto_atTop.1 hexpC δ hδ with ⟨Nexp, hNexp⟩
    rcases eventually_atTop.1 hCtail with ⟨NC, hNC⟩
    let N : ℝ := max 1 (max Nnorm (max Nerr (max Nexp NC)))
    have hN1 : 1 ≤ N := le_max_left _ _
    have hNnorm_le : Nnorm ≤ N := by
      calc
        Nnorm ≤ max Nnorm (max Nerr (max Nexp NC)) := le_max_left _ _
        _ ≤ max 1 (max Nnorm (max Nerr (max Nexp NC))) := le_max_right _ _
    have hNerr_le : Nerr ≤ N := by
      calc
        Nerr ≤ max Nerr (max Nexp NC) := le_max_left _ _
        _ ≤ max Nnorm (max Nerr (max Nexp NC)) := le_max_right _ _
        _ ≤ max 1 (max Nnorm (max Nerr (max Nexp NC))) := le_max_right _ _
    have hNexp_le : Nexp ≤ N := by
      calc
        Nexp ≤ max Nexp NC := le_max_left _ _
        _ ≤ max Nerr (max Nexp NC) := le_max_right _ _
        _ ≤ max Nnorm (max Nerr (max Nexp NC)) := le_max_right _ _
        _ ≤ max 1 (max Nnorm (max Nerr (max Nexp NC))) := le_max_right _ _
    have hNC_le : NC ≤ N := by
      calc
        NC ≤ max Nexp NC := le_max_right _ _
        _ ≤ max Nerr (max Nexp NC) := le_max_right _ _
        _ ≤ max Nnorm (max Nerr (max Nexp NC)) := le_max_right _ _
        _ ≤ max 1 (max Nnorm (max Nerr (max Nexp NC))) := le_max_right _ _
    refine ⟨N, ?_⟩
    have hordered : ∀ {s t : ℝ}, N ≤ s → N ≤ t → s ≤ t →
        dist (sys.u s) (sys.u t) < ε := by
      intro s t hs ht hst
      have h1s : 1 ≤ s := hN1.trans hs
      have h1t : 1 ≤ t := hN1.trans ht
      have hsNnorm : Nnorm ≤ s := hNnorm_le.trans hs
      have htNnorm : Nnorm ≤ t := hNnorm_le.trans ht
      have hsNerr : Nerr ≤ s := hNerr_le.trans hs
      have htNerr : Nerr ≤ t := hNerr_le.trans ht
      have hsNexp : Nexp ≤ s := hNexp_le.trans hs
      have htNC : NC ≤ t := hNC_le.trans ht
      have hnorm_s : |‖sys.u s‖ ^ 2 - 2 * normTailLimit| < δ := by
        simpa [Real.dist_eq] using hNnorm s hsNnorm
      have hnorm_t : |‖sys.u t‖ ^ 2 - 2 * normTailLimit| < δ := by
        simpa [Real.dist_eq] using hNnorm t htNnorm
      have hnorm_tri : |‖sys.u s‖ ^ 2 - ‖sys.u t‖ ^ 2| ≤
          |‖sys.u s‖ ^ 2 - 2 * normTailLimit| +
            |‖sys.u t‖ ^ 2 - 2 * normTailLimit| := by
        simpa [abs_sub_comm] using
          (abs_sub_le (‖sys.u s‖ ^ 2) (2 * normTailLimit) (‖sys.u t‖ ^ 2))
      have hnorm_diff : ‖sys.u s‖ ^ 2 - ‖sys.u t‖ ^ 2 < 2 * δ := by
        exact lt_of_le_of_lt (le_abs_self _) (by linarith [hnorm_tri, hnorm_s, hnorm_t])
      have herr_s : |Herror s - Herr| < δ := by
        simpa [Real.dist_eq] using hNerr s hsNerr
      have herr_t : |Herror t - Herr| < δ := by
        simpa [Real.dist_eq] using hNerr t htNerr
      have herr_tri : |Herror t - Herror s| ≤
          |Herror t - Herr| + |Herror s - Herr| := by
        have h := abs_sub_le (Herror t) Herr (Herror s)
        rw [abs_sub_comm Herr (Herror s)] at h
        exact h
      have herr_diff : Herror t - Herror s < 2 * δ := by
        exact lt_of_le_of_lt (le_abs_self _) (by linarith [herr_tri, herr_s, herr_t])
      have hcoef_nonneg : 0 ≤
          (Real.exp (-gamma * (s - 1)) - Real.exp (-gamma * (t - 1))) / gamma := by
        have harg : -gamma * (t - 1) ≤ -gamma * (s - 1) := by
          have hmul : 0 ≤ gamma * (t - s) :=
            mul_nonneg (le_of_lt sys.gamma_pos) (sub_nonneg.mpr hst)
          linarith
        exact div_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr harg))
          (le_of_lt sys.gamma_pos)
      have hderiv_le : deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u t‖ ^ 2 -
          (1 / 2 : ℝ) * ‖sys.u r - sys.u t‖ ^ 2) 1 ≤ C := by
        exact (le_abs_self _).trans (hNC t htNC)
      have hend0 :
          ((Real.exp (-gamma * (s - 1)) - Real.exp (-gamma * (t - 1))) / gamma) *
            deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u t‖ ^ 2 -
              (1 / 2 : ℝ) * ‖sys.u r - sys.u t‖ ^ 2) 1 ≤
          ((Real.exp (-gamma * (s - 1)) - Real.exp (-gamma * (t - 1))) / gamma) * C :=
        mul_le_mul_of_nonneg_left hderiv_le hcoef_nonneg
      have hexp_t_nonneg : 0 ≤ Real.exp (-gamma * (t - 1)) :=
        (Real.exp_pos _).le
      have hcoef_le :
          (Real.exp (-gamma * (s - 1)) - Real.exp (-gamma * (t - 1))) / gamma ≤
            Real.exp (-gamma * (s - 1)) / gamma := by
        exact div_le_div_of_nonneg_right
          (sub_le_self _ hexp_t_nonneg) (le_of_lt sys.gamma_pos)
      have hend1 :
          ((Real.exp (-gamma * (s - 1)) - Real.exp (-gamma * (t - 1))) / gamma) * C ≤
            (C / gamma) * Real.exp (-gamma * (s - 1)) := by
        calc
          _ ≤ (Real.exp (-gamma * (s - 1)) / gamma) * C :=
            mul_le_mul_of_nonneg_right hcoef_le hCnonneg
          _ = (C / gamma) * Real.exp (-gamma * (s - 1)) := by ring
      have hexp_bound : (C / gamma) * Real.exp (-gamma * (s - 1)) < δ := by
        have hnonneg : 0 ≤ (C / gamma) * Real.exp (-gamma * (s - 1)) :=
          mul_nonneg (div_nonneg hCnonneg (le_of_lt sys.gamma_pos))
            (le_of_lt (Real.exp_pos _))
        have h := hNexp s hsNexp
        rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg] at h
        exact h
      have hend :
          ((Real.exp (-gamma * (s - 1)) - Real.exp (-gamma * (t - 1))) / gamma) *
            deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u t‖ ^ 2 -
              (1 / 2 : ℝ) * ‖sys.u r - sys.u t‖ ^ 2) 1 < δ :=
        lt_of_le_of_lt (hend0.trans hend1) hexp_bound
      have hnest := hNestedLe h1s hst
      have hbound :
          ‖sys.u s‖ ^ 2 - ‖sys.u t‖ ^ 2 +
              ((Real.exp (-gamma * (s - 1)) - Real.exp (-gamma * (t - 1))) / gamma) *
                deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u t‖ ^ 2 -
                  (1 / 2 : ℝ) * ‖sys.u r - sys.u t‖ ^ 2) 1 +
            ∫ theta in s..t, ∫ r in 1..theta,
              Real.exp (-gamma * (theta - r)) * qfun r < ε ^ 2 / 2 := by
        have hsum :
            ‖sys.u s‖ ^ 2 - ‖sys.u t‖ ^ 2 +
                ((Real.exp (-gamma * (s - 1)) - Real.exp (-gamma * (t - 1))) / gamma) *
                  deriv (fun r => ‖sys.u r‖ ^ 2 - ‖sys.u t‖ ^ 2 -
                    (1 / 2 : ℝ) * ‖sys.u r - sys.u t‖ ^ 2) 1 +
              ∫ theta in s..t, ∫ r in 1..theta,
                Real.exp (-gamma * (theta - r)) * qfun r < 5 * δ := by
          linarith [hnorm_diff, hend, hnest, herr_diff]
        calc
          _ < 5 * δ := hsum
          _ = 5 * (ε ^ 2 / 12) := by rfl
          _ < ε ^ 2 / 2 := by nlinarith [sq_pos_of_pos hε]
      have hsq := hTwo h1s hst
      have hsq' : (1 / 2 : ℝ) * ‖sys.u s - sys.u t‖ ^ 2 < ε ^ 2 / 2 :=
        lt_of_le_of_lt hsq hbound
      have hnorm_lt : ‖sys.u s - sys.u t‖ < ε := by
        have hsqnorm : ‖sys.u s - sys.u t‖ ^ 2 < ε ^ 2 := by
          linarith
        simpa [abs_of_nonneg (norm_nonneg _)] using
          (abs_lt_of_sq_lt_sq hsqnorm (le_of_lt hε))
      simpa [dist_eq_norm] using hnorm_lt
    intro s t hs ht
    rcases le_total s t with hst | hts
    · exact hordered hs ht hst
    · simpa [dist_comm] using hordered ht hs hts

  obtain ⟨w, hstrong⟩ : ∃ w : H, Tendsto sys.u atTop (nhds w) := by
    apply cauchy_map_iff_exists_tendsto.mp
    rw [Metric.cauchy_iff]
    refine ⟨by infer_instance, ?_⟩
    intro ε hε
    rcases hUniform ε hε with ⟨N, hN⟩
    refine ⟨sys.u '' Set.Ici N, Filter.image_mem_map (eventually_ge_atTop N), ?_⟩
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    simpa [dist_eq_norm] using hN s t hs ht
  have hstrongWeak : Tendsto (fun t => toWeakSpace ℝ H (sys.u t)) atTop
      (nhds (toWeakSpace ℝ H w)) := by
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto w).comp hstrong
  have hw : w = uhat :=
    (toWeakSpace ℝ H).injective (tendsto_nhds_unique hstrongWeak hUhatWeak)
  subst w
  exact ⟨uhat, hUhatMin, hstrong⟩
```

## Proof explanation
The proof begins by unpacking the bounded-below hypothesis. From

$$
\exists m\in\mathbb R,\ \forall x\in H,\ m\le \Phi(x)
$$

the proof obtains a number $m$ and the pointwise lower bound $m\le \Phi(x)$. It then defines

$$
hBdd : \mathrm{BddBelow}(\mathrm{Set.range}\Phi)
$$

by witnessing the lower bound with this same $m$. This is exactly the statement that the range $\{\Phi(x)\mid x\in H\}$ is bounded below.

Next the proof proves that $0$ is already a global minimizer. It invokes `even_convex_zero_mem_argmin`, whose mathematical content is: if $\Phi$ is convex on all of $H$, even, and bounded below, then $0\in \mathrm{argmin}\Phi$. The convex-even argument is that convexity gives

$$
\Phi(0)=\Phi\!\left(\frac{x+(-x)}2\right)
\le \frac{\Phi(x)+\Phi(-x)}2=\Phi(x),
$$

using evenness in the last equality. Hence $0$ attains the global minimum. The proof records this as

$$
hZeroMin : (0:H)\in \mathrm{argmin}\Phi(hBdd).
$$

The proof also reconciles the bounded-below witness appearing in `hMin` with the witness `hBdd`. Since bounded-below proofs for the same set are proof-irrelevant, the two minimizer sets are the same. The tactic `simpa only [proof_irrel_heq] using hMin` transfers the nonemptiness of the minimizer set from the statement’s constructed bounded-below proof to the set using `hBdd`. Thus it obtains that $(\mathrm{argmin}\Phi(hBdd))$ is nonempty.

Then the proof packages the assumptions as

$$
hPhi : \mathrm{HasPotentialAssumption}(\Phi).
$$

The visible construction is from global $C^1$-ness of $\Phi$, convexity on all of $H$, and bounded-belowness. This package is the hypothesis required by the cited theorem `scalar_damped_minimizing_property`. The proof again uses proof irrelevance to identify

$$
\mathrm{potential\_range\_bddBelow}(hPhi)
$$

with the previously defined `hBdd`, and transfers the nonemptiness statement accordingly. This gives a nonempty minimizer set for the form required by the scalar minimizing property.

The proof then applies `scalar_damped_minimizing_property` to `hPhi` and `sys`. The mathematical content of that theorem, specialized to this setting, is a four-part conclusion:

1. the squared velocity is integrable on the positive half-line,

   $$
   t\mapsto \left\|\mathrm{fderiv}_{\mathbb R}\mathrm{sys.u}(t)(1)\right\|^2
   \in L^1([0,\infty));
   $$

2. the velocity tends to zero,

   $$
   \mathrm{fderiv}_{\mathbb R}\mathrm{sys.u}(t)(1)\to 0;
   $$

3. the potential values converge to the global minimum,

   $$
   \Phi(\mathrm{sys.u}(t))\to \inf \Phi(H);
   $$

4. if the minimizer set is nonempty, then the trajectory converges weakly to some global minimizer $\hat u$.

The proof extracts these as `hvel2`, `hvel0`, `hPhi0`, and `hweak`. From `hweak` and the nonemptiness just established, it obtains a point $\hat u$ with

$$
\hat u\in \mathrm{argmin}\Phi,
\qquad
\mathrm{sys.u}(t)\rightharpoonup \hat u.
$$

The latter is expressed in Lean through `toWeakSpace`.

Since $\hat u$ lies in the minimizer set, the proof records

$$
\Phi(\hat u)=\inf \Phi(H).
$$

The next step derives a differential inequality for the distance to $\hat u$. The proof applies `even_distance_damped_ineq`, whose statement, specialized here, says that for $x\in H$ and $t>0$,

$$
\frac{d^2}{dt^2}\left(\frac12\|\mathrm{sys.u}(t)-x\|^2\right)
+\gamma \frac{d}{dt}\left(\frac12\|\mathrm{sys.u}(t)-x\|^2\right)
\le
\Phi(x)-\Phi(\mathrm{sys.u}(t))
+\left\|\mathrm{fderiv}_{\mathbb R}\mathrm{sys.u}(t)(1)\right\|^2.
$$

Taking $x=\hat u$, the proof uses $\Phi(\hat u)=\inf\Phi(H)$ and `potential_sInf_le`, which says that the infimum of the range of $\Phi$ is at most $\Phi(y)$ for every $y$. Hence

$$
\Phi(\hat u)-\Phi(\mathrm{sys.u}(t))
=
\inf\Phi(H)-\Phi(\mathrm{sys.u}(t))\le 0.
$$

Therefore the potential-difference term can be dropped, yielding

$$
\frac{d^2}{dt^2}\left(\frac12\|\mathrm{sys.u}(t)-\hat u\|^2\right)
+\gamma \frac{d}{dt}\left(\frac12\|\mathrm{sys.u}(t)-\hat u\|^2\right)
\le
\left\|\mathrm{fderiv}_{\mathbb R}\mathrm{sys.u}(t)(1)\right\|^2.
$$

This is the first important damped differential inequality.

The same reasoning is repeated for the special point $x=0$. Since the proof already established $0\in \mathrm{argmin}\Phi$, it has

$$
\Phi(0)=\inf\Phi(H).
$$

Using `potential_sInf_le` again to bound $\inf\Phi(H)-\Phi(\mathrm{sys.u}(t))\le 0$, the proof obtains

$$
\frac{d^2}{dt^2}\left(\frac12\|\mathrm{sys.u}(t)\|^2\right)
+\gamma \frac{d}{dt}\left(\frac12\|\mathrm{sys.u}(t)\|^2\right)
\le
\left\|\mathrm{fderiv}_{\mathbb R}\mathrm{sys.u}(t)(1)\right\|^2.
$$

This will be used after shifting time by $1$, so that the scalar convergence lemmas can be applied on the interval $[0,\infty)$, avoiding the one-sided endpoint $0$ of the trajectory.

The proof now defines the shifted scalar function

$$
\theta(t)=\frac12\|\mathrm{sys.u}(t+1)\|^2.
$$

It establishes that $\theta$ is $C^2$ on $[0,\infty)$. This uses the smoothness of the trajectory supplied by the dissipative system and the fact that $t+1>0$ for $t\ge 0$, together with the smoothness of the squared norm. It also proves differentiability of $\theta$ at every $t\ge 0$, using `dissipativeSystem_differentiableAt_pos`, which states that $\mathrm{sys.u}$ is differentiable at every positive time. Since $t+1>0$, this applies.

The proof then computes derivatives of $\theta$. For $s>-1$,

$$
\theta'(s)
=
\frac{d}{dr}\left(\frac12\|\mathrm{sys.u}(r)\|^2\right)\bigg|_{r=s+1}.
$$

This is the chain rule for the shift $r\mapsto r+1$. It also proves that for $s\ge 0$,

$$
\theta''(s)
=
\frac{d^2}{dr^2}\left(\frac12\|\mathrm{sys.u}(r)\|^2\right)\bigg|_{r=s+1}.
$$

These identities are used to transfer the damped differential inequality from the original time variable to the shifted variable.

The integrability of the shifted force term is also obtained:

$$
s\mapsto
\left\|\mathrm{fderiv}_{\mathbb R}\mathrm{sys.u}(s+1)(1)\right\|^2
\in L^1([0,\infty)).
$$

This follows from `hvel2` by the measure-preserving translation $s\mapsto s+1$.

Combining the derivative identities with the damped inequality for the distance to $0$ gives, for every $s\ge 0$,

$$
\theta''(s)+\gamma \theta'(s)
\le
\left\|\mathrm{fderiv}_{\mathbb R}\mathrm{sys.u}(s+1)(1)\right\|^2.
$$

Now the proof applies `positive_part_integrable_of_damped_inequality`. That theorem says that if $\omega$ is $C^1$ on $[0,\infty)$, $\gamma>0$, and

$$
\omega'(t)+\gamma \omega(t)\le g(t)
$$

with $g\in L^1([0,\infty))$, then the positive part $t\mapsto \max(\omega(t),0)$ is integrable on $[0,\infty)$. Here the proof takes $\omega=\theta'$ and

$$
g(s)=\left\|\mathrm{fderiv}_{\mathbb R}\mathrm{sys.u}(s+1)(1)\right\|^2.
$$

The required $C^1$-ness of $\theta'$ comes from the $C^2$-ness of $\theta$, and the inequality was just established. Since the shifted force term is integrable, the conclusion is that

$$
s\mapsto \max(\theta'(s),0)
$$

is integrable on $[0,\infty)$.

The proof then invokes `converges_of_integrable_positive_derivative`. That theorem says that if a scalar function $\theta$ is $C^1$ on $[0,\infty)$, bounded below, and its positive derivative part $\max(\theta',0)$ is integrable, then $\theta$ converges to a finite limit at infinity. Here $\theta(t)=\frac12\|\mathrm{sys.u}(t+1)\|^2\ge 0$, so it is bounded below by $0$. The positive-part integrability was just proved. Hence there exists a real number `normTailLimit` such that

$$
\theta(t)\to \text{normTailLimit}.
$$

Multiplying by $2$, this gives

$$
\|\mathrm{sys.u}(t+1)\|^2\to 2\cdot \text{normTailLimit}.
$$

Shifting back by $t\mapsto t-1$, the proof obtains

$$
\|\mathrm{sys.u}(t)\|^2\to L
$$

where $L=2\cdot \text{normTailLimit}$.

At this point the proof turns to the causal error term from the paper. It applies `even_causal_error_converges`, whose statement says that if the squared velocity is integrable on $[0,\infty)$, then there exists a real number `Herr` such that

$$
r\mapsto
\frac32
\int_1^r \int_0^\theta
e^{-\gamma(\theta-s)}
\left\|\mathrm{fderiv}_{\mathbb R}\mathrm{sys.u}(s)(1)\right\|^2
\,ds\,d\theta
$$

converges to `Herr` as $r\to\infty$. The proof defines this function as `Herror`, so that

$$
\mathrm{Herror}(r)\to \mathrm{Herr}.
$$

Next the proof uses `eventually_bounded_even_endpoint_deriv`. That theorem says that if the squared norm $\|\mathrm{sys.u}(T)\|^2$ converges as $T\to\infty$, then there exist $C\ge 0$ such that eventually in $T$,

$$
\left|
\frac{d}{dr}
\left(
\|\mathrm{sys.u}(r)\|^2-\|\mathrm{sys.u}(T)\|^2
-\frac12\|\mathrm{sys.u}(r)-\mathrm{sys.u}(T)\|^2
\right)\bigg|_{r=1}
\right|
\le C.
$$

Here the convergence $\|\mathrm{sys.u}(T)\|^2\to L$ has just been proved, so the theorem applies and gives a nonnegative constant $C$ together with an eventual bound on the derivative at $r=1$ of the moving-endpoint function.

The proof then establishes an estimate for the coefficient of that derivative in the two-time integral bound. For $1\le t\le T$, it proves

$$
\frac{e^{-\gamma(t-1)}-e^{-\gamma(T-1)}}{\gamma}\ge 0,
$$

using $\gamma>0$ and monotonicity of the exponential. It also proves that eventually in $T$,

$$
\frac{e^{-\gamma(t-1)}-e^{-\gamma(T-1)}}{\gamma}
\cdot
\frac{d}{dr}
\left(
\|\mathrm{sys.u}(r)\|^2-\|\mathrm{sys.u}(T)\|^2
-\frac12\|\mathrm{sys.u}(r)-\mathrm{sys.u}(T)\|^2
\right)\bigg|_{r=1}
\le
\frac{e^{-\gamma(t-1)}-e^{-\gamma(T-1)}}{\gamma}
\cdot C.
$$

This follows because the coefficient is nonnegative and the derivative is eventually bounded above by $C$ in absolute value.

The proof then defines

$$
vfun(s)=\mathrm{fderiv}_{\mathbb R}\mathrm{sys.u}(s)(1),
\qquad
qfun(s)=\frac32\|vfun(s)\|^2.
$$

It proves that $vfun$ is continuous on $[1,\infty)$, using the smoothness of the trajectory at positive times, and hence that $qfun$ is continuous on $[1,\infty)$. It extends both functions to all of $\mathbb R$ by

$$
vext(s)=vfun(\max(s,1)),\qquad qext(s)=qfun(\max(s,1)).
$$

On $[1,\infty)$ these extensions agree with $vfun$ and $qfun$. This extension is used to prove interval integrability of the nested integral

$$
\theta\mapsto \int_1^\theta e^{-\gamma(\theta-s)}qfun(s)\,ds
$$

on every interval $[t,T]$ with $1\le t\le T$. The proof obtains this by a continuous parametric interval-integral argument: $qext$ is continuous, so the parametric integral is continuous, hence interval integrable on compact intervals, and then it is identified with the integral using $qfun$ on the relevant interval.

The proof also verifies smoothness of the moving-endpoint function

$$
G_T(r)=
\|\mathrm{sys.u}(r)\|^2-\|\mathrm{sys.u}(T)\|^2
-\frac12\|\mathrm{sys.u}(r)-\mathrm{sys.u}(T)\|^2.
$$

It shows that for every $T$, $G_T$ is $C^2$ on $[1,\infty)$, and that its derivative is $C^1$ on $[1,\infty)$. These are the differentiability hypotheses needed for the two-time integral bound.

Now the proof uses `damped_two_time_integral_bound`, a general lemma for a scalar function $g$. Specialized here, it takes $a=1$,

$$
g(r)=G_T(r),
\qquad
q(s)=qfun(s),
$$

and $t,T$ with $1\le t\le T$. The lemma requires $g$ and $g'$ to be $C^1$ on $[1,\infty)$, $q$ continuous on $[1,T]$, the nested integral of $e^{-\gamma(\theta-s)}q(s)$ to be interval integrable on $[t,T]$, $\gamma>0$, and the differential inequality

$$
g''(s)+\gamma g'(s)\le q(s)
$$

for $s\in(1,T)$. The latter is provided by `even_moving_endpoint_damped_ineq`, whose statement, specialized to the even potential $\Phi$, says that for $T\ge 1$ and $s\in(1,T]$,

$$
G_T''(s)+\gamma G_T'(s)
\le
\frac32\|\mathrm{fderiv}_{\mathbb R}\mathrm{sys.u}(s)(1)\|^2
=
qfun(s).
$$

Thus all hypotheses of `damped_two_time_integral_bound` are satisfied.

The conclusion of that bound is

$$
G_T(T)-G_T(t)
\le
\frac{e^{-\gamma(t-1)}-e^{-\gamma(T-1)}}{\gamma}G_T'(1)
+
\int_t^T\int_1^\theta
e^{-\gamma(\theta-s)}qfun(s)\,ds\,d\theta.
$$

Since

$$
G_T(T)=0,
$$

this rearranges to the key estimate

$$
\frac12\|\mathrm{sys.u}(t)-\mathrm{sys.u}(T)\|^2
\le
\|\mathrm{sys.u}(t)\|^2-\|\mathrm{sys.u}(T)\|^2
+
\frac{e^{-\gamma(t-1)}-e^{-\gamma(T-1)}}{\gamma}G_T'(1)
+
\int_t^T\int_1^\theta
e^{-\gamma(\theta-s)}qfun(s)\,ds\,d\theta.
$$

The proof also needs to compare the nested integral appearing here with the causal error function `Herror`. It applies `causal_exp_convolution_integrable_local` to the function $s\mapsto \|vfun(s)\|^2$. Since `hvel2` gives integrability of this squared velocity on $[0,\infty)$, that lemma gives integrability on $[0,\infty)$ of

$$
\theta\mapsto
\int_0^\theta e^{-\gamma(\theta-s)}\|vfun(s)\|^2\,ds.
$$

The proof then restricts this integrability to compact intervals $[t,T]$ with $1\le t\le T$. This is needed to split the integral defining `Herror`.

Using nonnegativity of the integrand $e^{-\gamma(\theta-s)}\|vfun(s)\|^2$ on $[0,1]$, the proof shows that for $1\le t\le T$,

$$
\int_t^T\int_1^\theta e^{-\gamma(\theta-s)}qfun(s)\,ds\,d\theta
\le
\mathrm{Herror}(T)-\mathrm{Herror}(t).
$$

Indeed, $qfun(s)=\frac32\|vfun(s)\|^2$, and on each slice $\theta$, the integral over $1\le s\le\theta$ is at most the integral over $0\le s\le\theta$ after multiplying by $\frac32$, because the contribution over $[0,1]$ is nonnegative. Integrating over $\theta\in[t,T]$ and using additivity of the integral gives the difference of `Herror` values.

Now the proof turns to the uniform Cauchy estimate. It wants to show that for every $\varepsilon>0$, there exists $N$ such that for all $s,t\ge N$,

$$
\mathrm{dist}(\mathrm{sys.u}(s),\mathrm{sys.u}(t))<\varepsilon.
$$

Let

$$
\delta=\frac{\varepsilon^2}{12}.
$$

Since $\delta>0$, the proof uses the convergence $\|\mathrm{sys.u}(t)\|^2\to L$ and `Herror(t)→Herr` to choose thresholds $Nnorm$ and $Nerr$ such that beyond them,

$$
\left|\|\mathrm{sys.u}(t)\|^2-L\right|<\delta,
\qquad
\left|\mathrm{Herror}(t)-\mathrm{Herr}\right|<\delta.
$$

It also uses $\gamma>0$ to show

$$
e^{-\gamma(r-1)}\to 0
$$

as $r\to\infty$, because $-\gamma<0$. Consequently,

$$
\frac{C}{\gamma}e^{-\gamma(r-1)}\to 0.
$$

Thus there is a threshold $Nexp$ beyond which

$$
\frac{C}{\gamma}e^{-\gamma(r-1)}<\delta.
$$

Finally, from the eventual bound on $G_T'(1)$, there is a threshold $NC$ beyond which the absolute value of that derivative is at most $C$. The proof sets

$$
N=\max\left(1,Nnorm,Nerr,Nexp,NC\right).
$$

Now take $s,t\ge N$ with $s\le t$. The proof proves the estimate first in the ordered case and then swaps $s,t$ for the other order. Since both points are beyond $Nnorm$,

$$
\left|\|\mathrm{sys.u}(s)\|^2-L\right|<\delta,
\qquad
\left|\|\mathrm{sys.u}(t)\|^2-L\right|<\delta.
$$

By the triangle inequality for absolute values,

$$
\left|\|\mathrm{sys.u}(s)\|^2-\|\mathrm{sys.u}(t)\|^2\right|<2\delta.
$$

Similarly, since both points are beyond $Nerr$,

$$
\left|\mathrm{Herror}(t)-\mathrm{Herror}(s)\right|<2\delta,
$$

so in particular

$$
\mathrm{Herror}(t)-\mathrm{Herror}(s)<2\delta.
$$

The coefficient of $G_t'(1)$ in the two-time estimate is nonnegative. Since $t\ge NC$, the derivative $G_t'(1)$ is at most $C$ in absolute value, hence at most $C$. Therefore the endpoint term satisfies

$$
\frac{e^{-\gamma(s-1)}-e^{-\gamma(t-1)}}{\gamma}G_t'(1)
\le
\frac{e^{-\gamma(s-1)}-e^{-\gamma(t-1)}}{\gamma}C.
$$

Because $e^{-\gamma(t-1)}\ge 0$, this is further bounded by

$$
\frac{C}{\gamma}e^{-\gamma(s-1)}<\delta,
$$

using $s\ge Nexp$.

Combining these estimates with the key two-time inequality gives

$$
\frac12\|\mathrm{sys.u}(s)-\mathrm{sys.u}(t)\|^2
<
2\delta+\delta+2\delta
=
5\delta.
$$

Since $\delta=\varepsilon^2/12$,

$$
5\delta=\frac{5\varepsilon^2}{12}<\frac{\varepsilon^2}{2}.
$$

Thus

$$
\frac12\|\mathrm{sys.u}(s)-\mathrm{sys.u}(t)\|^2
<\frac{\varepsilon^2}{2},
$$

and therefore

$$
\|\mathrm{sys.u}(s)-\mathrm{sys.u}(t)\|<\varepsilon.
$$

This proves the uniform Cauchy statement for the tail of the trajectory. The reverse order $t\le s$ is handled by symmetry of the distance.

The proof then upgrades this uniform Cauchy estimate to existence of a strong limit. It applies `cauchy_map_iff_exists_tendsto.mp`. In a complete space, a filter is Cauchy if and only if it converges. The proof uses `Metric.cauchy_iff` and the uniform estimate to show that the filter generated by the map $t\mapsto \mathrm{sys.u}(t)$ at infinity is Cauchy. Concretely, for every $\varepsilon>0$, the image $\mathrm{sys.u}''[N,\infty)$ is a set in the image filter, and any two of its points are within $\varepsilon$. Hence the map is Cauchy. Since $H$ is complete, there exists $w\in H$ such that

$$
\mathrm{sys.u}(t)\to w
$$

strongly.

Finally, the proof compares this strong limit with the weak limit $\hat u$ obtained earlier. The continuous linear map

$$
\mathrm{toWeakSpace} : H\to \text{WeakSpace}(\mathbb R,H)
$$

is continuous, so strong convergence $\mathrm{sys.u}(t)\to w$ implies weak convergence

$$
\mathrm{toWeakSpace}(\mathrm{sys.u}(t))\to \mathrm{toWeakSpace}(w).
$$

But the scalar minimizing property already gave weak convergence of the same trajectory to $\mathrm{toWeakSpace}(\hat u)$. Since limits in a Hausdorff space are unique, `tendsto_nhds_unique` yields

$$
\mathrm{toWeakSpace}(w)=\mathrm{toWeakSpace}(\hat u).
$$

The map $\mathrm{toWeakSpace}$ is injective, so $w=\hat u$. Substituting this equality and using the earlier fact that $\hat u\in \mathrm{argmin}\Phi$, the proof concludes

$$
\exists \hat u\in \mathrm{argmin}\Phi,\qquad
\mathrm{sys.u}(t)\to \hat u
$$

strongly as $t\to\infty$.

