## Source file
`Alvarez_Minimizing_property_second_order_dissipative_2000/items/thm_1.lean`

## Lean statement
```lean
theorem scalar_damped_minimizing_property {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {gamma : ℝ} {Phi : H → ℝ} {gradPhi : H → H}
    {u0 v0 : H} (hPhi : HasPotentialAssumption Phi)
    (sys : DissipativeSystem gamma Phi gradPhi u0 v0) :
    IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ici 0) ∧
    Tendsto (fun t => fderiv ℝ sys.u t 1) atTop (nhds 0) ∧
    Tendsto (fun t => Phi (sys.u t)) atTop (nhds (sInf (Set.range Phi))) ∧
    ((argmin Phi (potential_range_bddBelow hPhi)).Nonempty →
      ∃ uhat ∈ argmin Phi (potential_range_bddBelow hPhi),
      Tendsto (fun t => toWeakSpace ℝ H (sys.u t)) atTop (nhds (toWeakSpace ℝ H uhat)))
```

## Statement explanation
The declaration concerns a real Hilbert space \(H\), a potential \(\Phi:H\to\mathbb R\), a damping coefficient \(\gamma\), a gradient field `gradPhi`, and initial data \(u_0,v_0\in H\). The object `sys : DissipativeSystem gamma Phi gradPhi u0 v0` supplies the trajectory \(u(t)=\mathrm{sys}.u(t)\) of a damped second-order dissipative system. The proof uses the field `sys.gamma_pos`, which gives \(0<\gamma\), and the smoothness of the trajectory through `sys.contDiff`. The hypothesis `hPhi : HasPotentialAssumption Phi` is the potential-theoretic assumption on \(\Phi\); in the proof it is used through consequences such as boundedness below of \(\Phi\), the inequality \(\inf \Phi(H)\le \Phi(x)\), convexity of sublevel sets of \(\Phi\), and continuity of \(\Phi\).

The Lean expression `fderiv ℝ sys.u t 1` denotes the derivative \(u'(t)\) of the trajectory, viewed as the continuous linear map \(\mathbb R\to H\) evaluated at \(1\). Thus \(\|u'(t)\|^2\) is the squared speed. The value `sInf (Set.range Phi)` is the infimum of the set of all potential values, written below as \(\inf \Phi(H)\). The set `argmin Phi (potential_range_bddBelow hPhi)` is the set of global minimizers of \(\Phi\), namely
\[
\operatorname{argmin}\Phi
=
\left\{x\in H:\Phi(x)=\inf\Phi(H)\right\}.
\]
The argument `potential_range_bddBelow hPhi` is only the proof that this infimum is well-behaved; mathematically the set is just the minimizer set.

The conclusion is a four-part conjunction. First, the squared speed is integrable on \([0,\infty)\):
\[
\int_0^\infty \|u'(t)\|^2\,dt<\infty.
\]
Second, the velocity converges strongly to zero:
\[
u'(t)\to 0
\qquad (t\to\infty).
\]
Third, the potential along the trajectory converges to its infimum:
\[
\Phi(u(t))\to \inf\Phi(H)
\qquad (t\to\infty).
\]
Fourth, if the minimizer set is nonempty, then there is a minimizer \(\hat u\in \operatorname{argmin}\Phi\) such that the trajectory converges weakly to \(\hat u\):
\[
u(t)\rightharpoonup \hat u
\qquad (t\to\infty).
\]
The weak convergence is expressed in Lean by convergence in the weak topology, via `toWeakSpace ℝ H`.

## Lean proof
```lean
by
  have hvelIoi : IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ioi 0) :=
    scalar_velocity_sq_integrableOn_Ioi_zero hPhi sys
  have hvelIci : IntegrableOn (fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hvelIoi
  obtain ⟨energyLimit, henergyLimit⟩ := scalar_energy_converges hPhi sys
  obtain ⟨errorLimit, herrorLimit⟩ :=
    scalar_causal_velocity_error_converges sys hvelIci
  let energy : ℝ → ℝ := fun t =>
    (1 / 2 : ℝ) * ‖fderiv ℝ sys.u t 1‖ ^ 2 + Phi (sys.u t)
  let error : ℝ → ℝ := fun t => (3 / 2 : ℝ) *
    ∫ theta in 1..t, ∫ s in 0..theta,
      Real.exp (-gamma * (theta - s)) * ‖fderiv ℝ sys.u s 1‖ ^ 2
  have henergy : Tendsto energy atTop (nhds energyLimit) := by
    simpa [energy] using henergyLimit
  have herror : Tendsto error atTop (nhds errorLimit) := by
    simpa [error] using herrorLimit
  have henergyLower : ∀ t : ℝ, sInf (Set.range Phi) ≤ energy t := by
    intro t
    simpa [energy] using potential_sInf_le_scalar_energy hPhi sys t
  refine ⟨hvelIci, ?_⟩
  let q : ℝ → ℝ := fun t => ‖fderiv ℝ sys.u t 1‖ ^ 2
  let p : H → ℝ → ℝ := fun x t => (1 / 2 : ℝ) * ‖sys.u t - x‖ ^ 2
  let A : ℝ → ℝ := fun t =>
    (gamma * (t - 1) - 1 + Real.exp (-gamma * (t - 1))) / gamma ^ 2
  let B : ℝ → ℝ := fun t =>
    (1 - Real.exp (-gamma * (t - 1))) / gamma
  have hq_nonneg (t : ℝ) : 0 ≤ q t := sq_nonneg _
  have hpotential_le_energy (t : ℝ) : Phi (sys.u t) ≤ energy t := by
    dsimp [energy, q]
    nlinarith [sq_nonneg ‖fderiv ℝ sys.u t 1‖]
  have henergyLowerLimit : sInf (Set.range Phi) ≤ energyLimit := by
    exact ge_of_tendsto henergy (Filter.Eventually.of_forall henergyLower)
  have hA_pos : ∀ᶠ t in atTop, 0 < A t := by
    filter_upwards [eventually_ge_atTop (1 + 2 / gamma)] with t ht
    have hgamma : 0 < gamma := sys.gamma_pos
    have harg : 2 ≤ gamma * (t - 1) := by
      rw [mul_comm]
      apply (div_le_iff₀ hgamma).mp
      linarith
    have hexp : 0 < Real.exp (-gamma * (t - 1)) := Real.exp_pos _
    dsimp [A]
    apply div_pos
    · linarith
    · exact sq_pos_of_pos hgamma
  have hA_nonneg : ∀ t : ℝ, 1 ≤ t → 0 ≤ A t := by
    intro t ht
    simpa [A] using scalar_frozen_energy_coefficient_nonneg sys.gamma_pos ht
  -- The remaining comparison is the twice-integrated version of
  -- `scalar_distance_damped_frozen_energy_ineq`; its output will be divided
  -- by the eventually positive coefficient `A` above.
  have henergyEq : energyLimit = sInf (Set.range Phi) := by
    apply le_antisymm
    · by_contra hnot
      have hgap : 0 < energyLimit - sInf (Set.range Phi) := by
        have hle := henergyLowerLimit
        linarith
      let delta : ℝ := (energyLimit - sInf (Set.range Phi)) / 4
      have hdelta : 0 < delta := by dsimp [delta]; linarith
      rcases exists_lt_of_csInf_lt (b := sInf (Set.range Phi) + delta)
        (Set.range_nonempty Phi) (by
          linarith) with ⟨_, ⟨x, rfl⟩, hylt⟩
      have hcx : ∀ᶠ T in atTop,
          Phi x - energy T ≤ -(2 * delta) := by
        have hev := (tendsto_order.1 henergy).1 (sInf (Set.range Phi) + 3 * delta) (by
          dsimp [delta]
          linarith)
        filter_upwards [hev] with T hT
        have : Phi x ≤ sInf (Set.range Phi) + delta := hylt.le
        linarith
      have hinit : ∀ᶠ s in atTop,
          Real.exp (-gamma * (s - 1)) * deriv
            (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 ≤
              delta * Real.exp (-gamma) := by
        have he : Tendsto (fun s : ℝ => Real.exp (-gamma * (s - 1))) atTop
            (nhds 0) := by
          have harg : Tendsto (fun s : ℝ => -gamma * (s - 1)) atTop atBot := by
            have hlin : Tendsto (fun s : ℝ => -gamma * s) atTop atBot := by
              simpa [mul_comm] using
                (tendsto_id.atTop_mul_const_of_neg (neg_lt_zero.mpr sys.gamma_pos))
            simpa [sub_eq_add_neg, mul_add] using
              (Filter.tendsto_atBot_add_const_right atTop gamma hlin)
          exact (Real.tendsto_exp_atBot).comp harg
        have hmul := he.mul_const
          (deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1)
        have htarget : 0 * deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 <
            delta * Real.exp (-gamma) := by
          simp
          positivity
        have hev := (tendsto_order.1 hmul).2 (delta * Real.exp (-gamma)) htarget
        filter_upwards [hev] with s hs
        linarith
      have hRint : IntegrableOn (fun theta : ℝ =>
          ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * q s)
          (Set.Ici 0) := by
        simpa [q] using scalar_causal_exp_convolution_integrable q gamma
          sys.gamma_pos hvelIci
      let R : ℝ → ℝ := fun theta : ℝ =>
        ∫ s in 0..theta, Real.exp (-gamma * (theta - s)) * q s
      have hRnonneg : ∀ {a b : ℝ}, 0 ≤ a → a ≤ b →
          0 ≤ ∫ s in a..b, Real.exp (-gamma * (b - s)) * q s := by
        intro a b ha hab
        apply intervalIntegral.integral_nonneg hab
        intro s hs
        positivity
      have htail : ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ T in atTop, error T ≤ M := by
        refine ⟨|errorLimit| + 1, by positivity, ?_⟩
        have hev := herror.eventually (Metric.ball_mem_nhds errorLimit (ε := (1 : ℝ)) (by norm_num))
        filter_upwards [hev] with T hT
        have habs : |error T - errorLimit| < 1 := by
          simpa [Real.dist_eq, abs_sub_comm] using hT
        linarith [(abs_lt.mp habs).2, le_abs_self (errorLimit)]
      rcases htail with ⟨M, hMpos, hM⟩
      obtain ⟨a, ha_ge, ha_init, ha_energy, ha_err⟩ :=
        ((eventually_ge_atTop (2 : ℝ)).and (hinit.and (hcx.and hM))).exists
      have ha2 : (2 : ℝ) ≤ a := by
        exact le_trans (by norm_num) ha_ge
      have hTex : ∃ T : ℝ,
          ((a ≤ T ∧
            Real.exp (-gamma * (T - 1)) * deriv
              (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 ≤
                delta * Real.exp (-gamma) ∧
            Phi x - energy T ≤ -(2 * delta) ∧ error T ≤ M) ∧
            a + 1 < T) ∧
            a + 2 * (M + p x a + 1) / (delta * Real.exp (-gamma)) < T := by
        have hev := (eventually_ge_atTop a).and (hinit.and (hcx.and hM))
        have hev' := hev.and (eventually_gt_atTop (a + 1))
        have hev'' := hev'.and (eventually_gt_atTop
          (a + 2 * (M + p x a + 1) / (delta * Real.exp (-gamma))))
        simpa only [and_assoc] using hev''.exists
      rcases hTex with ⟨T, ⟨⟨hT_ge, hT_init, hT_energy, hT_err⟩, hTafter⟩, hTlarge⟩
      have hTa : a ≤ T := hT_ge
      have hTa_lt : a < T := lt_trans (by linarith) hTafter
      have hpoint : ∀ s ∈ Set.Ioo a T,
          deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) s ≤
            Real.exp (-gamma * (s - 1)) *
                deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 +
              (-(2 * delta)) * Real.exp (-gamma) + (3 / 2 : ℝ) * R s := by
        intro s hs
        have hs1 : 1 ≤ s := le_trans (by linarith [ha2]) (le_of_lt hs.1)
        have hsT : s ≤ T := hs.2.le
        have hbase := scalar_frozen_energy_first_integral hPhi sys
          (x := x) (theta := s) (t := T) hs1 hsT
        have hkcont : ContinuousOn (fun r : ℝ =>
            Real.exp (-gamma * (s - r))) (Set.Icc 0 s) := by
          exact (Real.continuous_exp.comp
            (continuous_const.mul (continuous_const.sub continuous_id))).continuousOn
        have hkint0 : IntervalIntegrable (fun r : ℝ =>
            Real.exp (-gamma * (s - r)) * q r) volume 0 1 := by
          have hi0 := (hvelIci.mono_set (Set.Icc_subset_Ici_self)).mul_continuousOn
            hkcont isCompact_Icc
          have hi : IntegrableOn (fun r : ℝ => q r * Real.exp (-gamma * (s - r)))
              (Set.Icc 0 1) volume := hi0.mono_set (by
                intro r hr
                change 0 ≤ r ∧ r ≤ s
                exact ⟨hr.1, le_trans hr.2 hs1⟩)
          simpa [q, mul_comm] using
            ((intervalIntegrable_iff_integrableOn_Icc_of_le (by norm_num)).mpr hi)
        have hkint1 : IntervalIntegrable (fun r : ℝ =>
            Real.exp (-gamma * (s - r)) * q r) volume 1 s := by
          have hi0 := (hvelIci.mono_set (Set.Icc_subset_Ici_self)).mul_continuousOn
            hkcont isCompact_Icc
          have hi : IntegrableOn (fun r : ℝ => q r * Real.exp (-gamma * (s - r)))
              (Set.Icc 1 s) volume := hi0.mono_set (by
                intro r hr
                change 0 ≤ r ∧ r ≤ s
                exact ⟨le_trans (by norm_num) hr.1, hr.2⟩)
          simpa [q, mul_comm] using
            ((intervalIntegrable_iff_integrableOn_Icc_of_le hs1).mpr hi)
        have hkintseg : IntervalIntegrable (fun r : ℝ =>
            Real.exp (-gamma * (s - r))) volume (s - 1) s := by
          apply ContinuousOn.intervalIntegrable_of_Icc (by linarith [hs1])
          exact hkcont.mono (by
            intro r hr
            change 0 ≤ r ∧ r ≤ s
            exact ⟨by linarith [hs1, hr.1], hr.2⟩)
        have hkintpre : IntervalIntegrable (fun r : ℝ =>
            Real.exp (-gamma * (s - r))) volume 1 (s - 1) := by
          apply ContinuousOn.intervalIntegrable_of_Icc (by linarith [ha2, hs.1])
          exact hkcont.mono (by
            intro r hr
            change 0 ≤ r ∧ r ≤ s
            exact ⟨by linarith [hr.1], le_trans hr.2 (by linarith [ha2, hs.1])⟩)
        have hkintall : IntervalIntegrable (fun r : ℝ =>
            Real.exp (-gamma * (s - r))) volume 1 s :=
          by
            have hkcont1 : ContinuousOn (fun r : ℝ => Real.exp (-gamma * (s - r)))
                (Set.Icc 1 s) := hkcont.mono (by
              intro r hr
              change 0 ≤ r ∧ r ≤ s
              exact ⟨by linarith [hr.1], hr.2⟩)
            exact hkcont1.intervalIntegrable_of_Icc hs1
        have hseg := intervalIntegral.integral_mono_on (by linarith : s - 1 ≤ s)
          (intervalIntegrable_const : IntervalIntegrable
            (fun _ : ℝ => Real.exp (-gamma)) volume (s - 1) s) hkintseg (by
            intro r hr
            have hr0 : 0 ≤ s - r := by linarith [hr.2]
            have hr1 : s - r ≤ 1 := by linarith [hr.1]
            exact Real.exp_le_exp.mpr (by nlinarith [sys.gamma_pos, hr0, hr1]))
        rw [intervalIntegral.integral_const] at hseg
        have hadd := intervalIntegral.integral_add_adjacent_intervals hkintpre hkintseg
        have hpre : 0 ≤ ∫ r in 1..(s - 1), Real.exp (-gamma * (s - r)) :=
          intervalIntegral.integral_nonneg (by linarith [ha2, hs.1])
            (by intro r hr; exact (Real.exp_pos _).le)
        have hK : Real.exp (-gamma) ≤ ∫ r in 1..s,
            Real.exp (-gamma * (s - r)) := by
          have hseg' : Real.exp (-gamma) ≤ ∫ r in (s - 1)..s,
              Real.exp (-gamma * (s - r)) := by
            simpa [smul_eq_mul] using hseg
          linarith
        have hqadd := intervalIntegral.integral_add_adjacent_intervals hkint0 hkint1
        have hqpre : 0 ≤ ∫ r in 0..1,
            Real.exp (-gamma * (s - r)) * q r :=
          intervalIntegral.integral_nonneg (by norm_num)
            (by intro r hr; positivity)
        have hqle : (∫ r in 1..s, Real.exp (-gamma * (s - r)) * q r) ≤ R s := by
          dsimp [R]
          linarith
        have hsplit : (∫ r in 1..s, Real.exp (-gamma * (s - r)) *
            (Phi x - energy T + (3 / 2 : ℝ) * q r)) =
            (Phi x - energy T) * (∫ r in 1..s, Real.exp (-gamma * (s - r))) +
              (3 / 2 : ℝ) * (∫ r in 1..s, Real.exp (-gamma * (s - r)) * q r) := by
          rw [show (fun r : ℝ => Real.exp (-gamma * (s - r)) *
              (Phi x - energy T + (3 / 2 : ℝ) * q r)) =
              (fun r => (Phi x - energy T) * Real.exp (-gamma * (s - r)) +
                (3 / 2 : ℝ) * (Real.exp (-gamma * (s - r)) * q r)) by
              funext r; ring]
          rw [intervalIntegral.integral_add
            ((intervalIntegrable_const : IntervalIntegrable
              (fun _ : ℝ => Phi x - energy T) volume 1 s).mul_continuousOn
                (by
                  simpa [Set.uIcc_of_le hs1] using
                    (hkcont.mono (by
                      intro r hr
                      change 0 ≤ r ∧ r ≤ s
                      exact ⟨by linarith [hr.1], hr.2⟩))))
            (hkint1.const_mul (3 / 2 : ℝ)),
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        have hc : Phi x - energy T ≤ -(2 * delta) := hT_energy
        have hck := mul_le_mul_of_nonpos_left hK (by linarith : Phi x - energy T ≤ 0)
        rw [hsplit] at hbase
        have hqscaled := mul_le_mul_of_nonneg_left hqle
          (by norm_num : (0 : ℝ) ≤ 3 / 2)
        have hsum := add_le_add hck hqscaled
        have hconst := mul_le_mul_of_nonneg_right hc (Real.exp_pos (-gamma)).le
        linarith
      have hpcont : ContDiffOn ℝ 2 (fun r : ℝ =>
          (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) (Set.Icc a T) := by
        have hu : ContDiffOn ℝ 2 sys.u (Set.Icc a T) :=
          sys.contDiff.mono (fun r hr => le_trans (by linarith [ha2]) hr.1)
        exact contDiffOn_const.mul (ContDiffOn.norm_sq ℝ (hu.sub contDiffOn_const))
      have hpint : IntervalIntegrable (deriv (fun r : ℝ =>
          (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2)) volume a T := by
        have hd := (hpcont.derivWithin (m := 0) (uniqueDiffOn_Icc hTa_lt) (by norm_num)).continuousOn
        apply (hd.intervalIntegrable_of_Icc hTa).congr_ae
        simp only [Set.uIoc_of_le hTa]
        rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
        filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with s hs
        exact derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)
      have hRintAT : IntervalIntegrable R volume a T := by
        apply (intervalIntegrable_iff_integrableOn_Icc_of_le hTa).mpr
        exact hRint.mono_set (by
          intro r hr
          change 0 ≤ r
          linarith [ha_ge, hr.1])
      have hmajint : IntervalIntegrable (fun s : ℝ =>
          Real.exp (-gamma * (s - 1)) *
            deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 +
          (-(2 * delta)) * Real.exp (-gamma) + (3 / 2 : ℝ) * R s) volume a T := by
        apply IntervalIntegrable.add
        · have hexpcont : ContinuousOn (fun s : ℝ => Real.exp (-gamma * (s - 1)))
              (Set.Icc a T) :=
            (Real.continuous_exp.comp (continuous_const.mul
              (continuous_id.sub continuous_const))).continuousOn
          have hexpint : IntervalIntegrable (fun s : ℝ => Real.exp (-gamma * (s - 1)))
              volume a T := hexpcont.intervalIntegrable_of_Icc hTa
          have hfirst : IntervalIntegrable (fun s : ℝ =>
              Real.exp (-gamma * (s - 1)) *
                deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1) volume a T :=
            hexpint.mul_continuousOn
              (continuousOn_const : ContinuousOn (fun _ : ℝ =>
                deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1) (Set.uIcc a T))
          exact hfirst.add (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ =>
              (-(2 * delta)) * Real.exp (-gamma)) volume a T)
        · exact hRintAT.const_mul (3 / 2 : ℝ)
      have hmono := intervalIntegral.integral_mono_on_of_le_Ioo hTa hpint hmajint hpoint
      have hFTC := intervalIntegral.integral_deriv_of_contDiffOn_Icc (hpcont.of_le (by norm_num)) hTa
      have hmono' := hmono
      rw [hFTC] at hmono'
      have hRle : (∫ s in a..T, R s) ≤ ∫ s in 1..T, R s := by
        have hRint1 : IntervalIntegrable R volume 1 a := by
          have h1a : (1 : ℝ) ≤ a := by linarith [ha2]
          apply (intervalIntegrable_iff_integrableOn_Icc_of_le h1a).mpr
          exact hRint.mono_set (by
            intro r hr
            change 0 ≤ r
            exact le_trans (by norm_num) hr.1)
        have haddR := intervalIntegral.integral_add_adjacent_intervals hRint1 hRintAT
        have hR01 : 0 ≤ ∫ s in 1..a, R s := by
          apply intervalIntegral.integral_nonneg (by linarith)
          intro s hs
          exact hRnonneg (a := 0) (b := s) (by norm_num) (by linarith [hs.1, ha2])
        linarith
      have hbound : (3 / 2 : ℝ) * (∫ s in 1..T, R s) ≤ M := by
        simpa [error, R, q] using hT_err
      have hlen : 0 ≤ T - a := by linarith
      have hinitInt :
          ∫ u in a..T,
            Real.exp (-gamma * (u - 1)) *
              deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1
            ≤ delta * Real.exp (-gamma) * (T - a) := by
        have hexpcont : ContinuousOn (fun u : ℝ => Real.exp (-gamma * (u - 1)))
            (Set.Icc a T) :=
          (Real.continuous_exp.comp (continuous_const.mul
            (continuous_id.sub continuous_const))).continuousOn
        have hexpint : IntervalIntegrable
            (fun u : ℝ => Real.exp (-gamma * (u - 1))) volume a T :=
          hexpcont.intervalIntegrable_of_Icc hTa
        have hDint : IntervalIntegrable
            (fun u : ℝ => Real.exp (-gamma * (u - 1)) *
              deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1) volume a T :=
          hexpint.mul_continuousOn
            (continuousOn_const : ContinuousOn (fun _ : ℝ =>
              deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1) (Set.uIcc a T))
        have hpointInit : ∀ u ∈ Set.Ioo a T,
            Real.exp (-gamma * (u - 1)) *
                deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 ≤
              delta * Real.exp (-gamma) := by
          intro u hu
          by_cases hD : deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 ≤ 0
          · have hleft : Real.exp (-gamma * (u - 1)) *
                deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 ≤ 0 :=
              mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hD
            have hright : 0 ≤ delta * Real.exp (-gamma) :=
              (mul_pos hdelta (Real.exp_pos _)).le
            linarith
          · have hDpos : 0 < deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 :=
              lt_of_not_ge hD
            have hexple : Real.exp (-gamma * (u - 1)) ≤
                Real.exp (-gamma * (a - 1)) := by
              apply Real.exp_le_exp.mpr
              nlinarith [sys.gamma_pos, hu.1.le]
            have hmul := mul_le_mul_of_nonneg_right hexple hDpos.le
            have ha' := ha_init
            have hinit_le := mul_le_mul_of_nonneg_right ha' (by positivity : (0 : ℝ) ≤ 1)
            nlinarith
        have hinitInt0 :=
          intervalIntegral.integral_mono_on_of_le_Ioo
            hTa hDint
            (intervalIntegrable_const :
              IntervalIntegrable (fun _ : ℝ => delta * Real.exp (-gamma)) volume a T)
            hpointInit
        rw [intervalIntegral.integral_const] at hinitInt0
        simpa [smul_eq_mul, mul_comm] using hinitInt0
      have hneg : delta * Real.exp (-gamma) / 2 * (T - a) >
          p x a + M + 1 := by
        have hTlarge' := hTlarge
        have hexp : 0 < Real.exp (-gamma) := Real.exp_pos _
        dsimp [p] at hTlarge'
        have hden : 0 < delta * Real.exp (-gamma) := mul_pos hdelta hexp
        have hratio : 2 * (M + p x a + 1) / (delta * Real.exp (-gamma)) < T - a := by
          linarith [hTlarge']
        have hprod := (div_lt_iff₀ hden).mp hratio
        nlinarith [hprod]
      have hpa : 0 ≤ (1 / 2 : ℝ) * ‖sys.u a - x‖ ^ 2 := by positivity
      have hpt : 0 ≤ (1 / 2 : ℝ) * ‖sys.u T - x‖ ^ 2 := by positivity
      have hsplitRhs :
          (∫ u in a..T,
            (Real.exp (-gamma * (u - 1)) *
                deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1 +
              (-(2 * delta)) * Real.exp (-gamma) + (3 / 2 : ℝ) * R u)) =
            (∫ u in a..T,
              Real.exp (-gamma * (u - 1)) *
                deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1) +
              (-(2 * delta)) * Real.exp (-gamma) * (T - a) +
              (3 / 2 : ℝ) * (∫ u in a..T, R u) := by
        have hfirstInt : IntervalIntegrable (fun u : ℝ =>
            Real.exp (-gamma * (u - 1)) *
              deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1) volume a T := by
          have hexpcont : ContinuousOn (fun u : ℝ => Real.exp (-gamma * (u - 1)))
              (Set.Icc a T) :=
            (Real.continuous_exp.comp (continuous_const.mul
              (continuous_id.sub continuous_const))).continuousOn
          have hexpint : IntervalIntegrable
              (fun u : ℝ => Real.exp (-gamma * (u - 1))) volume a T :=
            hexpcont.intervalIntegrable_of_Icc hTa
          exact hexpint.mul_continuousOn
            (continuousOn_const : ContinuousOn (fun _ : ℝ =>
              deriv (fun r => (1 / 2 : ℝ) * ‖sys.u r - x‖ ^ 2) 1) (Set.uIcc a T))
        have hconstInt : IntervalIntegrable (fun _ : ℝ =>
            (-(2 * delta)) * Real.exp (-gamma)) volume a T :=
          intervalIntegrable_const
        have hRscaled : IntervalIntegrable (fun u : ℝ => (3 / 2 : ℝ) * R u) volume a T :=
          hRintAT.const_mul (3 / 2 : ℝ)
        rw [intervalIntegral.integral_add (hfirstInt.add hconstInt) hRscaled,
          intervalIntegral.integral_add hfirstInt hconstInt,
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
        ring
      rw [hsplitRhs] at hmono'
      have hRscaled : (3 / 2 : ℝ) * (∫ s in a..T, R s) ≤
          (3 / 2 : ℝ) * (∫ s in 1..T, R s) :=
        mul_le_mul_of_nonneg_left hRle (by norm_num)
      dsimp [p] at hneg
      have hstep :
          (1 / 2 : ℝ) * ‖sys.u T - x‖ ^ 2 -
              (1 / 2 : ℝ) * ‖sys.u a - x‖ ^ 2 ≤
            -(delta * Real.exp (-gamma)) * (T - a) + M := by
        nlinarith [hmono', hinitInt, hRscaled, hbound]
      have hneg2 : delta * Real.exp (-gamma) * (T - a) >
          2 * ((1 / 2 : ℝ) * ‖sys.u a - x‖ ^ 2 + M + 1) := by
        nlinarith [hneg]
      have hpt_bound : (1 / 2 : ℝ) * ‖sys.u T - x‖ ^ 2 ≤
          (1 / 2 : ℝ) * ‖sys.u a - x‖ ^ 2 -
            delta * Real.exp (-gamma) * (T - a) + M := by
        linarith [hstep]
      have hneg3 : (1 / 2 : ℝ) * ‖sys.u a - x‖ ^ 2 -
          delta * Real.exp (-gamma) * (T - a) + M < 0 := by
        have hneg2' := hneg2
        ring_nf at hneg2' ⊢
        nlinarith [hneg2', hMpos, sq_nonneg ‖sys.u a - x‖]
      linarith [hpt_bound, hneg3, hpt]
    · exact henergyLowerLimit
  have hpotential : Tendsto (fun t => Phi (sys.u t)) atTop
      (nhds (sInf (Set.range Phi))) := by
    have henergy' : Tendsto energy atTop (nhds (sInf (Set.range Phi))) := by
      simpa [henergyEq] using henergy
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => sInf (Set.range Phi)) atTop
        (nhds (sInf (Set.range Phi)))) henergy'
    · intro t
      exact potential_sInf_le hPhi (sys.u t)
    · intro t
      exact hpotential_le_energy t
  have hvel0 : Tendsto (fun t => fderiv ℝ sys.u t 1) atTop (nhds 0) := by
    apply scalar_velocity_tendsto_zero_of_energy_potential_tendsto sys henergy
    simpa [henergyEq] using hpotential
  have hargmin : ∀ z ∈ argmin Phi (potential_range_bddBelow hPhi),
      ∃ l : ℝ, Tendsto (fun t => ‖sys.u t - z‖) atTop (nhds l) := by
    intro z hz
    exact scalar_distance_to_minimizer_converges hPhi sys hvelIci z hz
  refine ⟨hvel0, hpotential, ?_⟩
  intro hne
  have hcluster : ∀ z, (∃ u : ℕ → ℝ, Tendsto u atTop atTop ∧
      ∀ f : H →L[ℝ] ℝ, Tendsto (fun n => f (sys.u (u n))) atTop
        (nhds (f z))) → z ∈ argmin Phi (potential_range_bddBelow hPhi) := by
    intro z hz
    rcases hz with ⟨u, hu, hweak⟩
    have hphiSeq : Tendsto (fun n => Phi (sys.u (u n))) atTop
        (nhds (sInf (Set.range Phi))) := by
      simpa [Function.comp_def] using hpotential.comp hu
    have hweak' : Tendsto (fun n => toWeakSpace ℝ H (sys.u (u n))) atTop
        (nhds (toWeakSpace ℝ H z)) := by
      apply (weakConvergence_iff_forall_tendsto_inner_right _ z).2
      intro y
      let f : H →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ H) y
      have hf := hweak f
      simpa [f, InnerProductSpace.toDual_apply_apply, real_inner_comm] using hf
    have hzle : Phi z ≤ sInf (Set.range Phi) := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have hev := (tendsto_order.1 hphiSeq).2 (sInf (Set.range Phi) + ε) (by linarith)
      obtain ⟨N, hN⟩ := (eventually_atTop.1 hev)
      let v : ℕ → H := fun n => sys.u (u (n + N))
      have hv_mem : ∀ n : ℕ, v n ∈ {w : H | Phi w ≤ sInf (Set.range Phi) + ε} := by
        intro n
        dsimp [v]
        exact le_of_lt (hN (n + N) (by omega))
      have hshift : Tendsto (fun n : ℕ => n + N) atTop atTop := by
        refine tendsto_atTop.2 ?_
        intro b
        exact eventually_atTop.2 ⟨b, fun n hn => le_trans hn (Nat.le_add_right n N)⟩
      have hvweak : Tendsto (fun n => toWeakSpace ℝ H (v n)) atTop
          (nhds (toWeakSpace ℝ H z)) := by
        simpa [v, Function.comp_def] using hweak'.comp hshift
      have hclosed : IsClosed {w : H | Phi w ≤ sInf (Set.range Phi) + ε} :=
        isClosed_le hPhi.contDiff.continuous continuous_const
      have hconvex : Convex ℝ {w : H | Phi w ≤ sInf (Set.range Phi) + ε} := by
        simpa only [Set.mem_univ, true_and] using hPhi.convex.convex_le
          (sInf (Set.range Phi) + ε)
      exact mem_of_tendsto_weakly_of_isClosed_convex hclosed hconvex hv_mem hvweak
    have hzmin : Phi z = sInf (Set.range Phi) :=
      le_antisymm hzle (potential_sInf_le hPhi z)
    simpa [argmin] using hzmin
  obtain ⟨uhat, hUhat, hUweak⟩ := opial_lemma_continuous_weak sys.u
    (argmin Phi (potential_range_bddBelow hPhi)) hne hargmin hcluster
  refine ⟨uhat, hUhat, ?_⟩
  apply (weakConvergence_iff_forall_tendsto_inner_right sys.u uhat).2
  intro y
  let f : H →L[ℝ] ℝ := (InnerProductSpace.toDual ℝ H) y
  have hf := hUweak f
  dsimp [f] at hf
  simpa only [InnerProductSpace.toDual_apply_apply, real_inner_comm] using hf
```

## Proof explanation
The proof first establishes the squared-speed integrability and then studies the energy and the causal velocity error. The cited result `scalar_velocity_sq_integrableOn_Ioi_zero hPhi sys` gives integrability of
\[
t\mapsto \|u'(t)\|^2
\]
on \((0,\infty)\). The Lean lemma `integrableOn_Ici_iff_integrableOn_Ioi` converts this to integrability on \([0,\infty)\), which is the first conjunct.

Next, `scalar_energy_converges hPhi sys` provides a real number `energyLimit` such that
\[
E(t)=\frac12\|u'(t)\|^2+\Phi(u(t))
\]
converges to `energyLimit` as \(t\to\infty\). Independently, `scalar_causal_velocity_error_converges sys hvelIci` uses the already proved integrability of \(\|u'(t)\|^2\) on \([0,\infty)\) to provide a real number `errorLimit` such that
\[
\frac32\int_1^t\int_0^\theta
e^{-\gamma(\theta-s)}\|u'(s)\|^2\,ds\,d\theta
\]
converges to `errorLimit`. In the proof these two functions are named `energy` and `error`; the `simpa` steps simply unfold those local definitions so that the convergence statements match the definitions.

The inequality `potential_sInf_le_scalar_energy hPhi sys t` gives, for every \(t\),
\[
\inf\Phi(H)\le \frac12\|u'(t)\|^2+\Phi(u(t))=E(t).
\]
Since \(E(t)\to\text{energyLimit}\), the limit comparison rule `ge_of_tendsto` yields
\[
\inf\Phi(H)\le \text{energyLimit}.
\]
The proof then defines the coefficient
\[
A(t)=\frac{\gamma(t-1)-1+e^{-\gamma(t-1)}}{\gamma^2}.
\]
It proves that \(A(t)>0\) eventually, using \(t\ge 1+2/\gamma\) and \(\gamma>0\), and that \(A(t)\ge 0\) for \(t\ge 1\), using the cited lemma `scalar_frozen_energy_coefficient_nonneg`. These are preparatory coefficient facts; in the visible continuation of the proof the main contradiction argument proceeds without explicitly invoking them again.

The key step is proving
\[
\text{energyLimit}=\inf\Phi(H).
\]
The inequality \(\inf\Phi(H)\le\text{energyLimit}\) has already been obtained. For the reverse inequality, the proof argues by contradiction and assumes \(\text{energyLimit}>\inf\Phi(H)\). It sets
\[
d=\frac{\text{energyLimit}-\inf\Phi(H)}4>0.
\]
Using the definition of infimum, it chooses \(x\in H\) with
\[
\Phi(x)<\inf\Phi(H)+d.
\]
Since \(E(t)\to\text{energyLimit}\) and \(\text{energyLimit}>\inf\Phi(H)+3d\), eventually
\[
E(t)>\inf\Phi(H)+3d,
\]
and therefore, because \(\Phi(x)\le \inf\Phi(H)+d\), eventually
\[
\Phi(x)-E(t)\le -2d.
\]
The proof also notes that the initial exponential term
\[
e^{-\gamma(t-1)}p_x'(1),
\qquad
p_x(r)=\frac12\|u(r)-x\|^2,
\]
tends to \(0\), so eventually it is at most \(d e^{-\gamma}\). Finally, because the error function converges, it is eventually bounded by some real number \(M\ge 0\).

The proof then chooses \(a\ge 2\) satisfying these eventual estimates at \(a\), and then chooses \(T>a\) satisfying them at \(T\), with additionally
\[
T>a+1
\]
and
\[
T>a+\frac{2(M+p_x(a)+1)}{d e^{-\gamma}}.
\]
For \(s\in(a,T)\), the cited lemma `scalar_frozen_energy_first_integral` gives
\[
p_x'(s)\le
e^{-\gamma(s-1)}p_x'(1)
+
\int_1^s e^{-\gamma(s-r)}
\left(\Phi(x)-E(T)+\frac32\|u'(r)\|^2\right)dr.
\]
Using \(\Phi(x)-E(T)\le -2d\), nonnegativity of \(\|u'(r)\|^2\), and the lower bound
\[
\int_1^s e^{-\gamma(s-r)}\,dr\ge e^{-\gamma},
\]
the proof deduces
\[
p_x'(s)\le
e^{-\gamma(s-1)}p_x'(1)-2d e^{-\gamma}+\frac32 R(s),
\]
where
\[
R(s)=\int_0^s e^{-\gamma(s-r)}\|u'(r)\|^2\,dr.
\]
The integrability of \(R\) on \([0,\infty)\) comes from `scalar_causal_exp_convolution_integrable`, applied to \(g(r)=\|u'(r)\|^2\) and \(\gamma>0\).

Now the proof integrates the pointwise inequality from \(a\) to \(T\). The fundamental theorem of calculus, `intervalIntegral.integral_deriv_of_contDiffOn_Icc`, gives
\[
\int_a^T p_x'(s)\,ds=p_x(T)-p_x(a).
\]
The first exponential term is bounded using the eventual inequality at \(a\), yielding
\[
\int_a^T e^{-\gamma(s-1)}p_x'(1)\,ds
\le d e^{-\gamma}(T-a).
\]
The \(R\)-term is bounded using the fact that \(R\ge 0\) and
\[
\frac32\int_1^T R(s)\,ds=\text{error}(T)\le M,
\]
so
\[
\frac32\int_a^T R(s)\,ds\le M.
\]
Combining these estimates gives
\[
p_x(T)-p_x(a)
\le -d e^{-\gamma}(T-a)+M.
\]
But \(T\) was chosen so large that
\[
d e^{-\gamma}(T-a)>2(p_x(a)+M+1),
\]
hence
\[
p_x(T)
\le p_x(a)-d e^{-\gamma}(T-a)+M<0.
\]
This contradicts the definition
\[
p_x(T)=\frac12\|u(T)-x\|^2\ge 0.
\]
Therefore the assumption \(\text{energyLimit}>\inf\Phi(H)\) is impossible, and
\[
\text{energyLimit}=\inf\Phi(H).
\]

Once this equality is known, the potential convergence follows by squeezing. For every \(t\),
\[
\inf\Phi(H)\le \Phi(u(t))\le E(t),
\]
where the lower bound is `potential_sInf_le hPhi (sys.u t)` and the upper bound follows from the definition of \(E(t)\). Since both the lower bound and \(E(t)\) tend to \(\inf\Phi(H)\), the squeeze theorem `tendsto_of_tendsto_of_tendsto_of_le_of_le` gives
\[
\Phi(u(t))\to \inf\Phi(H).
\]

The velocity convergence is then immediate from the cited result `scalar_velocity_tendsto_zero_of_energy_potential_tendsto`. That lemma says that if the total energy tends to some \(m\) and the potential \(\Phi(u(t))\) also tends to the same \(m\), then \(u'(t)\to 0\). Here both limits are \(\inf\Phi(H)\), so
\[
u'(t)\to 0.
\]

For the minimizer statement, the proof first shows that for every \(z\in\operatorname{argmin}\Phi\), the distance \(\|u(t)-z\|\) has a limit as \(t\to\infty\). This is exactly the content of `scalar_distance_to_minimizer_converges`, applied to \(z\), the minimizer hypothesis \(z\in\operatorname{argmin}\Phi\), and the already established integrability of \(\|u'(t)\|^2\) on \([0,\infty)\).

Finally the proof assumes the minimizer set is nonempty. It must show that some minimizer is the weak limit of \(u(t)\). First it proves that every weak sequential cluster point of the trajectory is a minimizer. Suppose a sequence of times \(u_n\to\infty\) and \(u(u_n)\) converges weakly to some \(z\), meaning that for every continuous linear functional \(f:H\to\mathbb R\),
\[
f(u(u_n))\to f(z).
\]
Composing the already proved potential convergence with \(u_n\to\infty\), the proof obtains
\[
\Phi(u(u_n))\to \inf\Phi(H).
\]
For any \(\varepsilon>0\), eventually
\[
\Phi(u(u_n))\le \inf\Phi(H)+\varepsilon.
\]
The set
\[
C_\varepsilon=\{w\in H:\Phi(w)\le \inf\Phi(H)+\varepsilon\}
\]
is closed because \(\Phi\) is continuous and convex because \(\Phi\) is convex. The cited lemma `mem_of_tendsto_weakly_of_isClosed_convex` says that a weakly convergent sequence whose terms lie in a closed convex set has its weak limit in that set. Applying it to a tail of the sequence shows \(z\in C_\varepsilon\). Since this holds for every \(\varepsilon>0\), one gets
\[
\Phi(z)\le \inf\Phi(H).
\]
The reverse inequality \(\inf\Phi(H)\le \Phi(z)\) is `potential_sInf_le hPhi z`. Hence \(\Phi(z)=\inf\Phi(H)\), so \(z\in\operatorname{argmin}\Phi\).

The proof now applies Opial’s lemma in the form `opial_lemma_continuous_weak`. Its hypotheses are: the minimizer set is nonempty; for every minimizer \(z\), the distance \(\|u(t)-z\|\) has a limit; and every weak sequential cluster point of the trajectory lies in the minimizer set. Its conclusion is that there exists a minimizer \(\hat u\) such that for every continuous linear functional \(f\),
\[
f(u(t))\to f(\hat u).
\]
Finally, the lemma `weakConvergence_iff_forall_tendsto_inner_right` converts this functional convergence into weak convergence. For each \(y\in H\), take the continuous linear functional \(f_y(x)=\langle x,y\rangle\). The functional convergence gives
\[
\langle u(t),y\rangle\to \langle \hat u,y\rangle.
\]
Since this holds for every \(y\), the trajectory converges weakly to \(\hat u\). Thus the last conjunct of the theorem is proved.

