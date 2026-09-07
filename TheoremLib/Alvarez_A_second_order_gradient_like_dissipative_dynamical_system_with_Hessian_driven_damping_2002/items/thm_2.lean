import Mathlib
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_1
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_2
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_7
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.thm_1
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.cor_2
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.ext_thm_2
namespace Alvarez2002
open Filter

/-- A directional gradient identifies the Fréchet derivative of a `C¹`
potential.  This is the coordinate version needed by the analytic
Łojasiewicz estimate. -/
private theorem hasFDerivAt_of_coordinate_gradient {N : Type*} [Fintype N]
    (Φ : EuclideanSpace ℝ N → ℝ)
    (gradΦ : EuclideanSpace ℝ N → EuclideanSpace ℝ N) (hΦ : ContDiff ℝ 1 Φ)
    (hgrad : ∀ z w, HasDerivAt (fun r : ℝ => Φ (z + r • w))
      (∑ i, gradΦ z i * w i) 0) :
    ∀ z, HasFDerivAt Φ (innerSL ℝ (gradΦ z)) z := by
  intro z
  let D := fderiv ℝ Φ z
  have hdiff : DifferentiableAt ℝ Φ z :=
    (hΦ.differentiable (by norm_num)).differentiableAt
  have hD : HasFDerivAt Φ D z := by
    simpa [D] using hdiff.hasFDerivAt
  have hEq : D = innerSL ℝ (gradΦ z) := by
    ext w
    have hline : HasDerivAt (fun r : ℝ => z + r • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z
    have hcomp : HasDerivAt (fun r : ℝ => Φ (z + r • w)) (D w) 0 := by
      simpa [Function.comp_def] using hD.comp_hasDerivAt_of_eq 0 hline (by simp)
    exact hcomp.unique (by
      simpa [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using hgrad z w)
  simpa [hEq] using hD

private theorem sq_sum_le_two_sq_sum (a b : ℝ) :
    (a + b) ^ 2 ≤ 2 * (a ^ 2 + b ^ 2) := by
  nlinarith [sq_nonneg (a - b)]

/-- The interval estimate produced by the fractional-energy argument gives
integrability on its forward tail. -/
private theorem integrableOn_of_norm_interval_tail_bound {X : Type*}
    [NormedAddCommGroup X] (f : ℝ → X) (T B : ℝ) (hcont : Continuous f)
    (hbound : ∀ R, T ≤ R → ∫ s in T..R, ‖f s‖ ≤ B) :
    MeasureTheory.IntegrableOn f (Set.Ioi T) MeasureTheory.volume := by
  apply MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded B T
    (b := fun R : ℝ => R) (l := atTop)
  · intro R
    exact (hcont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  · exact tendsto_id
  · filter_upwards [eventually_ge_atTop T] with R hTR
    exact hbound R hTR

private theorem din_trajectory_continuous {N : Type*} [Fintype N]
    (Φ : EuclideanSpace ℝ N → ℝ)
    (α β : ℝ) (x : ℝ → EuclideanSpace ℝ N)
    (_hsol : IsDINTrajectory (EuclideanSpace ℝ N) Φ α β x)
    (hxreg : ContDiff ℝ 2 x) :
    Continuous x ∧ Continuous (deriv x) := by
  have hxC1 : ContDiff ℝ 1 x := hxreg.of_le (by norm_num)
  have hvC1 : ContDiff ℝ 1 (deriv x) := by
    have hdata := contDiff_succ_iff_deriv.mp
      (show ContDiff ℝ (1 + 1) x by simpa using hxreg)
    simpa using hdata.2.2
  exact ⟨hxC1.continuous, hvC1.continuous⟩

private theorem din_energy_hasDerivAt {N : Type*} [Fintype N]
    (Φ : EuclideanSpace ℝ N → ℝ) (α β : ℝ) (x : ℝ → EuclideanSpace ℝ N)
    (hΦ : AssumptionH (EuclideanSpace ℝ N) Φ)
    (hsol : IsDINTrajectory (EuclideanSpace ℝ N) Φ α β x)
    (hxreg : ContDiff ℝ 2 x) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivAt (dinForwardEnergy Φ β (α * β + 1) x)
      (-α * ‖deriv x t‖ ^ 2 - β * ‖gradient Φ (x t)‖ ^ 2) t := by
  have hΦC1 : ContDiff ℝ 1 Φ := hΦ.twice_continuously_differentiable.of_le (by norm_num)
  have hgradC1 : ContDiff ℝ 1 (gradient Φ) := by
    have hΦderivC1 : ContDiff ℝ 1 (fderiv ℝ Φ) := by
      exact (contDiff_succ_iff_fderiv.mp
        (show ContDiff ℝ (1 + 1) Φ by simpa using hΦ.twice_continuously_differentiable)).2.2
    simpa [gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ N)).symm.contDiff.comp hΦderivC1
  have hgradDeriv : HasFDerivAt (gradient Φ)
      (fderiv ℝ (gradient Φ) (x t)) (x t) :=
    (hgradC1.differentiable (by norm_num) (x t)).hasFDerivAt
  have hxAt : HasDerivAt x (deriv x t) t :=
    (hxreg.differentiable (by norm_num) t).hasDerivAt
  have hvAt : HasDerivAt (deriv x) (deriv (deriv x) t) t :=
    (hxreg.differentiable_deriv_two t).hasDerivAt
  have hgAt : HasDerivAt (fun s => gradient Φ (x s))
      ((fderiv ℝ (gradient Φ) (x t)) (deriv x t)) t := by
    simpa [Function.comp_def] using hgradDeriv.comp_hasDerivAt t hxAt
  have hΦAt : HasDerivAt (fun s => Φ (x s))
      (inner ℝ (gradient Φ (x t)) (deriv x t)) t := by
    have hp := (hΦC1.differentiable (by norm_num) (x t)).hasGradientAt.hasFDerivAt
      |>.comp_hasDerivAt t hxAt
    simpa [innerSL, Function.comp_def, real_inner_comm] using hp
  let r : ℝ → EuclideanSpace ℝ N := fun s => deriv x s + β • gradient Φ (x s)
  have hrAt : HasDerivAt r
      (deriv (deriv x) t + β • ((fderiv ℝ (gradient Φ) (x t)) (deriv x t))) t := by
    exact hvAt.add (hgAt.const_smul β)
  have hE := (hΦAt.const_smul (α * β + 1)).add (hrAt.norm_sq.const_mul (1 / 2 : ℝ))
  have heq := hsol.2.2 t ht
  have hacc : deriv (deriv x) t =
      -(α • deriv x t + β • ((fderiv ℝ (gradient Φ) (x t)) (deriv x t)) + gradient Φ (x t)) := by
    exact eq_neg_iff_add_eq_zero.mpr (by simpa [add_assoc] using heq)
  convert hE using 1
  rw [hacc]
  simp only [r, real_inner_self_eq_norm_sq,
    inner_add_left, inner_add_right, inner_neg_right, inner_smul_left, inner_smul_right]
  simp [real_inner_comm]
  ring_nf

set_option maxHeartbeats 1000000 in
-- The compactness and fractional-energy argument requires substantial elaboration.
/--
Theorem 4.1:
Strong convergence of a bounded finite-dimensional analytic `(DIN)` trajectory.
-/
theorem analytic_bounded_din_converges {N : Type*} [Fintype N]
    (Φ : EuclideanSpace ℝ N → ℝ)
    (x : ℝ → EuclideanSpace ℝ N)
    (hΦ : AssumptionH (EuclideanSpace ℝ N) Φ)
    (hanalytic : AnalyticOnNhd ℝ Φ Set.univ)
    (hsol : IsDINTrajectory (EuclideanSpace ℝ N) Φ α β x)
    (hxreg : ContDiff ℝ 2 x)
    (hbounded : Bornology.IsBounded (Set.range x)) :
    MeasureTheory.IntegrableOn (deriv x) (Set.Ioi (0 : ℝ)) MeasureTheory.volume ∧
    ∃ a, gradient Φ a = 0 ∧ Tendsto x atTop (nhds a) := by
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
  have hcoord : ∀ z w, HasDerivAt (fun r : ℝ => Φ (z + r • w))
      (inner ℝ (gradient Φ z) w) 0 := by
    intro z w
    have hline : HasDerivAt (fun r : ℝ => z + r • w) w 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add z
    have hcomp := (hgradF z).comp_hasDerivAt_of_eq 0 hline (by simp)
    simpa [innerSL] using hcomp
  have hlojall := connected_critical_set_lojasiewicz
    (Set.univ : Set (EuclideanSpace ℝ N)) (omegaLimit xI) Φ (gradient Φ) isOpen_univ
    ⟨isOpen_univ, hanalytic⟩ (Set.subset_univ _) hAnon hcoord hAcrit hAconn
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
end Alvarez2002
