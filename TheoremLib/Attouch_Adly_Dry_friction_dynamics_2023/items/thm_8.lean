import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_3
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.thm_3
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.lem_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_4

namespace AttouchAdlyDryFrictionDynamics2023

open Filter

/-- The second-order dual inertial system (DRYSTARDE).

The derivatives in the equation are the actual derivatives of `w`; they are
not independent trajectories supplied as part of the data.  The final term is
`gradient psi*`, namely `q - proj_B(q)`. -/
def IsDryStarDualInertial {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (r : ℝ) (hr : 0 < r) (α s₀ : ℝ) (fstar : H → ℝ) (w : ℝ → H) : Prop :=
  ∀ s ∈ Set.Ici s₀,
    fderiv ℝ (gradient fstar)
        (w s + (s / (α - 1)) • deriv w s)
        (deriv (deriv w) s + (α / s) • deriv w s) +
      (w s + (s / (α - 1)) • deriv w s -
        frictionBallProjection r hr
          (w s + (s / (α - 1)) • deriv w s)) = 0

private theorem quadratic_timeScale_tendsto_atTop {α : ℝ} (hα : 1 < α) :
    Tendsto (fun s : ℝ => s ^ 2 / (2 * (α - 1))) atTop atTop := by
  have hden : 0 < 2 * (α - 1) := mul_pos (by norm_num) (sub_pos.mpr hα)
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [eventually_ge_atTop (max 1 (2 * (α - 1) * b))] with s hs
  have hs1 : 1 ≤ s := le_trans (le_max_left _ _) hs
  have hsb : 2 * (α - 1) * b ≤ s := le_trans (le_max_right _ _) hs
  apply (le_div_iff₀ hden).2
  nlinarith [sq_nonneg (s - 1)]

private theorem scaled_point_eq
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {s₀ α s : ℝ} (hs₀ : 0 < s₀) (hα : 1 < α) (hs : s ∈ Set.Ici s₀)
    {v w : ℝ → H}
    (hode : deriv w s + (s / (α - 1))⁻¹ • (w s - v s) = 0) :
    w s + (s / (α - 1)) • deriv w s = v s := by
  have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
  have hcpos : 0 < s / (α - 1) := div_pos hspos (sub_pos.mpr hα)
  have hcne : s / (α - 1) ≠ 0 := ne_of_gt hcpos
  have hdw : deriv w s = (s / (α - 1))⁻¹ • (v s - w s) := by
    rw [show w s - v s = -(v s - w s) by abel, smul_neg] at hode
    exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg, add_comm] using hode)
  rw [hdw, smul_smul, mul_inv_cancel₀ hcne, one_smul]
  abel

private theorem timeScaled_distance_rate
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {r α : ℝ} (hα : 1 < α) (g : ℝ → H)
    (hg : Tendsto
      (fun t : ℝ => Real.sqrt t * Metric.infDist (g t) (frictionBall r))
      atTop (nhds 0)) :
    Tendsto
      (fun s : ℝ => s * Metric.infDist
        (g (s ^ 2 / (2 * (α - 1)))) (frictionBall r))
      atTop (nhds 0) := by
  let τ : ℝ → ℝ := fun s => s ^ 2 / (2 * (α - 1))
  have hcomp : Tendsto
      (fun s : ℝ => Real.sqrt (τ s) * Metric.infDist (g (τ s)) (frictionBall r))
      atTop (nhds 0) := by
    simpa [Function.comp_def] using hg.comp (quadratic_timeScale_tendsto_atTop hα)
  let c : ℝ := Real.sqrt (2 * (α - 1))
  have hmul := hcomp.const_mul c
  have heq : (fun s : ℝ => c *
      (Real.sqrt (τ s) * Metric.infDist (g (τ s)) (frictionBall r))) =ᶠ[atTop]
      (fun s : ℝ => s * Metric.infDist
        (g (s ^ 2 / (2 * (α - 1)))) (frictionBall r)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
    have hden : 0 < 2 * (α - 1) := mul_pos (by norm_num) (sub_pos.mpr hα)
    have hsqrt : c * Real.sqrt (τ s) = s := by
      dsimp [c, τ]
      rw [Real.sqrt_div (sq_nonneg s), Real.sqrt_sq_eq_abs, abs_of_nonneg hs]
      field_simp [ne_of_gt (Real.sqrt_pos.2 hden)]
    rw [← mul_assoc, hsqrt]
  simpa using hmul.congr' heq

private theorem weightedAverage_power_formula
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {s₀ α : ℝ} (hs₀ : 0 < s₀) (hα : 1 < α) (v w : ℝ → H)
    (hv : Continuous v) (hw : Differentiable ℝ w)
    (hode : ∀ s ∈ Set.Ici s₀,
      deriv w s + (s / (α - 1))⁻¹ • (w s - v s) = 0) :
    ∀ s ∈ Set.Ici s₀,
      s ^ (α - 1) • w s =
        s₀ ^ (α - 1) • w s₀ +
          ∫ u in s₀..s, ((α - 1) * u ^ (α - 2)) • v u := by
  intro s hs
  have hαsub : 0 < α - 1 := sub_pos.mpr hα
  let F : ℝ → H := fun u => u ^ (α - 1) • w u
  let F' : ℝ → H := fun u => ((α - 1) * u ^ (α - 2)) • v u
  have hF : ∀ u ∈ Set.Ici s₀, HasDerivAt F (F' u) u := by
    intro u hu
    have hupos : 0 < u := lt_of_lt_of_le hs₀ hu
    have hune : u ≠ 0 := ne_of_gt hupos
    have hcne : u / (α - 1) ≠ 0 := div_ne_zero hune (ne_of_gt hαsub)
    have hraw := (Real.hasDerivAt_rpow_const (p := α - 1) (Or.inl hune)).smul
      (hw u).hasDerivAt
    have hvel : deriv w u = (u / (α - 1))⁻¹ • (v u - w u) := by
      have huode := hode u hu
      rw [show w u - v u = -(v u - w u) by abel, smul_neg] at huode
      exact eq_of_sub_eq_zero (by
        simpa [sub_eq_add_neg, add_comm] using huode)
    have hrpow : u ^ (α - 1) = u * u ^ (α - 2) := by
      calc
        u ^ (α - 1) = u ^ ((α - 2) + 1) := by ring_nf
        _ = u ^ (α - 2) * u ^ (1 : ℝ) := Real.rpow_add hupos (α - 2) 1
        _ = u * u ^ (α - 2) := by rw [Real.rpow_one]; ring
    have hexp : α - 1 - 1 = α - 2 := by ring
    have hcoeff : u ^ (α - 1) * (u / (α - 1))⁻¹ =
        (α - 1) * u ^ (α - 2) := by
      rw [hrpow]
      field_simp [hune, ne_of_gt hαsub]
    dsimp [F, F']
    convert hraw using 1
    rw [hvel, hexp, smul_smul, hcoeff]
    module
  have hFint : IntervalIntegrable F' MeasureTheory.volume s₀ s := by
    apply ContinuousOn.intervalIntegrable
    intro u hu
    have hsle : s₀ ≤ s := hs
    have hupos : 0 < u := lt_of_lt_of_le hs₀ (Set.uIcc_of_le hsle ▸ hu).1
    exact (((continuousAt_const.mul
      (Real.continuousAt_rpow_const u (α - 2) (Or.inl (ne_of_gt hupos)))).smul
        hv.continuousAt).continuousWithinAt)
  have hFTC : ∫ u in s₀..s, F' u = F s - F s₀ := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro u hu
      exact hF u (by
        rw [Set.uIcc_of_le (show s₀ ≤ s from hs)] at hu
        exact hu.1)
    · exact hFint
  dsimp [F, F'] at hFTC ⊢
  rw [hFTC]
  abel

private theorem weightedAverage_distance_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {s₀ r α : ℝ} (hr : 0 < r) (hs₀ : 0 < s₀)
    (hα : 1 < α) (v w : ℝ → H) (hv : Continuous v)
    (hw₀ : w s₀ = v s₀)
    (hformula : ∀ s ∈ Set.Ici s₀,
      s ^ (α - 1) • w s =
        s₀ ^ (α - 1) • w s₀ +
          ∫ u in s₀..s, ((α - 1) * u ^ (α - 2)) • v u) :
    ∀ s ∈ Set.Ici s₀,
      s ^ (α - 1) * Metric.infDist (w s) (frictionBall r) ≤
        s₀ ^ (α - 1) * Metric.infDist (v s₀) (frictionBall r) +
          ∫ u in s₀..s, ((α - 1) * u ^ (α - 2)) *
            Metric.infDist (v u) (frictionBall r) := by
  intro s hs
  have hsle : s₀ ≤ s := hs
  have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
  have hαsub : 0 < α - 1 := sub_pos.mpr hα
  let weight : ℝ → ℝ := fun u => (α - 1) * u ^ (α - 2)
  let D : H → ℝ := fun x => Metric.infDist x (frictionBall r)
  have hweight : ∀ u ∈ Set.Icc s₀ s, 0 ≤ weight u := by
    intro u hu
    exact mul_nonneg hαsub.le (Real.rpow_nonneg (le_trans hs₀.le hu.1) _)
  have hmass : ∫ u in s₀..s, weight u = s ^ (α - 1) - s₀ ^ (α - 1) := by
    dsimp [weight]
    rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by linarith : -1 < α - 2))]
    have hident : α - 2 + 1 = α - 1 := by ring
    rw [hident]
    field_simp [ne_of_gt hαsub]
  have hnormInt :
      ‖∫ u in s₀..s, weight u • v u‖ ≤
        ∫ u in s₀..s, weight u * ‖v u‖ := by
    calc
      ‖∫ u in s₀..s, weight u • v u‖ ≤
          ∫ u in s₀..s, ‖weight u • v u‖ :=
        intervalIntegral.norm_integral_le_integral_norm hsle
      _ = ∫ u in s₀..s, weight u * ‖v u‖ := by
        apply intervalIntegral.integral_congr
        intro u hu
        change ‖weight u • v u‖ = weight u * ‖v u‖
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg]
        exact hweight u (by simpa only [Set.uIcc_of_le hsle] using hu)
  have hnorm : s ^ (α - 1) * ‖w s‖ ≤
      s₀ ^ (α - 1) * ‖v s₀‖ + ∫ u in s₀..s, weight u * ‖v u‖ := by
    have h := norm_add_le (s₀ ^ (α - 1) • w s₀)
      (∫ u in s₀..s, weight u • v u)
    rw [← hformula s hs, hw₀, norm_smul, norm_smul,
      Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hspos.le _),
      abs_of_nonneg (Real.rpow_nonneg hs₀.le _)] at h
    exact h.trans (add_le_add_right hnormInt _)
  have hweight_cont : ContinuousOn weight (Set.Icc s₀ s) := by
    intro u hu
    have hupos : 0 < u := lt_of_lt_of_le hs₀ hu.1
    exact (continuousAt_const.mul
      (Real.continuousAt_rpow_const u (α - 2) (Or.inl (ne_of_gt hupos)))).continuousWithinAt
  have hDcont : Continuous (fun u : ℝ => D (v u)) := by
    dsimp [D]
    simp_rw [infDist_frictionBall_eq r hr]
    exact ((hv.norm.sub continuous_const).max continuous_const)
  have hnormDiffInt : IntervalIntegrable (fun u => weight u * (‖v u‖ - r))
      MeasureTheory.volume s₀ s := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hsle, Pi.mul_apply, Pi.sub_apply,
      Pi.ofNat_apply] using
      hweight_cont.mul ((hv.norm.sub continuous_const).continuousOn)
  have hDIntg : IntervalIntegrable (fun u => weight u * D (v u))
      MeasureTheory.volume s₀ s := by
    apply ContinuousOn.intervalIntegrable
    simpa only [Set.uIcc_of_le hsle, Pi.mul_apply] using
      hweight_cont.mul hDcont.continuousOn
  have hDInt : ∫ u in s₀..s, weight u * (‖v u‖ - r) ≤
      ∫ u in s₀..s, weight u * D (v u) := by
    apply intervalIntegral.integral_mono_on hsle hnormDiffInt hDIntg
    intro u hu
    exact mul_le_mul_of_nonneg_left
      (by
        dsimp [D]
        rw [infDist_frictionBall_eq r hr]
        exact le_max_left _ _)
      (hweight u hu)
  have hrhs_nonneg : 0 ≤
      s₀ ^ (α - 1) * D (v s₀) + ∫ u in s₀..s, weight u * D (v u) := by
    apply add_nonneg
    · exact mul_nonneg (Real.rpow_nonneg hs₀.le _) Metric.infDist_nonneg
    · apply intervalIntegral.integral_nonneg hsle
      intro u hu
      exact mul_nonneg (hweight u hu) Metric.infDist_nonneg
  rw [infDist_frictionBall_eq r hr]
  change s ^ (α - 1) * max (‖w s‖ - r) 0 ≤ _
  by_cases hws : ‖w s‖ ≤ r
  · rw [max_eq_right (sub_nonpos.mpr hws), mul_zero]
    exact hrhs_nonneg
  · rw [max_eq_left (sub_nonneg.mpr (not_le.mp hws).le)]
    have hsub : s ^ (α - 1) * (‖w s‖ - r) ≤
        s₀ ^ (α - 1) * (‖v s₀‖ - r) +
          ∫ u in s₀..s, weight u * (‖v u‖ - r) := by
      have hnormIntg : IntervalIntegrable (fun u => weight u * ‖v u‖)
          MeasureTheory.volume s₀ s := by
        apply ContinuousOn.intervalIntegrable
        simpa only [Set.uIcc_of_le hsle, Pi.mul_apply] using
          hweight_cont.mul hv.norm.continuousOn
      have hweightIntg : IntervalIntegrable weight MeasureTheory.volume s₀ s := by
        apply ContinuousOn.intervalIntegrable
        simpa only [Set.uIcc_of_le hsle] using hweight_cont
      have hrewrite : (∫ u in s₀..s, weight u * (‖v u‖ - r)) =
          (∫ u in s₀..s, weight u * ‖v u‖) - r * (∫ u in s₀..s, weight u) := by
        simp_rw [mul_sub]
        rw [intervalIntegral.integral_sub hnormIntg (hweightIntg.mul_const r),
          intervalIntegral.integral_mul_const]
        ring
      rw [hrewrite, hmass]
      nlinarith [hnorm]
    exact hsub.trans (add_le_add
      (mul_le_mul_of_nonneg_left
        (by
          change ‖v s₀‖ - r ≤ D (v s₀)
          dsimp [D]
          rw [infDist_frictionBall_eq r hr]
          exact le_max_left _ _)
        (Real.rpow_nonneg hs₀.le _)) hDInt)

/-- Theorem 5.1 (corrected): time scaling and averaging of a DRYGRAD
trajectory produce DRYSTARDE and the two accelerated residual estimates.

The paper states `1 < α`.  Its averaging formula contains an initial atom of
mass `(s₀ / s)^(α-1)` and a power-weighted integral; the claimed
`o(1 / s)` distance estimate for `w` therefore requires `2 < α` in
general. -/
theorem theorem_5_1 {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    {s₀ r α : ℝ} (hr : 0 < r) (hs₀ : 0 < s₀) (hα : 2 < α)
    (f : H → ℝ) (hf : ContDiff ℝ 2 f)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hf_lower : ∃ m : ℝ, ∀ x : H, m ≤ f x)
    (hgradient_lip : LocallyLipschitz (gradient f))
    (fstar : H → ℝ) (hfstar : ContDiff ℝ 2 fstar)
    (hlegendre : ∀ x : H, gradient fstar (gradient f x) = x)
    (z : ℝ → H) (hz : Differentiable ℝ z)
    (hsol : IsDrygradTrajectory r f z (s₀ ^ 2 / (2 * (α - 1))))
    (w : ℝ → H) (hw : ContDiff ℝ 2 w)
    (haverage : IsWeightedAverageOn
      (fun s : ℝ => s ^ 2 / (2 * (α - 1)))
      (fun s : ℝ => s / (α - 1))
      w (fun s => gradient f (z (s ^ 2 / (2 * (α - 1))))) (deriv w) s₀) :
    IsDryStarDualInertial r hr α s₀ fstar w ∧
      Tendsto
        (fun s : ℝ => s * Metric.infDist
          (w s + (s / (α - 1)) • deriv w s) (frictionBall r))
        atTop (nhds 0) ∧
      Tendsto (fun s : ℝ => s * Metric.infDist (w s) (frictionBall r))
        atTop (nhds 0) := by
  let τ : ℝ → ℝ := fun s => s ^ 2 / (2 * (α - 1))
  let dτ : ℝ → ℝ := fun s => s / (α - 1)
  let g : ℝ → H := fun t => gradient f (z t)
  let v : ℝ → H := fun s => g (τ s)
  change IsWeightedAverageOn τ dτ w v (deriv w) s₀ at haverage
  have hα1 : 1 < α := lt_trans one_lt_two hα
  have hαsub : 0 < α - 1 := sub_pos.mpr hα1
  have hτderiv : ∀ s : ℝ, HasDerivAt τ (dτ s) s := by
    intro s
    dsimp [τ, dτ]
    convert ((hasDerivAt_pow 2 s).div_const (2 * (α - 1))) using 1
    field_simp [ne_of_gt hαsub]
    ring
  have hτmono : StrictMonoOn τ (Set.Ici s₀) :=
    (quadraticTimeScale_isIncreasingC1TimeScaleOn hα1 hs₀).1
  have hτmem : ∀ s ∈ Set.Ici s₀, τ s ∈ Set.Ici (τ s₀) := by
    intro s hs
    exact hτmono.monotoneOn (Set.mem_Ici.mpr le_rfl) hs hs
  obtain ⟨hflow, _hanti, hgrate, _hbregman⟩ :=
    theorem_3_2 hr f z hf hconvex hf_lower hgradient_lip hz hsol
  let p : ℝ → H := Classical.choose hflow
  have hpflow : ∀ t ∈ Set.Ici (τ s₀),
      p t ∈ frictionBallProjector r (g t) ∧ HasDerivAt z (p t - g t) t := by
    simpa [p, g, τ] using Classical.choose_spec hflow
  have hfderiv_contdiff : ContDiff ℝ 1 (fderiv ℝ f) := by
    exact (contDiff_succ_iff_fderiv.mp
      (show ContDiff ℝ (1 + 1) f by simpa using hf)).2.2
  have hgradient_diff : Differentiable ℝ (gradient f) := by
    have hgradient_contdiff : ContDiff ℝ 1 (gradient f) := by
      simpa [gradient, Function.comp_def] using
        (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hfderiv_contdiff
    exact hgradient_contdiff.differentiable (by norm_num)
  have hfstar_fderiv_contdiff : ContDiff ℝ 1 (fderiv ℝ fstar) := by
    exact (contDiff_succ_iff_fderiv.mp
      (show ContDiff ℝ (1 + 1) fstar by simpa using hfstar)).2.2
  have hgradient_fstar_diff : Differentiable ℝ (gradient fstar) := by
    have hgradient_fstar_contdiff : ContDiff ℝ 1 (gradient fstar) := by
      simpa [gradient, Function.comp_def] using
        (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hfstar_fderiv_contdiff
    exact hgradient_fstar_contdiff.differentiable (by norm_num)
  have hv_diff : Differentiable ℝ v := by
    have hτdiff : Differentiable ℝ τ := fun s => (hτderiv s).differentiableAt
    exact hgradient_diff.comp (hz.comp hτdiff)
  have hw_diff : Differentiable ℝ w := hw.differentiable (by norm_num)
  have hdw_diff : Differentiable ℝ (deriv w) := by
    have h := (contDiff_nat_iff_iteratedDeriv.mp hw).2 1 (by norm_num)
    simpa [iteratedDeriv_one] using h
  have hpoint : ∀ s ∈ Set.Ici s₀,
      w s + (s / (α - 1)) • deriv w s = v s := by
    intro s hs
    exact scaled_point_eq hs₀ hα1 hs (haverage.2.2 s hs).2
  have hpoint_deriv : ∀ s ∈ Set.Ici s₀,
      HasDerivAt v
        ((s / (α - 1)) •
          (deriv (deriv w) s + (α / s) • deriv w s)) s := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
    let y : ℝ → H := fun u => w u + (u / (α - 1)) • deriv w u
    have hy : HasDerivAt y
        (deriv w s + (1 / (α - 1)) • deriv w s +
          (s / (α - 1)) • deriv (deriv w) s) s := by
      dsimp [y]
      convert (hw_diff s).hasDerivAt.add
        (((hasDerivAt_id s).div_const (α - 1)).smul
          (hdw_diff s).hasDerivAt) using 1
      all_goals (simp; module)
    have hy_as_v : HasDerivWithinAt v
        (deriv w s + (1 / (α - 1)) • deriv w s +
          (s / (α - 1)) • deriv (deriv w) s) (Set.Ici s₀) s := by
      apply hy.hasDerivWithinAt.congr
      · intro u hu
        exact (hpoint u hu).symm
      · exact (hpoint s hs).symm
    have heq := (uniqueDiffOn_Ici s₀ s hs).eq_deriv (Set.Ici s₀)
      (hv_diff s).hasDerivAt.hasDerivWithinAt hy_as_v
    have hformula :
        deriv w s + (1 / (α - 1)) • deriv w s +
            (s / (α - 1)) • deriv (deriv w) s =
          (s / (α - 1)) •
            (deriv (deriv w) s + (α / s) • deriv w s) := by
      have hsne : s ≠ 0 := ne_of_gt hspos
      have hane : α - 1 ≠ 0 := ne_of_gt hαsub
      have hcoeff : 1 + 1 / (α - 1) = (s / (α - 1)) * (α / s) := by
        field_simp [hsne, hane]
        ring
      rw [smul_add, smul_smul, ← hcoeff]
      module
    have hvbase := (hv_diff s).hasDerivAt
    rw [heq, hformula] at hvbase
    exact hvbase
  have hstar_point : ∀ t : ℝ, gradient fstar (g t) = z t := by
    intro t
    exact hlegendre (z t)
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
    have hcpos : 0 < dτ s := div_pos hspos hαsub
    have hcne : dτ s ≠ 0 := ne_of_gt hcpos
    have hpt := hpflow (τ s) (hτmem s hs)
    have hdual_time : HasDerivAt (fun t => gradient fstar (g t))
        (p (τ s) - g (τ s)) (τ s) := by
      convert hpt.2 using 1
      · funext t
        exact hstar_point t
    have hdual_scaled : HasDerivAt (fun u => gradient fstar (v u))
        (dτ s • (p (τ s) - v s)) s := by
      simpa [v, Function.comp_def] using hdual_time.scomp s (hτderiv s)
    have hdual_chain : HasDerivAt (fun u => gradient fstar (v u))
        (fderiv ℝ (gradient fstar) (v s)
          (dτ s • (deriv (deriv w) s + (α / s) • deriv w s))) s := by
      exact (hgradient_fstar_diff (v s)).hasFDerivAt.comp_hasDerivAt s
        (hpoint_deriv s hs)
    have heq := hdual_chain.unique hdual_scaled
    rw [map_smul] at heq
    have hmain : fderiv ℝ (gradient fstar) (v s)
        (deriv (deriv w) s + (α / s) • deriv w s) = p (τ s) - v s :=
      smul_right_injective H hcne heq
    have hp : p (τ s) = frictionBallProjection r hr (v s) := by
      have hmem : p (τ s) ∈ frictionBallProjector r (v s) := by
        simpa [v] using hpt.1
      exact (frictionBall_isChebyshev hr.le (v s)).choose_spec.2 _ hmem
    rw [hpoint s hs, hmain, hp]
    abel
  · have hvrate : Tendsto
        (fun s : ℝ => s * Metric.infDist (v s) (frictionBall r))
        atTop (nhds 0) := by
      simpa [v, g, τ] using timeScaled_distance_rate hα1 g (by simpa [g] using hgrate)
    apply hvrate.congr'
    filter_upwards [eventually_ge_atTop s₀] with s hs
    rw [hpoint s hs]
  · have hv_cont : Continuous v := hv_diff.continuous
    have hformula := weightedAverage_power_formula hs₀ hα1 v w hv_cont hw_diff
      (fun s hs => (haverage.2.2 s hs).2)
    have hdist_bound := weightedAverage_distance_bound hr hs₀ hα1 v w hv_cont
      haverage.2.1 hformula
    let D : H → ℝ := fun x => Metric.infDist x (frictionBall r)
    let a : ℝ → ℝ := fun u =>
      max u s₀ * D (v (max u s₀)) + (max u s₀)⁻¹
    have hmaxpos : ∀ u : ℝ, 0 < max u s₀ := by
      intro u
      exact lt_of_lt_of_le hs₀ (le_max_right _ _)
    have ha_cont : Continuous a := by
      have hmax : Continuous (fun u : ℝ => max u s₀) := continuous_id.max continuous_const
      have hDv : Continuous (fun u : ℝ => D (v u)) := by
        dsimp [D]
        simp_rw [infDist_frictionBall_eq r hr]
        exact ((hv_cont.norm.sub continuous_const).max continuous_const)
      exact (hmax.mul (hDv.comp hmax)).add
        (hmax.inv₀ (fun u => ne_of_gt (hmaxpos u)))
    have ha_pos : ∀ u ∈ Set.Ici s₀, 0 < a u := by
      intro u hu
      dsimp [a]
      rw [show max u s₀ = u from max_eq_left hu]
      exact add_pos_of_nonneg_of_pos
        (mul_nonneg (le_trans hs₀.le hu) Metric.infDist_nonneg)
        (inv_pos.mpr (lt_of_lt_of_le hs₀ hu))
    have hvrate : Tendsto (fun s : ℝ => s * D (v s)) atTop (nhds 0) := by
      simpa [D, v, g, τ] using
        timeScaled_distance_rate hα1 g (by simpa [g] using hgrate)
    have ha_zero : Tendsto a atTop (nhds 0) := by
      have hbase : Tendsto (fun u : ℝ => u * D (v u) + u⁻¹) atTop (nhds 0) := by
        simpa using hvrate.add tendsto_inv_atTop_zero
      apply hbase.congr'
      filter_upwards [eventually_ge_atTop s₀] with u hu
      simp only [a, max_eq_left hu]
    have ha_int : ∀ t : ℝ, IntervalIntegrable
        (fun u : ℝ => u ^ ((α - 1) - 2) * a u)
        MeasureTheory.volume s₀ t := by
      intro t
      exact (intervalIntegral.intervalIntegrable_rpow'
        (a := s₀) (b := t) (by linarith : -1 < (α - 1) - 2)).mul_continuousOn
          ha_cont.continuousOn
    have hweighted := lemma_A_1 (s₀ := s₀) (α := α - 1) (by linarith) a
      ha_pos ha_zero hs₀.le ha_int
    let C : ℝ := s₀ ^ (α - 1) * D (v s₀)
    let J : ℝ → ℝ := fun s =>
      (s ^ ((α - 1) - 1))⁻¹ *
        ∫ u in s₀..s, u ^ ((α - 1) - 2) * a u
    have hJ : Tendsto J atTop (nhds 0) := by
      simpa [J] using hweighted
    have hC : Tendsto (fun s : ℝ => C * (s ^ (α - 2))⁻¹) atTop (nhds 0) := by
      have hp := tendsto_rpow_neg_atTop (by linarith : 0 < α - 2)
      have hp' : Tendsto (fun s : ℝ => (s ^ (α - 2))⁻¹) atTop (nhds 0) := by
        apply hp.congr'
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with s hs
        rw [Real.rpow_neg hs.le]
      simpa using hp'.const_mul C
    have hupper : Tendsto (fun s : ℝ =>
        C * (s ^ (α - 2))⁻¹ + (α - 1) * J s) atTop (nhds 0) := by
      simpa using hC.add (hJ.const_mul (α - 1))
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop (0 : ℝ)] with s hs
      exact mul_nonneg hs Metric.infDist_nonneg
    · filter_upwards [eventually_ge_atTop s₀] with s hs
      have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
      have hpowpos : 0 < s ^ (α - 2) := Real.rpow_pos_of_pos hspos _
      have hscale : (s ^ (α - 2))⁻¹ * s ^ (α - 1) = s := by
        have hrpow : s ^ (α - 1) = s ^ (α - 2) * s := by
          calc
            s ^ (α - 1) = s ^ ((α - 2) + 1) := by ring_nf
            _ = s ^ (α - 2) * s ^ (1 : ℝ) := Real.rpow_add hspos _ _
            _ = s ^ (α - 2) * s := by rw [Real.rpow_one]
        rw [hrpow, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpowpos), one_mul]
      have hAK : (∫ u in s₀..s, u ^ (α - 2) * D (v u)) ≤
          ∫ u in s₀..s, u ^ ((α - 1) - 2) * a u := by
        have hDcontinuous : Continuous (fun u : ℝ => D (v u)) := by
          dsimp [D]
          simp_rw [infDist_frictionBall_eq r hr]
          exact ((hv_cont.norm.sub continuous_const).max continuous_const)
        have hleft : IntervalIntegrable (fun u : ℝ => u ^ (α - 2) * D (v u))
            MeasureTheory.volume s₀ s := by
          apply ContinuousOn.intervalIntegrable
          intro u hu
          have hu' : u ∈ Set.Icc s₀ s := by
            simpa only [Set.uIcc_of_le hs] using hu
          have hupos : 0 < u := lt_of_lt_of_le hs₀ hu'.1
          exact ((Real.continuousAt_rpow_const u (α - 2)
            (Or.inl (ne_of_gt hupos))).mul
              hDcontinuous.continuousAt).continuousWithinAt
        apply intervalIntegral.integral_mono_on hs hleft (ha_int s)
        intro u hu
        have hupos : 0 < u := lt_of_lt_of_le hs₀ hu.1
        have hmax : max u s₀ = u := max_eq_left hu.1
        have hrpow : u ^ (α - 2) = u ^ ((α - 1) - 2) * u := by
          calc
            u ^ (α - 2) = u ^ (((α - 1) - 2) + 1) := by ring_nf
            _ = u ^ ((α - 1) - 2) * u ^ (1 : ℝ) := Real.rpow_add hupos _ _
            _ = u ^ ((α - 1) - 2) * u := by rw [Real.rpow_one]
        rw [hrpow]
        dsimp [a]
        rw [hmax]
        have hnonneg : 0 ≤ u ^ ((α - 1) - 2) := Real.rpow_nonneg hupos.le _
        have hinv : 0 ≤ u⁻¹ := (inv_pos.mpr hupos).le
        nlinarith [Metric.infDist_nonneg (x := v u) (s := frictionBall r)]
      have hb := hdist_bound s hs
      have hbscaled := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hpowpos.le)
      have hlhs : s * D (w s) =
          (s ^ (α - 2))⁻¹ * (s ^ (α - 1) * D (w s)) := by
        rw [← mul_assoc, hscale]
      have hint : (∫ u in s₀..s, ((α - 1) * u ^ (α - 2)) * D (v u)) =
          (α - 1) * ∫ u in s₀..s, u ^ (α - 2) * D (v u) := by
        rw [show (fun u : ℝ => ((α - 1) * u ^ (α - 2)) * D (v u)) =
            fun u => (α - 1) * (u ^ (α - 2) * D (v u)) by
          funext u
          ring]
        exact intervalIntegral.integral_const_mul _ _
      change s * D (w s) ≤ C * (s ^ (α - 2))⁻¹ + (α - 1) * J s
      rw [hlhs]
      calc
        (s ^ (α - 2))⁻¹ * (s ^ (α - 1) * D (w s))
            ≤ (s ^ (α - 2))⁻¹ *
                (C + ∫ u in s₀..s, ((α - 1) * u ^ (α - 2)) * D (v u)) := by
              simpa [C, D] using hbscaled
        _ = C * (s ^ (α - 2))⁻¹ + (α - 1) *
              ((s ^ (α - 2))⁻¹ * ∫ u in s₀..s, u ^ (α - 2) * D (v u)) := by
              rw [hint]
              ring
        _ ≤ C * (s ^ (α - 2))⁻¹ + (α - 1) *
              ((s ^ (α - 2))⁻¹ *
                ∫ u in s₀..s, u ^ ((α - 1) - 2) * a u) := by
              gcongr
        _ = C * (s ^ (α - 2))⁻¹ + (α - 1) * J s := by
              simp only [J]
              congr 3
              ring_nf
    · exact hupper

end AttouchAdlyDryFrictionDynamics2023
