import Mathlib

namespace Alvarez2000

open MeasureTheory

private theorem damped_le_causal_exp_convolution (omega g : ℝ → ℝ) (gamma : ℝ)
    (hDiff : ContDiffOn ℝ 1 omega (Set.Ici 0))
    (hineq : ∀ t ∈ Set.Ici 0, deriv omega t + gamma * omega t ≤ |g t|)
    (hg : IntegrableOn g (Set.Ici 0)) (t : ℝ) (ht : t ∈ Set.Ici 0) :
    omega t ≤ Real.exp (-gamma * t) * omega 0 +
      ∫ s in 0..t, Real.exp (-gamma * (t - s)) * |g s| := by
  have ht0 : 0 ≤ t := ht
  have hG : IntegrableOn (fun s : ℝ => |g s|) (Set.Ici 0) := hg.abs
  have hGlocal : IntegrableOn (fun s : ℝ => |g s|) (Set.Icc 0 t) :=
    hG.mono_set Set.Icc_subset_Ici_self
  have hweighted : IntegrableOn (fun s : ℝ =>
      Real.exp (gamma * s) * |g s|) (Set.Icc 0 t) :=
    IntegrableOn.continuousOn_mul
      (Real.continuous_exp.comp (continuous_const.mul continuous_id) |>.continuousOn)
      hGlocal isCompact_Icc
  have hweighted_interval : IntervalIntegrable (fun s : ℝ =>
      Real.exp (gamma * s) * |g s|) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht0).mpr hweighted
  rcases ht0.eq_or_lt with rfl | ht0
  · simp
  let F : ℝ → ℝ := fun x => Real.exp (gamma * x) * omega x
  have hF : ContDiffOn ℝ 1 F (Set.Icc 0 t) := by
    dsimp [F]
    exact ((Real.contDiff_exp.comp (contDiff_const.mul contDiff_id)).contDiffOn).mul
      (hDiff.mono Set.Icc_subset_Ici_self)
  have hderivInt : IntervalIntegrable (deriv F) volume 0 t := by
    have hcont :=
      (hF.derivWithin (m := 0) (uniqueDiffOn_Icc ht0) (by simp)).continuousOn
    apply (hcont.intervalIntegrable_of_Icc ht0.le).congr_ae
    simp only [ht0.le, Set.uIoc_of_le]
    rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with x hx
    exact derivWithin_of_mem_nhds (Icc_mem_nhds hx.1 hx.2)
  have hderiv : ∀ x ∈ Set.Ioo 0 t,
      deriv F x ≤ Real.exp (gamma * x) * |g x| := by
    intro x hx
    have hexp : HasDerivAt (fun y : ℝ => Real.exp (gamma * y))
        (gamma * Real.exp (gamma * x)) x := by
      convert (Real.hasDerivAt_exp (gamma * x)).comp x
        ((hasDerivAt_const (c := gamma) (x := x)).mul (hasDerivAt_id x)) using 1
      all_goals ring
    have homega : HasDerivAt omega (deriv omega x) x :=
      (hDiff.contDiffAt (Ici_mem_nhds hx.1)).differentiableAt (by norm_num) |>.hasDerivAt
    have hFderiv : deriv F x = Real.exp (gamma * x) *
        (deriv omega x + gamma * omega x) := by
      convert (hexp.mul homega).deriv using 1
      all_goals
        dsimp [F]
        ring
    rw [hFderiv]
    exact mul_le_mul_of_nonneg_left (hineq x (le_of_lt hx.1))
      (le_of_lt (Real.exp_pos _))
  have hFTC : F t - F 0 = ∫ x in 0..t, deriv F x := by
    simpa using (intervalIntegral.integral_deriv_of_contDiffOn_Icc hF ht0.le).symm
  have hIntegrated : F t - F 0 ≤ ∫ x in 0..t, Real.exp (gamma * x) * |g x| := by
    rw [hFTC]
    exact intervalIntegral.integral_mono_on_of_le_Ioo ht0.le hderivInt hweighted_interval hderiv
  have hmul := mul_le_mul_of_nonneg_left hIntegrated
    (le_of_lt (Real.exp_pos (-gamma * t)))
  rw [← intervalIntegral.integral_const_mul] at hmul
  have hexp : ∀ s : ℝ, Real.exp (-gamma * t) * Real.exp (gamma * s) =
      Real.exp (-gamma * (t - s)) := by
    intro s
    rw [← Real.exp_add]
    congr 1
    ring
  dsimp [F] at hmul
  change Real.exp (-gamma * t) *
      (Real.exp (gamma * t) * omega t - Real.exp (gamma * 0) * omega 0) ≤ _ at hmul
  have hcancel : Real.exp (-gamma * t) * Real.exp (gamma * t) = 1 := by
    rw [← Real.exp_add]
    norm_num
  rw [mul_sub] at hmul
  rw [← mul_assoc, hcancel] at hmul
  simp only [one_mul, mul_zero, Real.exp_zero] at hmul
  have hkernel_eq :
      (∫ x in 0..t, Real.exp (-gamma * t) *
        (Real.exp (gamma * x) * |g x|)) =
        ∫ x in 0..t, Real.exp (-gamma * (t - x)) * |g x| := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards with x hx
    rw [← mul_assoc, hexp x]
  rw [hkernel_eq] at hmul
  linarith

private theorem causal_exp_convolution_integrable (g : ℝ → ℝ) (gamma : ℝ)
    (hgamma : 0 < gamma) (hg : IntegrableOn g (Set.Ici 0)) :
    IntegrableOn (fun t : ℝ =>
      ∫ s in 0..t, Real.exp (-gamma * (t - s)) * |g s|) (Set.Ici 0) := by
  have hG : IntegrableOn (fun s : ℝ => |g s|) (Set.Ici 0) := hg.abs
  have hkernel : IntegrableOn (fun t : ℝ => Real.exp ((-gamma) * t)) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_exp_mul_Ioi (by linarith) 0
  have hG' : IntegrableOn (fun s : ℝ => |g s|) (Set.Ioi 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mp hG
  have hkernel' : IntegrableOn (fun s : ℝ => Real.exp ((-gamma) * s)) (Set.Ioi 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mp hkernel
  have hconv := integrable_posConvolution hG' hkernel'
    (ContinuousLinearMap.mul ℝ ℝ)
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply hconv.integrableOn.congr
  filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with t ht
  rw [posConvolution]
  simp only [Set.indicator_of_mem ht]
  change (∫ s in 0..t, |g s| * Real.exp ((-gamma) * (t - s))) = _
  simp [mul_comm]

/-- Lemma 2.3: the positive part of a damped subsolution with integrable forcing is integrable. -/
theorem positive_part_integrable_of_damped_inequality (omega g : ℝ → ℝ) (gamma : ℝ)
    (hDiff : ContDiffOn ℝ 1 omega (Set.Ici 0)) (hgamma : 0 < gamma)
    (hIneq : ∀ t ∈ Set.Ici 0, deriv omega t + gamma * omega t ≤ g t)
    (hg : IntegrableOn g (Set.Ici 0)) :
    IntegrableOn (fun t => max (omega t) 0) (Set.Ici 0) := by
  have hG : IntegrableOn (fun t : ℝ => |g t|) (Set.Ici 0) := hg.abs
  have hineq_abs : ∀ t ∈ Set.Ici 0, deriv omega t + gamma * omega t ≤ |g t| :=
    fun t ht => (hIneq t ht).trans (le_abs_self (g t))
  have hcomparison := damped_le_causal_exp_convolution omega g gamma hDiff hineq_abs hg
  have hconvolution := causal_exp_convolution_integrable g gamma hgamma hg
  have hkernel : IntegrableOn (fun t : ℝ => Real.exp ((-gamma) * t)) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]
    exact integrableOn_exp_mul_Ioi (by linarith) 0
  have hinitial : IntegrableOn
      (fun t : ℝ => Real.exp (-gamma * t) * max (omega 0) 0) (Set.Ici 0) := by
    simpa only [neg_mul] using hkernel.mul_const (max (omega 0) 0)
  have hmajorant : IntegrableOn (fun t : ℝ =>
      Real.exp (-gamma * t) * max (omega 0) 0 +
        ∫ s in 0..t, Real.exp (-gamma * (t - s)) * |g s|) (Set.Ici 0) :=
    hinitial.add hconvolution
  have hconvolution_nonneg : ∀ t ∈ Set.Ici 0,
      0 ≤ ∫ s in 0..t, Real.exp (-gamma * (t - s)) * |g s| := by
    intro t ht
    exact intervalIntegral.integral_nonneg_of_forall ht fun s =>
      mul_nonneg (le_of_lt (Real.exp_pos _)) (abs_nonneg _)
  have hpointwise : ∀ t ∈ Set.Ici 0,
      max (omega t) 0 ≤ Real.exp (-gamma * t) * max (omega 0) 0 +
        ∫ s in 0..t, Real.exp (-gamma * (t - s)) * |g s| := by
    intro t ht
    apply max_le
    · calc
        omega t ≤ Real.exp (-gamma * t) * omega 0 +
            ∫ s in 0..t, Real.exp (-gamma * (t - s)) * |g s| := hcomparison t ht
        _ ≤ Real.exp (-gamma * t) * max (omega 0) 0 +
            ∫ s in 0..t, Real.exp (-gamma * (t - s)) * |g s| :=
          add_le_add
            (mul_le_mul_of_nonneg_left (le_max_left _ _)
              (le_of_lt (Real.exp_pos _))) le_rfl
    · exact add_nonneg
        (mul_nonneg (le_of_lt (Real.exp_pos _)) (le_max_right _ _))
        (hconvolution_nonneg t ht)
  have htarget_measurable : AEStronglyMeasurable (fun t : ℝ => max (omega t) 0)
      (volume.restrict (Set.Ici 0)) := by
    apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ici
    intro t ht
    exact (hDiff t ht).continuousWithinAt.max continuousWithinAt_const
  have hnorm_bound : ∀ᵐ t ∂(volume.restrict (Set.Ici 0)),
      ‖max (omega t) 0‖ ≤ Real.exp (-gamma * t) * max (omega 0) 0 +
  ∫ s in 0..t, Real.exp (-gamma * (t - s)) * |g s| := by
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ici] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    exact hpointwise t ht
  exact hmajorant.mono' htarget_measurable hnorm_bound

end Alvarez2000
