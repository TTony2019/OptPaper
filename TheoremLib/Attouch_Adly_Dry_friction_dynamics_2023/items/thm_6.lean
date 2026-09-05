import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.thm_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.thm_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.thm_5
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.lem_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_3
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_4
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_thm_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_thm_3

namespace AttouchAdlyDryFrictionDynamics2023

/-! The following interfaces are the analytic transfer steps in the proof of
Theorem 4.2.  They correspond respectively to (4.20)--(4.22), (4.26)--(4.29),
and the final ergodic-limit argument in the paper. -/

theorem time_scale_velocity_transfer
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {s₀ α : ℝ}
    (hα : 1 < α) (hs₀ : 0 < s₀) (z y : ℝ → H)
    (hz : ContDiff ℝ 2 z)
    (hy : y = timeScaledTrajectory z (fun s => s ^ 2 / (2 * (α - 1))))
    (hzrate : Filter.Tendsto (fun t : ℝ => t * ‖deriv z t‖)
      Filter.atTop (nhds 0))
    (hzint : MeasureTheory.IntegrableOn (fun t : ℝ => ‖deriv z t‖)
      (Set.Ici (s₀ ^ 2 / (2 * (α - 1))))) :
    ∃ dy : ℝ → H,
      (∀ s ∈ Set.Ici s₀, HasDerivAt y (dy s) s) ∧
      Filter.Tendsto (fun s : ℝ => s * ‖dy s‖) Filter.atTop (nhds 0) ∧
      MeasureTheory.IntegrableOn (fun s : ℝ => ‖dy s‖) (Set.Ici s₀) := by
  let τ : ℝ → ℝ := fun s => s ^ 2 / (2 * (α - 1))
  let dτ : ℝ → ℝ := fun s => s / (α - 1)
  let dy : ℝ → H := fun s => dτ s • deriv z (τ s)
  have hα1 : 0 < α - 1 := sub_pos.mpr hα
  have hτderiv : ∀ s : ℝ, HasDerivAt τ (dτ s) s := by
    intro s
    dsimp [τ, dτ]
    convert ((hasDerivAt_pow 2 s).div_const (2 * (α - 1))) using 1 <;>
      field_simp [ne_of_gt hα1] <;> ring
  have hτmono : StrictMonoOn τ (Set.Ici s₀) :=
    (quadraticTimeScale_isIncreasingC1TimeScaleOn hα hs₀).1
  have hτdomain : ∀ s ∈ Set.Ici s₀, τ s ∈ Set.Ici (τ s₀) := by
    intro s hs
    exact hτmono.monotoneOn (Set.mem_Ici.mpr le_rfl) hs hs
  have hdy : ∀ s ∈ Set.Ici s₀, HasDerivAt (timeScaledTrajectory z τ) (dy s) s := by
    intro s hs
    dsimp [timeScaledTrajectory, dy]
    simpa [Function.comp_def] using ((hz.differentiable (by norm_num) (τ s)).hasDerivAt.scomp s (hτderiv s))
  have hτtop : Filter.Tendsto τ Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 ?_
    intro b
    filter_upwards [Filter.eventually_atTop.2
      ⟨max 1 (2 * (α - 1) * b), fun s hs => hs⟩] with s hs
    have hs1 : 1 ≤ s := le_trans (le_max_left _ _) hs
    have hsq : s ≤ s ^ 2 := by nlinarith
    have hsb : 2 * (α - 1) * b ≤ s := le_trans (le_max_right _ _) hs
    apply (le_div_iff₀ (mul_pos (by norm_num) hα1)).2
    nlinarith
  have hrate : Filter.Tendsto (fun s => τ s * ‖deriv z (τ s)‖)
      Filter.atTop (nhds 0) := by
    simpa [Function.comp_def] using hzrate.comp hτtop
  have hhydrate : Filter.Tendsto (fun s => s * ‖dy s‖)
      Filter.atTop (nhds 0) := by
    have heq : ∀ᶠ s : ℝ in Filter.atTop,
        s * ‖dy s‖ = (2 : ℝ) * (τ s * ‖deriv z (τ s)‖) := by
      filter_upwards [Filter.eventually_atTop.2
        ⟨s₀, fun s hs => hs⟩] with s hs
      have hspos : 0 ≤ s := le_trans (le_of_lt hs₀) hs
      dsimp [dy, dτ, τ]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hspos hα1.le)]
      field_simp [ne_of_gt hα1]
    have hmul := hrate.const_mul (2 : ℝ)
    have hmul' : Filter.Tendsto (fun s => (2 : ℝ) *
        (τ s * ‖deriv z (τ s)‖)) Filter.atTop (nhds 0) := by simpa using hmul
    exact Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) hmul'
  refine ⟨dy, ?_, hhydrate, ?_⟩
  · intro s hs
    rw [hy]
    exact hdy s hs
  have hτmono' : MonotoneOn τ (Set.Ioi s₀) :=
    hτmono.monotoneOn.mono Set.Ioi_subset_Ici_self
  have himage : τ '' Set.Ioi s₀ ⊆ Set.Ici (τ s₀) := by
    rintro t ⟨s, hs, rfl⟩
    exact hτmono.monotoneOn (Set.mem_Ici.mpr le_rfl)
      (Set.Ioi_subset_Ici_self hs) (le_of_lt (Set.mem_Ioi.mp hs))
  have hgint : MeasureTheory.IntegrableOn (fun t : ℝ => ‖deriv z t‖)
      (τ '' Set.Ioi s₀) := hzint.mono_set himage
  have hderivWithin : ∀ s ∈ Set.Ioi s₀,
      HasDerivWithinAt τ (dτ s) (Set.Ioi s₀) s := by
    intro s hs
    exact (hτderiv s).hasDerivWithinAt
  have hcompint : MeasureTheory.IntegrableOn
      (fun s : ℝ => dτ s * ‖deriv z (τ s)‖) (Set.Ioi s₀) := by
    simpa [smul_eq_mul] using
      (MeasureTheory.integrableOn_image_iff_integrableOn_deriv_smul_of_monotoneOn
        measurableSet_Ioi hderivWithin hτmono' (fun t : ℝ => ‖deriv z t‖)).mp hgint
  have hnormint : MeasureTheory.IntegrableOn (fun s : ℝ => ‖dy s‖)
      (Set.Ioi s₀) := by
    apply hcompint.congr_fun
    · intro s hs
      dsimp [dy, dτ]
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg]
      exact div_nonneg (le_of_lt (lt_trans hs₀ (Set.mem_Ioi.mp hs))) hα1.le
    · exact measurableSet_Ioi
  exact (integrableOn_Ici_iff_integrableOn_Ioi).2 hnormint

theorem weighted_average_velocity_transfer
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H] {s₀ α : ℝ}
    (hα : 1 < α) (hs₀ : 0 < s₀) (x y dx dy : ℝ → H)
    (haverage : IsWeightedAverageOn
      (fun s : ℝ => s ^ 2 / (2 * (α - 1)))
      (fun s : ℝ => s / (α - 1)) x y dx s₀)
    (hdy : ∀ s ∈ Set.Ici s₀, HasDerivAt y (dy s) s)
    (hydrate : Filter.Tendsto (fun s : ℝ => s * ‖dy s‖)
      Filter.atTop (nhds 0))
    (hydyint : MeasureTheory.IntegrableOn (fun s : ℝ => ‖dy s‖)
      (Set.Ici s₀)) :
    Filter.Tendsto (fun s : ℝ => s * ‖dx s‖) Filter.atTop (nhds 0) ∧
      MeasureTheory.IntegrableOn (fun s : ℝ => ‖dx s‖) (Set.Ici s₀) := by
  exact weighted_average_velocity_transfer_external hα hs₀ x y dx dy haverage hdy hydrate hydyint

theorem weighted_average_limit_transfer
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H] {s₀ α : ℝ}
    (hα : 1 < α) (hs₀ : 0 < s₀) (x y dx : ℝ → H) (xLimit : H)
    (haverage : IsWeightedAverageOn
      (fun s : ℝ => s ^ 2 / (2 * (α - 1)))
      (fun s : ℝ => s / (α - 1)) x y dx s₀)
    (hy_limit : Filter.Tendsto y Filter.atTop (nhds xLimit)) :
    Filter.Tendsto x Filter.atTop (nhds xLimit) := by
  exact weighted_average_limit_transfer_external hα hs₀ x y dx xLimit haverage hy_limit

/-! Theorem 4.2.  The hypotheses and the conclusion follow the statement in
the paper; the three transfer lemmas above isolate the change-of-time and
weighted-average calculations used in its proof. -/
theorem theorem_4_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {s₀ r α : ℝ} (hr : 0 < r) (hα : 1 < α) (hs₀ : 0 < s₀)
    (f : H → ℝ) (hf : ContDiff ℝ 2 f)
    (x p z : ℝ → H) (hx : ContDiff ℝ 2 x) (hz : ContDiff ℝ 2 z)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hgradient_lip_on_bounded : ∀ R : ℝ, ∃ L : NNReal,
      LipschitzOnWith L (gradient f) (Metric.closedBall 0 R))
    (hmin : ∃ xstar : H, ∀ u : H, f xstar ≤ f u)
    (hsolution : IsDryStarTrajectory r α s₀ f x p)
    (hsol : IsDrygradTrajectory r f z (s₀ ^ 2 / (2 * (α - 1))))
    (hbridge_initial : x s₀ = z (s₀ ^ 2 / (2 * (α - 1))))
    (hbridge_relation : ∀ s ∈ Set.Ici s₀,
      z (s ^ 2 / (2 * (α - 1))) =
        x s + (s / (α - 1)) • deriv x s)
    (hinitial : r < ‖gradient f (z (s₀ ^ 2 / (2 * (α - 1))))‖) :
    Filter.Tendsto (fun s : ℝ => s * ‖deriv x s‖) Filter.atTop (nhds 0) ∧
      MeasureTheory.IntegrableOn (fun s => ‖deriv x s‖) (Set.Ici s₀) ∧
      ∃ xLimit, Filter.Tendsto x Filter.atTop (nhds xLimit) ∧
        ‖gradient f xLimit‖ = r := by
  have hf₁ : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hz_diff : Differentiable ℝ z := hz.differentiable (by norm_num)
  have hgradient_lip : LocallyLipschitz (gradient f) := by
    intro u
    obtain ⟨L, hL⟩ := hgradient_lip_on_bounded (‖u‖ + 1)
    refine ⟨L, Metric.ball u 1, Metric.ball_mem_nhds u zero_lt_one, hL.mono ?_⟩
    intro v hv
    have hvdist : dist v u < 1 := by simpa [Metric.mem_ball] using hv
    have hvdist' : ‖v - u‖ < 1 := by simpa [dist_eq_norm] using hvdist
    have hvnorm : ‖v‖ ≤ ‖u‖ + 1 := by
      have htri : ‖v‖ ≤ ‖v - u‖ + ‖u‖ := by
        calc
          ‖v‖ = ‖(v - u) + u‖ := by congr 1; abel
          _ ≤ ‖v - u‖ + ‖u‖ := norm_add_le _ _
      exact (lt_of_le_of_lt htri (by linarith)).le
    simpa [frictionBall, dist_zero_right] using hvnorm
  obtain ⟨xstar, hxstar⟩ := hmin
  have hlower : ∃ m : ℝ, ∀ u : H, m ≤ f u := ⟨f xstar, hxstar⟩
  have hzrate := theorem_3_1 hr f z hf hconvex hsol hlower hgradient_lip hz hinitial
  have hzmain := theorem_2_1 hr f z hf₁ hlower hgradient_lip hz_diff hinitial hsol
  obtain ⟨y, hy, haverage⟩ := reverse_time_scaling_average hα hs₀ x z hx
    hbridge_initial hbridge_relation
  obtain ⟨dy, hdy, hydrate, hydyint⟩ := time_scale_velocity_transfer
    hα hs₀ z y hz hy hzrate.2 hzmain.2.2.1
  have hxt := weighted_average_velocity_transfer hα hs₀ x y (deriv x) dy
    haverage hdy hydrate hydyint
  obtain ⟨zLimit, hzLimit, hzGrad, _⟩ := hzmain.2.2.2
  have hyLimit : Filter.Tendsto y Filter.atTop (nhds zLimit) := by
    have hden : 0 < 2 * (α - 1) := mul_pos (by norm_num) (sub_pos.mpr hα)
    have hτ : Filter.Tendsto
        (fun s : ℝ => s ^ 2 / (2 * (α - 1))) Filter.atTop Filter.atTop := by
      refine Filter.tendsto_atTop.2 ?_
      intro b
      filter_upwards [Filter.eventually_atTop.2
        ⟨max 1 (2 * (α - 1) * b), fun s hs => hs⟩] with s hs
      have hs1 : 1 ≤ s := le_trans (le_max_left _ _) hs
      have hsq : s ≤ s ^ 2 := by nlinarith
      have hsb : 2 * (α - 1) * b ≤ s := le_trans (le_max_right _ _) hs
      apply (le_div_iff₀ hden).2
      nlinarith
    rw [hy]
    exact hzLimit.comp hτ
  have hxLimit := weighted_average_limit_transfer hα hs₀ x y (deriv x) zLimit
    haverage hyLimit
  refine ⟨hxt.1, hxt.2, zLimit, hxLimit, ?_⟩
  exact hzGrad

end AttouchAdlyDryFrictionDynamics2023
