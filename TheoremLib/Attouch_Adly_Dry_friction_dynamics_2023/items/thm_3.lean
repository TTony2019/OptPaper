import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_3
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_lem_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.thm_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.thm_2

namespace AttouchAdlyDryFrictionDynamics2023

/-- The normalized dual Bregman energy along a primal trajectory.

When the Fenchel conjugate is finite at `gLimit`, this differs from the paper's
`D_{f*}(gradient f (z t), gLimit)` only by the constant `f*(gLimit)`.  This
form remains real-valued without imposing an unnecessary global smoothness
assumption on the conjugate. -/
def dualBregmanEnergy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (z : ℝ → H) (gLimit : H) (t : ℝ) : ℝ :=
  f (z t) - inner ℝ gLimit (z t)

/-- Theorem 3.2: the generalized dual flow and decay of the distance to the
friction ball.

The assumptions on `f` are the standing assumptions of the paper and the
convexity assumption of Section 3.  The theorem-specific hypotheses are only
the differentiability of `z` and the fact that it solves DRYGRAD. -/
theorem theorem_3_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {t₀ r : ℝ} (hr : 0 < r) (f : H → ℝ) (z : ℝ → H)
    (hf : ContDiff ℝ 2 f) (hconvex : ConvexOn ℝ Set.univ f)
    (hf_lower : ∃ m : ℝ, ∀ x : H, m ≤ f x)
    (hgradient_lip : LocallyLipschitz (gradient f))
    (hz_diff : Differentiable ℝ z) (hsol : IsDrygradTrajectory r f z t₀) :
    (∃ p : ℝ → H, ∀ t ∈ Set.Ici t₀,
      p t ∈ frictionBallProjector r (gradient f (z t)) ∧
        HasDerivAt z (p t - gradient f (z t)) t) ∧
    AntitoneOn
      (fun t => Metric.infDist (gradient f (z t)) (frictionBall r) ^ 2) (Set.Ici t₀) ∧
    Filter.Tendsto
      (fun t : ℝ => Real.sqrt t * Metric.infDist (gradient f (z t)) (frictionBall r))
      Filter.atTop (nhds 0) ∧
    ∀ gLimit : H, gLimit ∈ frictionBall r →
      AntitoneOn (dualBregmanEnergy f z gLimit) (Set.Ici t₀) := by
  classical
  let g : ℝ → H := fun t => gradient f (z t)
  let p : ℝ → H := fun t => frictionBallProjection r hr (g t)
  have hf_diff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfderiv_contdiff : ContDiff ℝ 1 (fderiv ℝ f) := by
    exact (contDiff_succ_iff_fderiv.mp (show ContDiff ℝ (1 + 1) f by simpa using hf)).2.2
  have hgradient_contdiff : ContDiff ℝ 1 (gradient f) := by
    simpa [gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hfderiv_contdiff
  have hgradient_diff : Differentiable ℝ (gradient f) :=
    hgradient_contdiff.differentiable (by norm_num)
  have hg_deriv : ∀ t : ℝ,
      HasDerivAt g (fderiv ℝ (gradient f) (z t) (deriv z t)) t := by
    intro t
    simpa [g, Function.comp_def] using
      (hgradient_diff (z t)).hasFDerivAt.comp_hasDerivAt t (hz_diff t).hasDerivAt
  have hp_mem : ∀ t : ℝ, p t ∈ frictionBallProjector r (g t) := by
    intro t
    exact (frictionBall_isChebyshev hr.le (g t)).choose_spec.1
  have hp_formula : ∀ t : ℝ, p t = g t - softThresholder r (g t) := by
    intro t
    exact frictionBallProjection_eq_sub_softThresholder r hr (g t)
  have hvelocity : ∀ t ∈ Set.Ici t₀, deriv z t = p t - g t := by
    intro t ht
    rw [hp_formula]
    have hv := drygrad_velocity_formula hr (hsol t ht)
    simpa using hv
  have hgnorm_deriv : ∀ t ∈ interior (Set.Ici t₀),
      HasDerivAt (fun s => ‖g s‖)
        (if g t = 0 then 0 else
          inner ℝ (fderiv ℝ (gradient f) (z t) (deriv z t)) (g t) / ‖g t‖) t := by
    intro t ht
    by_cases hgt : g t = 0
    · rw [if_pos hgt]
      have hzt : deriv z t = 0 := by
        rw [hvelocity t (interior_subset ht), hp_formula, hgt]
        simp [softThresholder_apply]
      have hg0 : HasDerivAt g 0 t := by
        simpa [hzt] using hg_deriv t
      rw [hasDerivAt_iff_isLittleO]
      simpa [hgt] using hg0.isLittleO.norm_left
    · rw [if_neg hgt]
      have hnorm_ne : ‖g t‖ ≠ 0 := norm_ne_zero_iff.mpr hgt
      have hs := (hg_deriv t).norm_sq.sqrt (pow_ne_zero 2 hnorm_ne)
      convert hs using 1
      all_goals simp [real_inner_comm, norm_nonneg]
      all_goals field_simp
  have hgnorm_deriv_nonpos : ∀ t ∈ interior (Set.Ici t₀),
      deriv (fun s => ‖g s‖) t ≤ 0 := by
    intro t ht
    rw [(hgnorm_deriv t ht).deriv]
    by_cases hgt : g t = 0
    · simp [hgt]
    · rw [if_neg hgt]
      by_cases hball : ‖g t‖ ≤ r
      · have hzt : deriv z t = 0 := by
          rw [hvelocity t (interior_subset ht), hp_formula, softThresholder_apply,
            if_neg (not_lt_of_ge hball)]
          simp
        simp [hzt]
      · have houtside : r < ‖g t‖ := lt_of_not_ge hball
        have hcoef : 0 < 1 - r / ‖g t‖ := by
          rw [sub_pos, div_lt_one (lt_trans hr houtside)]
          exact houtside
        have hzt : deriv z t = -(1 - r / ‖g t‖) • g t := by
          rw [hvelocity t (interior_subset ht), hp_formula, softThresholder_apply,
            if_pos houtside]
          module
        have hmono := gradient_derivative_inner_nonnegative f hconvex hf_diff z
          (hz_diff t) (hg_deriv t).differentiableAt
        rw [(hg_deriv t).deriv] at hmono
        have hmono' : 0 ≤ -(1 - r / ‖g t‖) *
            inner ℝ (g t) (fderiv ℝ (gradient f) (z t) (deriv z t)) := by
          calc
            0 ≤ inner ℝ (deriv z t)
                (fderiv ℝ (gradient f) (z t) (deriv z t)) := hmono
            _ = -(1 - r / ‖g t‖) *
                inner ℝ (g t) (fderiv ℝ (gradient f) (z t) (deriv z t)) := by
              rw [hzt, real_inner_smul_left]
        have hinner : inner ℝ (fderiv ℝ (gradient f) (z t) (deriv z t)) (g t) ≤ 0 := by
          rw [real_inner_comm]
          nlinarith
        exact div_nonpos_of_nonpos_of_nonneg hinner (norm_nonneg _)
  have hgnorm_anti : AntitoneOn (fun t => ‖g t‖) (Set.Ici t₀) := by
    have hcont : ContinuousOn (fun t => ‖g t‖) (Set.Ici t₀) := by
      exact (hgradient_lip.continuous.comp_continuousOn
        hz_diff.continuous.continuousOn).norm
    apply antitoneOn_of_deriv_nonpos (convex_Ici t₀) hcont
    · intro t ht
      exact (hgnorm_deriv t ht).differentiableAt.differentiableWithinAt
    · exact hgnorm_deriv_nonpos
  have hdist_formula : ∀ t : ℝ,
      Metric.infDist (g t) (frictionBall r) = max (‖g t‖ - r) 0 :=
    fun t => infDist_frictionBall_eq r hr (g t)
  have hdist_anti : AntitoneOn
      (fun t => Metric.infDist (g t) (frictionBall r) ^ 2) (Set.Ici t₀) := by
    intro s hs t ht hst
    change Metric.infDist (g t) (frictionBall r) ^ 2 ≤
      Metric.infDist (g s) (frictionBall r) ^ 2
    rw [hdist_formula, hdist_formula]
    have hmax : max (‖g t‖ - r) 0 ≤ max (‖g s‖ - r) 0 := by
      exact max_le_max_right 0 (sub_le_sub_right (hgnorm_anti hs ht hst) r)
    exact pow_le_pow_left₀ (by positivity) hmax 2
  have hdist_velocity : ∀ t ∈ Set.Ici t₀,
      Metric.infDist (g t) (frictionBall r) = ‖deriv z t‖ := by
    intro t ht
    have hpdist := (hp_mem t).2
    rw [← hpdist, dist_eq_norm, hvelocity t ht]
    rw [show g t - p t = -(p t - g t) by abel, norm_neg]
  have hdist_integrable : MeasureTheory.IntegrableOn
      (fun t => Metric.infDist (g t) (frictionBall r) ^ 2 / 2) (Set.Ici t₀) := by
    by_cases hinitial : r < ‖g t₀‖
    · have hsq := (theorem_2_1 hr f z (hf.of_le (by norm_num)) hf_lower hgradient_lip
          hz_diff (by simpa [g] using hinitial) hsol).2.1
      have hsq' : MeasureTheory.IntegrableOn
          (fun t => Metric.infDist (g t) (frictionBall r) ^ 2) (Set.Ici t₀) := by
        apply hsq.congr_fun
        · intro t ht
          change ‖deriv z t‖ ^ 2 = Metric.infDist (g t) (frictionBall r) ^ 2
          rw [hdist_velocity t ht]
        · exact measurableSet_Ici
      exact hsq'.div_const 2
    · have hzero : ∀ t ∈ Set.Ici t₀,
          Metric.infDist (g t) (frictionBall r) ^ 2 / 2 = 0 := by
        intro t ht
        have hle : ‖g t‖ ≤ r :=
          (hgnorm_anti (Set.mem_Ici.mpr le_rfl) ht ht).trans (not_lt.mp hinitial)
        rw [hdist_formula, max_eq_right (sub_nonpos.mpr hle)]
        norm_num
      apply MeasureTheory.integrableOn_zero.congr_fun
      · intro t ht
        exact (hzero t ht).symm
      · exact measurableSet_Ici
  have hhalf_nonneg : ∀ t ∈ Set.Ici t₀,
      0 ≤ Metric.infDist (g t) (frictionBall r) ^ 2 / 2 := by
    intro t ht
    positivity
  have hhalf_anti : AntitoneOn
      (fun t => Metric.infDist (g t) (frictionBall r) ^ 2 / 2) (Set.Ici t₀) := by
    intro s hs t ht hst
    exact div_le_div_of_nonneg_right (hdist_anti hs ht hst) (by norm_num)
  have htail := lemma_3_1 (t₀ := t₀)
    (fun t => Metric.infDist (g t) (frictionBall r) ^ 2 / 2)
    hhalf_nonneg hhalf_anti hdist_integrable
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
  have hbregman : ∀ gLimit : H, gLimit ∈ frictionBall r →
      AntitoneOn (dualBregmanEnergy f z gLimit) (Set.Ici t₀) := by
    intro gLimit hgLimit
    have hderiv : ∀ t ∈ Set.Ici t₀,
        HasDerivAt (dualBregmanEnergy f z gLimit)
          (inner ℝ (g t - gLimit) (p t - g t)) t := by
      intro t ht
      have hfz := (hf_diff (z t)).hasGradientAt.hasFDerivAt.comp_hasDerivAt
        t (hz_diff t).hasDerivAt
      have hinner := (hasDerivAt_const t gLimit).inner ℝ (hz_diff t).hasDerivAt
      convert hfz.sub hinner using 1
      rw [← hvelocity t ht]
      simp [g, inner_sub_left]
    have hcont : ContinuousOn (dualBregmanEnergy f z gLimit) (Set.Ici t₀) :=
      HasDerivAt.continuousOn hderiv
    apply antitoneOn_of_deriv_nonpos (convex_Ici t₀) hcont
    · intro t ht
      exact (hderiv t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hderiv t (interior_subset ht)).deriv]
      have hp' : IsFrictionBallBestApproximation r (g t) (p t) := hp_mem t
      rw [show g t - gLimit = (g t - p t) + (p t - gLimit) by abel,
        inner_add_left]
      have hproj : inner ℝ (g t - p t) (gLimit - p t) ≤ 0 := by
        exact (norm_eq_iInf_iff_real_inner_le_zero
          (by simpa [frictionBall] using (convex_closedBall (0 : H) r)) hp'.1).mp
          (by simpa [dist_eq_norm, Metric.infDist_eq_iInf] using hp'.2) gLimit hgLimit
      have hfirst : inner ℝ (g t - p t) (p t - g t) ≤ 0 := by
        rw [show p t - g t = -(g t - p t) by abel, inner_neg_right]
        exact neg_nonpos.mpr real_inner_self_nonneg
      have hsecond : inner ℝ (p t - gLimit) (p t - g t) ≤ 0 := by
        calc
          inner ℝ (p t - gLimit) (p t - g t) =
              inner ℝ (gLimit - p t) (g t - p t) := by
                rw [show p t - gLimit = -(gLimit - p t) by abel,
                  show p t - g t = -(g t - p t) by abel,
                  inner_neg_left, inner_neg_right, neg_neg]
          _ = inner ℝ (g t - p t) (gLimit - p t) := real_inner_comm _ _
          _ ≤ 0 := hproj
      linarith
  refine ⟨⟨p, ?_⟩, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨hp_mem t, (hz_diff t).hasDerivAt.congr_deriv (hvelocity t ht)⟩
  · simpa [g] using hdist_anti
  · simpa [g] using hrate
  · exact hbregman

end AttouchAdlyDryFrictionDynamics2023
