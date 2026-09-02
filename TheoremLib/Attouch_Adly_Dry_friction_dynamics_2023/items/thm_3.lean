import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_3
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_lem_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_3
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_5

namespace AttouchAdlyDryFrictionDynamics2023

/-- Theorem 3.2: dual Riemannian flow and decay of distance to the friction ball.

The differentiability and dissipation certificates are the smooth form of the
dual-flow calculation (3.9)--(3.13) used in the paper.  They are stated
explicitly because `IsDrygradTrajectory` alone only supplies a subgradient
witness and does not provide this regularity. -/
theorem theorem_3_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {t₀ r : ℝ} (hr : 0 < r) (f : H → ℝ) (hf : Differentiable ℝ f) (z : ℝ → H)
    (fstar : H → ℝ) (gradFstar : H → H) (p : ℝ → H)
    (hp : ∀ t : ℝ, p t ∈ frictionBallProjector r (gradient f (z t)))
    (hdual : ∀ t ∈ Set.Ici t₀,
      HasDerivAt (fun u => gradFstar (gradient f (z u))) (p t - gradient f (z t)) t)
    (hdist : ∀ t : ℝ,
      HasDerivAt (fun u => Metric.infDist (gradient f (z u)) (frictionBall r) ^ 2)
        (inner ℝ (gradient f (z t) - p t) (p t - gradient f (z t))) t)
    (hint : MeasureTheory.IntegrableOn
      (fun t => Metric.infDist (gradient f (z t)) (frictionBall r) ^ 2 / 2) (Set.Ici t₀))
    (hbregman : ∀ gLimit : H, gLimit ∈ frictionBall r → ∀ t : ℝ,
      HasDerivAt
        (fun u => dualBregmanDistance fstar gradFstar (gradient f (z u)) gLimit)
        (inner ℝ (gradient f (z t) - p t) (gLimit - gradient f (z t))) t) :
    (∀ t ∈ Set.Ici t₀,
      p t ∈ frictionBallProjector r (gradient f (z t)) ∧
      HasDerivAt (fun u => gradFstar (gradient f (z u))) (p t - gradient f (z t)) t) ∧
    AntitoneOn (fun t => Metric.infDist (gradient f (z t)) (frictionBall r) ^ 2) (Set.Ici t₀) ∧
      Filter.Tendsto (fun t : ℝ => Real.sqrt t * Metric.infDist (gradient f (z t)) (frictionBall r))
        Filter.atTop (nhds 0) ∧
      ∀ gLimit : H, gLimit ∈ frictionBall r →
        AntitoneOn (fun t => dualBregmanDistance fstar gradFstar (gradient f (z t)) gLimit)
          (Set.Ici t₀) := by
  let g : ℝ → H := fun t => gradient f (z t)
  have hdist_nonpos : ∀ t : ℝ,
      inner ℝ (g t - p t) (p t - g t) ≤ 0 := by
    intro t
    rw [show p t - g t = -(g t - p t) by abel, inner_neg_right]
    exact neg_nonpos.mpr real_inner_self_nonneg
  have hdist_anti : Antitone (fun t => Metric.infDist (g t) (frictionBall r) ^ 2) := by
    apply antitone_of_deriv_nonpos (fun t => (hdist t).differentiableAt)
    intro t
    rw [(hdist t).deriv]
    exact hdist_nonpos t
  have hhalf_nonneg : ∀ t ∈ Set.Ici t₀,
      0 ≤ Metric.infDist (g t) (frictionBall r) ^ 2 / 2 := by
    intro t ht
    positivity
  have hhalf_anti : AntitoneOn
      (fun t => Metric.infDist (g t) (frictionBall r) ^ 2 / 2) (Set.Ici t₀) := by
    intro s hs t ht hst
    exact div_le_div_of_nonneg_right (hdist_anti hst) (by norm_num)
  have htail := lemma_3_1 (t₀ := t₀)
    (fun t => Metric.infDist (g t) (frictionBall r) ^ 2 / 2)
    hhalf_nonneg hhalf_anti hint
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
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht
    exact ⟨hp t, hdual t ht⟩
  · simpa [g] using hdist_anti.antitoneOn (Set.Ici t₀)
  · simpa [g] using hrate
  · intro gLimit hgLimit
    have hanti : Antitone
        (fun t => dualBregmanDistance fstar gradFstar (g t) gLimit) := by
      apply antitone_of_deriv_nonpos
      · intro t
        exact (hbregman gLimit hgLimit t).differentiableAt
      · intro t
        rw [(hbregman gLimit hgLimit t).deriv]
        have hp' : IsFrictionBallBestApproximation r (g t) (p t) := hp t
        rw [show gLimit - g t = (gLimit - p t) + (p t - g t) by abel,
          inner_add_right]
        have hproj : inner ℝ (g t - p t) (gLimit - p t) ≤ 0 := by
          exact (norm_eq_iInf_iff_real_inner_le_zero
            (by simpa [frictionBall] using (convex_closedBall (0 : H) r)) hp'.1).mp
            (by simpa [dist_eq_norm, Metric.infDist_eq_iInf] using hp'.2) gLimit hgLimit
        rw [show p t - g t = -(g t - p t) by abel, inner_neg_right]
        nlinarith [real_inner_self_nonneg (x := g t - p t)]
    change AntitoneOn (fun t => dualBregmanDistance fstar gradFstar (g t) gLimit) (Set.Ici t₀)
    exact hanti.antitoneOn _

end AttouchAdlyDryFrictionDynamics2023
