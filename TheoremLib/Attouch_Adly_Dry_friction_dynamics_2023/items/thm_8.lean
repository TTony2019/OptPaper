import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_3
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.thm_3
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_3
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_4
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_thm_2

namespace AttouchAdlyDryFrictionDynamics2023

/-- The second-order dual inertial system (DRYSTARDE). -/
def IsDryStarDualInertial {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (_r α s₀ : ℝ) (fstar : H → ℝ) (gradFstar : H → H)
    (hessFstar : H → H →L[ℝ] H) (gradPsiStar : H → H)
    (_hgradFstar : ∀ q v, fderiv ℝ fstar q v = inner ℝ (gradFstar q) v)
    (_hhessFstar : ∀ q v, fderiv ℝ gradFstar q v = hessFstar q v)
    (w dw ddw : ℝ → H) : Prop :=
  ∀ s ∈ Set.Ici s₀, HasDerivAt w (dw s) s ∧ HasDerivAt dw (ddw s) s ∧
    hessFstar (w s + (s / (α - 1)) • dw s)
      (ddw s + (α / s) • dw s) + gradPsiStar (w s + (s / (α - 1)) • dw s) = 0

private theorem hasDerivAt_quadratic_timeScale {α s : ℝ} (hα : 1 < α) :
    HasDerivAt (fun u : ℝ => u ^ 2 / (2 * (α - 1))) (s / (α - 1)) s := by
  have hne : α - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hα)
  convert (hasDerivAt_pow 2 s).div_const (2 * (α - 1)) using 1
  field_simp
  ring

private theorem scaled_point_eq_v {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {s₀ α s : ℝ} (hs₀ : 0 < s₀) (hα : 1 < α) (hs : s ∈ Set.Ici s₀)
    {v w dw : ℝ → H}
    (hode : dw s + ((α - 1) / s) • (w s - v s) = 0) :
    w s + (s / (α - 1)) • dw s = v s := by
  have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hαne : α - 1 ≠ 0 := sub_ne_zero.mpr (ne_of_gt hα)
  have hcoeff : (s / (α - 1)) * ((α - 1) / s) = 1 := by
    field_simp
  have hdw : dw s = ((α - 1) / s) • (v s - w s) := by
    rw [show w s - v s = -(v s - w s) by abel] at hode
    rw [smul_neg] at hode
    exact eq_of_sub_eq_zero (by simpa [sub_eq_add_neg, add_comm] using hode)
  rw [hdw, smul_smul, hcoeff, one_smul]
  abel

/-- Theorem 5.1: accelerated dual DRYSTARDE distance decay. -/
theorem theorem_5_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {s₀ r α : ℝ} (hr : 0 < r) (hs₀ : 0 < s₀) (hα : 1 < α) (x₀ : H) (z dz g v w dw ddw : ℝ → H)
    (f : H → ℝ) (fgrad : H → H) (fstar : H → ℝ) (gradFstar gradPsiStar : H → H)
    (hessFstar : H → H →L[ℝ] H)
    (_hgradient : ∀ x u, fderiv ℝ f x u = inner ℝ (fgrad x) u)
    (_hconjugate : ∀ q, fstar q = (ERealFunction.conjugate (fun x => (f x : EReal)) q).toReal)
    (hgradFstar : ∀ q v, fderiv ℝ fstar q v = inner ℝ (gradFstar q) v)
    (hhessFstar : ∀ q v, fderiv ℝ gradFstar q v = hessFstar q v)
    (hgradFstar_smooth : ∀ q, HasFDerivAt gradFstar (hessFstar q) q)
    (_hsol : IsDrygradTrajectory r hr fgrad z dz s₀)
    (hdualFlow : ∃ p : ℝ → H, ∀ t ∈ Set.Ici s₀, g t = fgrad (z t) ∧
      p t ∈ frictionBallProjector r (g t) ∧
      HasDerivAt (fun u => gradFstar (g u)) (p t - g t) t)
    (hscale : ∀ s ∈ Set.Ici s₀, v s = g (s ^ 2 / (2 * (α - 1))) ∧
      HasDerivAt w (dw s) s ∧ HasDerivAt dw (ddw s) s ∧
        dw s + ((α - 1) / s) • (w s - v s) = 0)
    (hτIci : ∀ s ∈ Set.Ici s₀, s ^ 2 / (2 * (α - 1)) ∈ Set.Ici s₀)
    (_hw₀ : w s₀ = v s₀ ∧ v s₀ = x₀)
    (hv_deriv : ∀ s ∈ Set.Ici s₀,
      HasDerivAt v ((s / (α - 1)) • (ddw s + (α / s) • dw s)) s)
    (hdualScaled : ∀ s ∈ Set.Ici s₀,
      HasDerivAt (fun u => gradFstar (v u))
        ((s / (α - 1)) • (Classical.choose hdualFlow
          (s ^ 2 / (2 * (α - 1))) - v s)) s)
    (hv_decay : Filter.Tendsto (fun s : ℝ => s * Metric.infDist (v s) (frictionBall r)) Filter.atTop (nhds 0))
    (hw_decay : Filter.Tendsto (fun s : ℝ => s * Metric.infDist (w s) (frictionBall r)) Filter.atTop (nhds 0))
    (hpsi : ∀ u q, q ∈ frictionBallProjector r u → gradPsiStar u = u - q) :
    IsDryStarDualInertial r α s₀ fstar gradFstar hessFstar gradPsiStar hgradFstar hhessFstar w dw ddw ∧
    Filter.Tendsto (fun s : ℝ => s * Metric.infDist (w s + (s / (α - 1)) • dw s) (frictionBall r)) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun s : ℝ => s * Metric.infDist (w s) (frictionBall r)) Filter.atTop (nhds 0) := by
  constructor
  · unfold IsDryStarDualInertial
    intro s hs
    refine ⟨(hscale s hs).2.1, (hscale s hs).2.2.1, ?_⟩
    have hv_eq := scaled_point_eq_v hs₀ hα hs (hscale s hs).2.2.2
    have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
    have hτpos : 0 < s / (α - 1) := div_pos hspos (sub_pos.mpr hα)
    have hτne : s / (α - 1) ≠ 0 := ne_of_gt hτpos
    let p : ℝ → H := Classical.choose hdualFlow
    have hpflow : ∀ t ∈ Set.Ici s₀, g t = fgrad (z t) ∧
        p t ∈ frictionBallProjector r (g t) ∧
          HasDerivAt (fun u => gradFstar (g u)) (p t - g t) t :=
      Classical.choose_spec hdualFlow
    have hp : p (s ^ 2 / (2 * (α - 1))) ∈ frictionBallProjector r
        (g (s ^ 2 / (2 * (α - 1)))) := (hpflow _ (hτIci s hs)).2.1
    have hdual' : HasDerivAt (fun u => gradFstar (v u))
        ((s / (α - 1)) • (p (s ^ 2 / (2 * (α - 1))) - v s)) s := by
      simpa only [p] using hdualScaled s hs
    have hv' : HasDerivAt v ((s / (α - 1)) • (ddw s + (α / s) • dw s)) s := hv_deriv s hs
    have hgrad : HasDerivAt (fun u => gradFstar (v u))
        (hessFstar (v s) ((s / (α - 1)) • (ddw s + (α / s) • dw s))) s :=
      (hgradFstar_smooth (v s)).comp_hasDerivAt s hv'
    have heq := hgrad.unique hdual'
    rw [ContinuousLinearMap.map_smul] at heq
    have hmain : hessFstar (v s) (ddw s + (α / s) • dw s) = p (s ^ 2 / (2 * (α - 1))) - v s :=
      smul_right_injective H hτne heq
    have hps : p (s ^ 2 / (2 * (α - 1))) ∈ frictionBallProjector r (v s) := by
      simpa only [(hscale s hs).1] using hp
    rw [hv_eq, hmain, hpsi _ _ hps]
    abel
  constructor
  · apply hv_decay.congr'
    filter_upwards [Filter.eventually_ge_atTop s₀] with s hs
    rw [scaled_point_eq_v hs₀ hα hs (hscale s hs).2.2.2]
  · exact hw_decay

end AttouchAdlyDryFrictionDynamics2023
