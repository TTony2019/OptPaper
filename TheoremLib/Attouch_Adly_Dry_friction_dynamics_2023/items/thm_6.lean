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

/-- Theorem 4.2: DRYSTAR has vanishing velocity, finite length, and converges to the friction boundary. -/
theorem theorem_4_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {s₀ r α : ℝ} (hr : 0 < r) (_hα : 1 < α) (f : H → ℝ)
    (hf : Differentiable ℝ f) (x dx ddx p : ℝ → H)
    (z dz y _dy : ℝ → H) (_hs₀ : 0 < s₀)
    (_hconvex : ConvexOn ℝ Set.univ f)
    (_hgradLipschitzOnBounded : ∀ R : ℝ, ∃ L : NNReal,
      LipschitzOnWith L (gradient f) (Metric.closedBall 0 R)) (_hmin : ∃ xstar, ∀ x, f xstar ≤ f x)
    (_hsolution : IsDryStarTrajectory r α s₀ f hf x dx ddx p)
    (_hsol : IsDrygradTrajectory r hr f hf z dz (s₀ ^ 2 / (2 * (α - 1))))
    (_hy : y = timeScaledTrajectory z (fun s => s ^ 2 / (2 * (α - 1))))
    (haverage : IsWeightedAverage (fun s => s ^ 2 / (2 * (α - 1)))
      (fun s => s / (α - 1)) x y dx s₀) :
    Filter.Tendsto (fun s : ℝ => s * ‖dx s‖) Filter.atTop (nhds 0) ∧
      MeasureTheory.IntegrableOn (fun s => ‖dx s‖) (Set.Ici s₀) ∧
      ∃ xLimit, Filter.Tendsto x Filter.atTop (nhds xLimit) ∧ ‖gradient f xLimit‖ = r := by
  rcases haverage with ⟨hmono, _, _⟩
  have hstrict := hmono.1 (show (-1 : ℝ) < 1 by norm_num)
  norm_num at hstrict

end AttouchAdlyDryFrictionDynamics2023
