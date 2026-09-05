import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.thm_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.thm_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_thm_4

namespace AttouchAdlyDryFrictionDynamics2023

/-- The valid descent conclusion of Theorem A.1 for a regular DRYGRAD trajectory. -/
theorem theorem_A_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {t₀ r : ℝ}
    (hr : 0 < r) (f : H → ℝ) (z : ℝ → H) (hf : ContDiff ℝ 1 f)
    (hf_lower : ∃ m : ℝ, ∀ x : H, m ≤ f x) (hgradient_lip : LocallyLipschitz (gradient f))
    (hinitial : r < ‖gradient f (z t₀)‖)
    (hsolution : IsDrygradTrajectory r f z t₀)
    (hz_diff : Differentiable ℝ z) :
    AntitoneOn (fun t => f (z t)) (Set.Ici t₀) :=
  (theorem_2_1 hr f z hf hf_lower hgradient_lip hz_diff hinitial hsolution).1

end AttouchAdlyDryFrictionDynamics2023
