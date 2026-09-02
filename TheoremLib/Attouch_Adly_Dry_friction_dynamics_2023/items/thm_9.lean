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
    (hr : 0 < r) (f : H → ℝ) (z dz : ℝ → H) (hf : ContDiff ℝ 1 f)
    (hf_lower : ∃ m : ℝ, ∀ x : H, m ≤ f x) (hgradient_lip : LocallyLipschitz (gradient f))
    (hinitial : r < ‖gradient f (z t₀)‖)
    (hchain : ∀ t ∈ Set.Ici t₀,
      HasDerivAt (fun s => f (z s)) (inner ℝ (gradient f (z t)) (dz t)) t)
    (hcomp_cont : ContinuousOn (fun t => f (z t)) (Set.Ici t₀))
    (hsolution : IsDrygradTrajectory r hr f (hf.differentiable (by norm_num)) z dz t₀)
    (V : H → H) (hV_lip : LocallyLipschitz V)
    (hV_zero : ∀ x, V x = 0 ↔ ‖gradient f x‖ ≤ r)
    (hvelocity : ∀ t ∈ Set.Ici t₀, dz t = V (z t))
    (hvelocity_limit : Filter.Tendsto dz Filter.atTop (nhds 0))
    (hstationary : ∀ S ∈ Set.Ici t₀, V (z S) = 0 →
      ∀ t ∈ Set.Ici S, z t = z S) :
    AntitoneOn (fun t => f (z t)) (Set.Ici t₀) :=
  (theorem_2_1 hr f z dz hf hf_lower hgradient_lip hinitial hchain hcomp_cont hsolution V
    hV_lip hV_zero hvelocity hvelocity_limit hstationary).1

end AttouchAdlyDryFrictionDynamics2023
