import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_1

namespace AttouchAdlyDryFrictionDynamics2023

/-- Pointwise form of (DRYGRAD): `0 ∈ v + ∂φ(v) + ∇f(z)`. -/
def IsDrygradTrajectory {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (r : ℝ) (hr : 0 < r) (f : H → ℝ) (hf : Differentiable ℝ f)
    (z dz : ℝ → H) (t₀ : ℝ) : Prop :=
  let _ := hr
  let _ := hf
  ∀ t ∈ Set.Ici t₀, HasDerivAt z (dz t) t ∧
    ∃ u : H,
      (∀ y : H,
        (dryFrictionPotential (H := H) r (dz t) : EReal) +
            (inner ℝ u (y - dz t) : EReal) ≤
          (dryFrictionPotential (H := H) r y : EReal)) ∧
        dz t + u + gradient f (z t) = 0

end AttouchAdlyDryFrictionDynamics2023
