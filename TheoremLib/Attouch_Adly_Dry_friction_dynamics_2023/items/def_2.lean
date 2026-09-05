import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_1

namespace AttouchAdlyDryFrictionDynamics2023

/-- Pointwise form of (DRYGRAD): `0 ∈ v + ∂φ(v) + ∇f(z)`. -/
def IsDrygradTrajectory {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (r : ℝ) (f : H → ℝ) (z : ℝ → H) (t₀ : ℝ) : Prop :=
  ∀ t ∈ Set.Ici t₀, ∃ u : H,
    u ∈ ERealFunction.subdifferential
      (dryFrictionPotential (H := H) r) (deriv z t) ∧
        deriv z t + u + gradient f (z t) = 0

end AttouchAdlyDryFrictionDynamics2023
