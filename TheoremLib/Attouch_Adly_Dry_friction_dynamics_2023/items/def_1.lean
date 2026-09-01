import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_1

namespace AttouchAdlyDryFrictionDynamics2023

/-- The dry-friction potential `φ(x) = r ‖x‖` for a positive friction coefficient. -/
def dryFrictionPotential {H : Type*} [NormedAddCommGroup H] (r : ℝ) (x : H) : ℝ := r * ‖x‖

def IsDryFrictionPotential {H : Type*} [NormedAddCommGroup H] (φ : H → ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∀ x, φ x = r * ‖x‖

end AttouchAdlyDryFrictionDynamics2023
