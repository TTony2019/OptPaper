import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_2

namespace AttouchAdlyDryFrictionDynamics2023

/-- Bregman distance `D_F(a,b) = F(b)-F(a)-⟪∇F(a),b-a⟫`. -/
def bregmanDistance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (F : H → ℝ) (gradF : H → H) (a b : H) : ℝ := F b - F a - inner ℝ (gradF a) (b - a)

end AttouchAdlyDryFrictionDynamics2023
