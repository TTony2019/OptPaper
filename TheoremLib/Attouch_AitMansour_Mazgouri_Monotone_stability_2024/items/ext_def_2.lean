import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_3

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-- The parametric damped second-order system `S(A_μ,u₀^μ,v₀^μ)`.

The paper assumes positive damping and uses the same notion of strong global
solution as Definition 2.3: all differential conditions hold almost everywhere
on the forward half-line.  Although trajectories are represented as functions
on `ℝ`, no condition is imposed at negative times. -/
def ext_def_2 {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : H → H) (γ : ℝ) (u₀ v₀ : H) (x dx ddx : ℝ → H) : Prop :=
  0 < γ ∧ def_3 A γ u₀ v₀ x dx ddx

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
