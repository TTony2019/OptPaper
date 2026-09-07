import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_2
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_3

namespace AttouchPeypouquetRedont2014

/-- Mechanical energy `E_k = Θ(u_k) + γ‖ξ_k‖²`. -/
noncomputable def mechanicalEnergy {H : Type*} [NormedAddCommGroup H] (Θ : H → EReal)
    (u : ℕ → H) (γ : ℝ) (k : ℕ) (hk : 1 ≤ k) : EReal :=
  Θ (u k) + ((γ * ‖velocity u k hk‖ ^ 2 : ℝ) : EReal)

end AttouchPeypouquetRedont2014
