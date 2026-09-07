import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_2

namespace AttouchPeypouquetRedont2014

open ERealFunction

/-- A pair of sequences satisfies the inertial forward--backward update. -/
structure IsIFBTrajectory {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (a b lam : ℝ)
    (u y : ℕ → H) : Prop where
  a_pos : 0 < a
  b_pos : 0 < b
  lambda_pos : 0 < lam
  phi_proper : ERealFunction.IsProper phi
  first_update : ∀ k, ∃ g ∈ subdifferential phi (u (k + 1)),
    (1 / lam) • (u (k + 1) - u k) + g + a • u k - b • y k = 0
  second_update : ∀ k,
    (1 / lam) • (y (k + 1) - y k) + gradPsi (u (k + 1)) - a • u (k + 1) + b • y (k + 1) = 0

end AttouchPeypouquetRedont2014
