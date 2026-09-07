import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_3
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_5
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_2

namespace AttouchPeypouquetRedont2014

open ERealFunction

/-- The vector `z_k = ξ_k/λ + a u_{k-1} - b y_{k-1}`. -/
noncomputable def zSequence {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (u y : ℕ → H)
    (a b lam : ℝ) (k : ℕ) (hk : 1 ≤ k) : H :=
  (1 / lam) • velocity u k hk + a • u (k - 1) - b • y (k - 1)

/-- The membership part of equation (3.4). -/
def HasZSubgradient {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ : H → EReal) (u y : ℕ → H) (a b lam : ℝ)
    (_hΦconvex : Convex ℝ (ERealFunction.epigraph Φ)) : Prop :=
  ∀ k (hk : 1 ≤ k),
    -zSequence u y a b lam k hk ∈ subdifferential Φ (u k)

end AttouchPeypouquetRedont2014
