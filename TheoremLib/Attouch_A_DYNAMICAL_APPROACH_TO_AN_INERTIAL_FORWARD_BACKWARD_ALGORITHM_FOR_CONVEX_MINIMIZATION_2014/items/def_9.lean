import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_7

namespace AttouchPeypouquetRedont2014

/-- The sequence `A_k(q)` of (3.23). -/
noncomputable def auxiliaryA {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u y : ℕ → H) (a b lam : ℝ) (q : H) (k : ℕ) (hk : 1 ≤ k) : ℝ :=
  (a + b) / (2 * lam) * ‖u k - q‖ ^ 2 -
    (1 / lam + b) * auxiliaryG u y a b lam q (k + 1) (by omega)

end AttouchPeypouquetRedont2014
