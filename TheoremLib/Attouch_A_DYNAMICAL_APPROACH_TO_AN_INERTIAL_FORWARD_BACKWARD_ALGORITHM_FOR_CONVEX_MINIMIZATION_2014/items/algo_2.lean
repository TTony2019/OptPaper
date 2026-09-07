import Mathlib
import Foundation.Projection.BestApproximation
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_6
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_7

namespace AttouchPeypouquetRedont2014

/-- The two updates of the gradient--projection algorithm (5.1). -/
noncomputable def IsGradientProjectionTrajectory {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (hC : IsChebyshev C) (gradPsi : H → H) (lam μ : ℝ) (u y : ℕ → H) : Prop :=
  μ = lam / (1 + lam) ∧ ∀ k,
    u (k + 1) = projectionPoint C hC (lam • y k + (1 - lam) • u k) ∧
    y (k + 1) = (1 - μ) • y k + μ • (u (k + 1) - gradPsi (u (k + 1)))

end AttouchPeypouquetRedont2014
