import Mathlib
import Foundation.Projection.BestApproximation
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_6
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_7
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_8

namespace AttouchPeypouquetRedont2014

/-- Classical CQ update (5.13), with `A†` denoting the adjoint action. -/
noncomputable def IsCQTrajectory {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] (C : Set H) (hC : IsChebyshev C)
    (Q : Set K) (hQ : IsChebyshev Q) (A : H → K) (At : K → H)
    (_hAt : ∀ x z, inner ℝ (A x) z = inner ℝ x (At z)) (lam : ℝ) (u : ℕ → H) : Prop :=
  ∀ k, u (k + 1) = projectionPoint C hC (u k - lam • At
    (A (u k) - projectionPoint Q hQ (A (u k))))

end AttouchPeypouquetRedont2014
