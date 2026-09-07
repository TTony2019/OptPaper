import Mathlib
import Foundation.Projection.BestApproximation
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.algo_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_6
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_7
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_8

namespace AttouchPeypouquetRedont2014

/-- IFB CQ iteration (5.14). -/
noncomputable def IsIFBCQTrajectory {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [NormedAddCommGroup K] [InnerProductSpace ℝ K] (C : Set H) (hC : IsChebyshev C)
    (Q : Set K) (hQ : IsChebyshev Q) (A : H → K) (At : K → H)
    (_hAt : ∀ x z, inner ℝ (A x) z = inner ℝ x (At z)) (a b lam : ℝ)
    (u y : ℕ → H) : Prop := 0 < a ∧ 0 < b ∧ 0 < lam ∧ ∀ k,
  u (k + 1) = projectionPoint C hC ((1 - lam * a) • u k + (lam * b) • y k) ∧
  y (k + 1) = (1 / (1 + lam * b)) • y k + (lam * a / (1 + lam * b)) • u (k + 1) -
    (lam / (1 + lam * b)) • (u (k + 1) - At
      (A (u (k + 1)) - projectionPoint Q hQ (A (u (k + 1)))))

end AttouchPeypouquetRedont2014
