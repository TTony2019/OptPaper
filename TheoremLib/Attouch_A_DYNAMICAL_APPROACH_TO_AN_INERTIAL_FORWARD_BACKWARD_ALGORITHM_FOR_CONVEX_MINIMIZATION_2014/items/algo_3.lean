import Mathlib
import Foundation.Projection.BestApproximation
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_6

namespace AttouchPeypouquetRedont2014

/-- Classical gradient--projection update (5.4). -/
noncomputable def IsClassicalGradientProjectionTrajectory {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (hC : IsChebyshev C) (Ci : ℕ → Set H) (hCi : ∀ i, IsChebyshev (Ci i))
    (ω : ℕ → ℝ) (p : ℕ) (lam : ℝ) (u : ℕ → H) : Prop :=
  0 < lam ∧ lam < 2 ∧ ∀ k,
    u (k + 1) = projectionPoint C hC ((1 - lam) • u k + lam • ∑ i ∈ Finset.Icc 1 p,
      ω i • projectionPoint (Ci i) (hCi i) (u k))

end AttouchPeypouquetRedont2014
