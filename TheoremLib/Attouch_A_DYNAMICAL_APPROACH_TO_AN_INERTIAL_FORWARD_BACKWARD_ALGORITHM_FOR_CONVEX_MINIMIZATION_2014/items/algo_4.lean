import Mathlib
import Foundation.Projection.BestApproximation
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.algo_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_6

namespace AttouchPeypouquetRedont2014

/-- General-parameter IFB gradient--projection iteration (5.6). -/
noncomputable def IsGeneralIFBGradientProjection {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (hC : IsChebyshev C) (Ci : ℕ → Set H) (hCi : ∀ i, IsChebyshev (Ci i))
    (ω : ℕ → ℝ) (p : ℕ) (a b lam : ℝ)
    (u y : ℕ → H) : Prop := ∀ k,
  0 < a ∧ 0 < b ∧ u (k + 1) = projectionPoint C hC ((1 - lam * a) • u k + (lam * b) • y k) ∧
  y (k + 1) = (1 / (1 + lam * b)) • y k + (lam * a / (1 + lam * b)) • u (k + 1) -
    (lam / (1 + lam * b)) • (u (k + 1) - ∑ i ∈ Finset.Icc 1 p,
      ω i • projectionPoint (Ci i) (hCi i) (u (k + 1)))

end AttouchPeypouquetRedont2014
