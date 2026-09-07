import Mathlib
import Foundation.Analysis.ExtendedRealFunctions

namespace AttouchPeypouquetRedont2014

/-- Hypothesis `H` of the inertial forward--backward scheme. -/
structure IFBHypothesis {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi theta : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (a b lam Lpsi : ℝ) : Prop where
  phi_proper : ERealFunction.IsProper phi
  phi_lower_semicontinuous : IsClosed (ERealFunction.epigraph phi)
  phi_convex : Convex ℝ (ERealFunction.epigraph phi)
  psi_differentiable : Differentiable ℝ psi
  psi_gradient : ∀ x h, fderiv ℝ psi x h = inner ℝ (gradPsi x) h
  psi_lipschitz : ∀ x y, ‖gradPsi x - gradPsi y‖ ≤ Lpsi * ‖x - y‖
  a_pos : 0 < a
  b_pos : 0 < b
  step_pos : 0 < lam
  step_lt : lam < min (1 / a) (2 * (a + b) / (b * Lpsi))
  theta_eq : ∀ x, theta x = phi x + (psi x : EReal)
  theta_convex : Convex ℝ (ERealFunction.epigraph theta)
  theta_bounded_below : ∃ m : ℝ, ∀ x, (m : EReal) ≤ theta x

end AttouchPeypouquetRedont2014
