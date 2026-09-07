import Mathlib

namespace Alvarez2002

/-- Assumption `(H)` of the paper.  The last field is the local Lipschitz
condition imposed on the Hessian. -/
structure AssumptionH (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (Φ : H → ℝ) : Prop where
  bounded_below : ∃ m : ℝ, ∀ x, m ≤ Φ x
  twice_continuously_differentiable : ContDiff ℝ 2 Φ
  hessian_lipschitz_on_bounded :
    ∀ R : ℝ, 0 < R → ∃ L : ℝ, 0 < L ∧ ∀ x y, ‖x‖ ≤ R → ‖y‖ ≤ R →
      ‖fderiv ℝ (gradient Φ) x - fderiv ℝ (gradient Φ) y‖ ≤ L * ‖x - y‖

end Alvarez2002
