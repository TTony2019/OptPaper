import Mathlib
namespace Alvarez2002
/-- The Hessian-driven inertial equation `(DIN)` on the forward time half-line. -/
def IsDINTrajectory (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (Φ : H → ℝ) (α β : ℝ) (x : ℝ → H) : Prop :=
  0 < α ∧ 0 < β ∧
    ∀ t, 0 ≤ t → deriv (deriv x) t + α • deriv x t +
      β • (fderiv ℝ (gradient Φ) (x t)) (deriv x t) + gradient Φ (x t) = 0
end Alvarez2002
