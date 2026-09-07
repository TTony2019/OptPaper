import Mathlib
import Foundation.Operator.Linear

/-- Strong convexity in the first-order form used by the paper. -/
def IsStronglyConvexDifferentiable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (mu : ℝ) : Prop :=
  0 < mu ∧ ∀ x y : H, f y ≥ f x + inner ℝ (gradient f x) (y - x) +
    (mu / 2) * ‖y - x‖ ^ 2
