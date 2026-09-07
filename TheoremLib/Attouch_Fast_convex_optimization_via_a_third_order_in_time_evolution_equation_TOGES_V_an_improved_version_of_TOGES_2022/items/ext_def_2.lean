import Mathlib
import Foundation.Operator.Linear

/-- Strong convexity in the first-order form used by the paper. -/
def IsStronglyConvexDifferentiable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (grad : H → H) (mu : ℝ) : Prop :=
  0 < mu ∧ ∀ x y : H, f y ≥ f x + inner ℝ (grad x) (y - x) + (mu / 2) * ‖y - x‖ ^ 2
