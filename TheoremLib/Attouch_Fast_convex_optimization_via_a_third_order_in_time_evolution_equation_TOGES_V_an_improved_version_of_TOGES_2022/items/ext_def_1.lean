import Mathlib
import Foundation.Convex.Basic

/-- A convex differentiable objective together with its first-order convexity inequality. -/
structure ConvexDifferentiableObjective (H : Type*) [NormedAddCommGroup H]
    [NormedSpace ℝ H] [InnerProductSpace ℝ H] [CompleteSpace H] where
  f : H → ℝ
  differentiable : ∀ x : H, DifferentiableAt ℝ f x
  convex : ∀ x y : H, ∀ s : ℝ, 0 ≤ s → s ≤ 1 →
    f ((1 - s) • x + s • y) ≤ (1 - s) * f x + s * f y
  firstOrder : ∀ x y : H, f y ≥ f x + inner ℝ (gradient f x) (y - x)
