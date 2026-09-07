import Mathlib
import Foundation.Projection.BestApproximation
namespace Alvarez2002
/-- The constrained first-order system `(c-DIN)`. -/
structure ConstrainedHypothesis {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] (C : Set H) (Φ : H → ℝ) : Prop where
  nonempty : C.Nonempty
  closed : IsClosed C
  convex : Convex ℝ C
  open_neighborhood : ∃ U : Set H, IsOpen U ∧ C ⊆ U
  continuously_differentiable_on_neighborhood : ∃ U : Set H, IsOpen U ∧ C ⊆ U ∧ ContDiffOn ℝ 1 Φ U
  bounded_below : ∃ m : ℝ, ∀ x ∈ C, m ≤ Φ x
  gradient_lipschitz_on_bounded : ∀ R : ℝ, ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ C, ∀ y ∈ C,
    ‖x‖ ≤ R → ‖y‖ ≤ R → ‖gradient Φ x - gradient Φ y‖ ≤ L * ‖x - y‖


noncomputable def IsConstrainedDINTrajectory {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℝ H] [CompleteSpace H] (C : Set H) (Φ : H → ℝ)
  (hC : ConstrainedHypothesis C Φ)
  (β a b : ℝ) (x₀ y₀ : H) (x y : ℝ → H) : Prop :=
  0 < β ∧ a ≠ 0 ∧ 0 < b ∧ 0 < b + a ∧ x 0 = x₀ ∧ x₀ ∈ C ∧ y 0 = y₀ ∧
  ∀ t, t ≥ 0 → deriv x t + x t - projectionPoint C
        (isChebyshev_of_nonempty_isClosed_convex hC.nonempty hC.closed hC.convex)
        (x t - β • gradient Φ (x t) - a • x t - b • y t) = 0 ∧
    deriv y t + a • x t + b • y t = 0


noncomputable def constrainedEnergy {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (Φ : H → ℝ) (a b ell : ℝ) (x y : H) : ℝ := ell * Φ x + (1 / 2) * ‖a • x + b • y‖ ^ 2


end Alvarez2002
