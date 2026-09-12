import Mathlib
import Foundation.Convex.Basic
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.ext_def_2

open scoped InnerProductSpace

open ERealFunction

namespace Nesterov1983

/-- The data and standing assumptions of extremal problem (8). -/
structure ExtremalProblem (m : ℕ) (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  Q : Set E
  Q_convex : Convex ℝ Q
  Q_closed : IsClosed Q
  F : EuclideanSpace ℝ (Fin m) → ℝ
  F_convex : ConvexOn ℝ Set.univ F
  F_homogeneous : PositivelyHomogeneous F
  f : Fin m → E → ℝ
  f_convex : ∀ i, ConvexOn ℝ Set.univ (f i)
  f_continuouslyDifferentiable : ∀ i, ContDiff ℝ 1 (f i)
  solutionSet : Set E
  solutions_nonempty : solutionSet.Nonempty
  solution_iff : ∀ x, x ∈ solutionSet ↔ x ∈ Q ∧
    ∀ z ∈ Q, F (WithLp.toLp 2 (fun i => f i x)) ≤ F (WithLp.toLp 2 (fun i => f i z))
  negative_multiplier_linear : ∀ l ∈ subdifferential (fun y => (F y : EReal)) 0, ∀ i,
    l i < 0 → ∃ g : E →ₗ[ℝ] ℝ, ∀ x, f i x = g x

end Nesterov1983
