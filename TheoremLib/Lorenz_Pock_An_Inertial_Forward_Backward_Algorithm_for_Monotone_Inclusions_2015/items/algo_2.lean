import Mathlib
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.algo_1

namespace LorenzPock

/-- Fully implicit inertial proximal point iteration. -/
structure FullyImplicitInertialIteration (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (T : SetValuedOperator H H) (Mbar : H →L[ℝ] H)
    (α ell : ℕ → ℝ) where
  x : ℕ → H
  y : ℕ → H
  inertia_range : ∀ k, 0 ≤ α k ∧ α k < 1
  metric_self_adjoint : ∀ u v, inner ℝ (Mbar u) v = inner ℝ u (Mbar v)
  metric_positive_definite : ∀ u, u ≠ 0 → 0 < inner ℝ (Mbar u) u
  inertial : ∀ k, y k = x k + α k • (x k - x (k - 1))
  proximal : ∀ k, ∃ t ∈ T (x (k + 1)), Mbar (y k - x (k + 1)) = ell k • t

end LorenzPock
