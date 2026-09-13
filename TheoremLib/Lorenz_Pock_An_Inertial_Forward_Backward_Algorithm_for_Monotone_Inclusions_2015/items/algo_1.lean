import Mathlib
import Foundation.SetValued.Resolvent
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.def_1
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.ext_def_1

open scoped Pointwise

namespace LorenzPock

/-- The inertial forward--backward iteration (10), expressed through membership in the
resolvent relation. -/
structure InertialForwardBackwardIteration (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (A : SetValuedOperator H H) (B : H → H)
    (M : H →L[ℝ] H) (α ell : ℕ → ℝ) where
  x : ℕ → H
  y : ℕ → H
  inertia_range : ∀ k, 0 ≤ α k ∧ α k < 1
  metric_self_adjoint : ∀ u v, inner ℝ (M u) v = inner ℝ u (M v)
  metric_positive_definite : ∀ u, u ≠ 0 → 0 < inner ℝ (M u) u
  inertial : ∀ k, y k = x k + α k • (x k - x (k - 1))
  forward_backward : ∀ k, ∃ a ∈ A (x (k + 1)),
    M (y k - x (k + 1)) - ell k • B (y k) = ell k • a

end LorenzPock
