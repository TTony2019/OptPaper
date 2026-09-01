import Mathlib

namespace AbbasDynamical2015

open scoped Gradient

/-- Gradient-projection dynamics (81) on a closed convex set. -/
structure GradientProjectionDynamics {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Psi : H → ℝ) (C : Set H) (tangentCone : H → Set H)
    (projection : H → Set H → H) where
  closed_convex : IsClosed C ∧ Convex ℝ C
  x : ℝ → H
  path_in_constraint : ∀ t, 0 ≤ t → x t ∈ C
  tangent_cone_at_path : ∀ t, 0 ≤ t → tangentCone (x t) = tangentConeAt ℝ C (x t)
  projection_mem : ∀ t, 0 ≤ t →
    projection (-(∇ Psi (x t))) (tangentCone (x t)) ∈ tangentCone (x t)
  projection_min_dist : ∀ t, 0 ≤ t → ∀ z ∈ tangentCone (x t),
    ‖-(∇ Psi (x t)) - projection (-(∇ Psi (x t))) (tangentCone (x t))‖ ≤
      ‖-(∇ Psi (x t)) - z‖
  differential_equation : ∀ t, 0 ≤ t →
    deriv x t = projection (-(∇ Psi (x t))) (tangentCone (x t))

end AbbasDynamical2015
