import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_1
import Mathlib

open scoped InnerProductSpace

open ERealFunction

/-- The dry-friction property: convexity, continuity, zero minimum, and an interior subgradient. -/
structure DryFriction {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (phi : H → ℝ) : Prop where
  convex : ConvexOn ℝ Set.univ phi
  continuous : Continuous phi
  minimum_at_zero : ∀ x, phi 0 ≤ phi x
  value_at_zero : phi 0 = 0
  interior_subgradient : (0 : H) ∈ interior (subdifferential phi 0)
