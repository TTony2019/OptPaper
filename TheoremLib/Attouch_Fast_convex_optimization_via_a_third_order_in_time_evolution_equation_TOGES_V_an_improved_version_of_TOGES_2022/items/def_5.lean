import Mathlib

/-- The strongly convex third-order evolution equation (24). -/
def IsStronglyConvexThirdOrderEvolution {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u uDot uDdot uDddot : ℝ → H) (grad : H → H) (mu : ℝ) : Prop :=
  0 < mu ∧ ∀ t : ℝ,
    uDddot t + (3 * Real.sqrt mu) • uDdot t + (2 * mu) • uDot t +
      Real.sqrt mu • grad (u t + (Real.sqrt mu)⁻¹ • uDot t) = 0
