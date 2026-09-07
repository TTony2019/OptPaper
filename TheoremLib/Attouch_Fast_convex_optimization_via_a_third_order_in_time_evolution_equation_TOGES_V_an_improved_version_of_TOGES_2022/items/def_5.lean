import Mathlib

/-- The strongly convex third-order evolution equation (24). -/
def IsStronglyConvexThirdOrderEvolution {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [InnerProductSpace ℝ H] [CompleteSpace H]
  (u : ℝ → H) (mu : ℝ) (f : H → ℝ) : Prop :=
  0 < mu ∧ ∀ t : ℝ,
    deriv (deriv (deriv u)) t + (3 * Real.sqrt mu) • (deriv (deriv u)) t + (2 * mu) • (deriv u) t +
      Real.sqrt mu • gradient f (u t + (Real.sqrt mu)⁻¹ • (deriv u) t) = 0
