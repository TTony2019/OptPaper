import Mathlib

/-- The TOGES third-order evolution equation from the preceding paper.

The damping term is the second derivative and the singular term is the first
derivative of the trajectory. -/
def IsTOGES {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [InnerProductSpace ℝ H]
  [CompleteSpace H] (alpha : ℝ) (u : ℝ → H) (f : H → ℝ) (t0 : ℝ) : Prop :=
  ∀ t : ℝ, t ≥ t0 →
    deriv (deriv (deriv u)) t + ((3 * alpha + 5) / (2 * t)) • deriv (deriv u) t +
      ((3 * alpha - 1) / t ^ 2) • deriv u t +
      gradient f (u t + t • deriv u t) = 0
