import Mathlib


/-- The TOGES-V third-order evolution equation from (TOGES-V).

The derivatives are the derivatives of the trajectory itself; in particular the
leading term is the third derivative and the two damping terms use the second
and first derivatives, respectively. -/
def IsTOGESV {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [InnerProductSpace ℝ H] [CompleteSpace H] (alpha : ℝ) (u : ℝ → H) (f : H → ℝ)
  (t0 : ℝ) : Prop :=
  ∀ t : ℝ, t ≥ t0 →
    deriv (deriv (deriv u)) t + ((alpha + 7) / t) • deriv (deriv u) t +
      (5 * (alpha + 1) / t ^ 2) • deriv u t +
      gradient f (u t + (t / 4) • deriv u t) = 0
