import Mathlib

/-- The third-order TOGES evolution equation, preserving the source's two acceleration terms. -/
def IsTOGES {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u uDot uDdot : ℝ → H) (grad : H → H) (alpha : ℝ) : Prop :=
  ∀ t : ℝ, t ≠ 0 →
    uDdot t + ((3 * alpha + 5) / (2 * t)) • uDdot t + ((3 * alpha - 1) / t ^ 2) • uDot t +
      grad (u t + t • uDot t) = 0
