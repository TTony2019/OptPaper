import Mathlib


/-- The TOGES-V third-order evolution equation. -/
def IsTOGESV {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u uDot uDdot uDddot : ℝ → H) (grad : H → H) (alpha : ℝ) : Prop :=
  ∀ t : ℝ, t ≠ 0 →
    uDddot t + ((alpha + 7) / t) • uDdot t + (5 * (alpha + 1) / t ^ 2) • uDot t +
      grad (u t + (t / 4) • uDot t) = 0
