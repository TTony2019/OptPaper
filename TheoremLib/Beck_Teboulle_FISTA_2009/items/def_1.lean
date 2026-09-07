import Mathlib.Data.Real.Basic

/-- The positive part of a real number: `max{a, 0}`.
This matches the paper's notation `(a)_+` used in the shrinkage operator definition. -/
def positivePart (a : ℝ) : ℝ :=
  max a 0
