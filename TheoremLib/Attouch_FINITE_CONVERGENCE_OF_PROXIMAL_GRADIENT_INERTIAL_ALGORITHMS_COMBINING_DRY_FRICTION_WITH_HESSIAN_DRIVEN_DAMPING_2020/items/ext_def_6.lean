import Mathlib

/-- Scalar soft thresholding. -/
noncomputable def softThreshold (a : ℝ) (_ha : 0 ≤ a) (t : ℝ) : ℝ :=
  Real.sign t * max (|t| - a) 0
