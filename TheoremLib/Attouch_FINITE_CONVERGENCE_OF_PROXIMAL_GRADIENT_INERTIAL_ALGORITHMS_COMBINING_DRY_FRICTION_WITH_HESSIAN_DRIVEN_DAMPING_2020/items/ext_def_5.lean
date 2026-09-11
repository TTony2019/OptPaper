import Mathlib

/-- Extremal eigenvalue data for a positive-definite finite-dimensional matrix. -/
structure ExtremalEigenvalues (n : Type*) [Fintype n] [DecidableEq n]
    (M : Matrix n n ℝ) where
  muMin : ℝ
  muMax : ℝ
  symmetric : M.IsSymm
  positive_definite : ∀ x : n → ℝ, x ≠ 0 → 0 < dotProduct x (M.mulVec x)
  muMin_pos : 0 < muMin
  ordered : muMin ≤ muMax
  muMin_isLeast : ∀ μ : ℝ, (∃ v : n → ℝ, v ≠ 0 ∧ M.mulVec v = fun i ↦ μ * v i) → muMin ≤ μ
  muMin_isEigenvalue : ∃ v : n → ℝ, v ≠ 0 ∧ M.mulVec v = fun i ↦ muMin * v i
  muMax_isGreatest : ∀ μ : ℝ, (∃ v : n → ℝ, v ≠ 0 ∧ M.mulVec v = fun i ↦ μ * v i) → μ ≤ muMax
  muMax_isEigenvalue : ∃ v : n → ℝ, v ≠ 0 ∧ M.mulVec v = fun i ↦ muMax * v i
