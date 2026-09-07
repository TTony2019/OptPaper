import Mathlib.Analysis.InnerProductSpace.PiL2

open Set
open scoped RealInnerProductSpace

/-- The subdifferential `∂g(x)` of a convex function `g : ℝⁿ → ℝ` at a point `x`.
A vector `γ` belongs to `∂g(x)` if it satisfies the subgradient inequality:
`g(y) ≥ g(x) + ⟨γ, y - x⟩` for all `y`. -/
def subdifferential {n : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  {γ | ∀ y, g x + ⟪γ, y - x⟫ ≤ g y}
