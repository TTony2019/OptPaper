import Mathlib
namespace Alvarez2002
/-- The generalized first-order system `(g-DIN)`. -/
def IsSolution_gDIN {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
 [InnerProductSpace ℝ H] [CompleteSpace H] (Φ : H → ℝ) (β a b : ℝ) (x₀ y₀ : H)
 (x y : ℝ → H) :=
 (∀ t, 0 ≤ t → deriv x t + β • gradient Φ (x t) + a • x t + b • y t = 0) ∧
 (∀ t, 0 ≤ t → deriv y t + a • x t + b • y t = 0) ∧
 (x 0 = x₀) ∧ (y 0 = y₀)
end Alvarez2002
