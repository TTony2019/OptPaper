import Mathlib

namespace Alvarez2000

/-- Assumption `(h_Phi)`: a continuously differentiable convex potential bounded below. -/
structure HasPotentialAssumption {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Phi : H → ℝ) where
  contDiff : ContDiff ℝ 1 Phi
  convex : ConvexOn ℝ Set.univ Phi
  bounded_below : ∃ m : ℝ, ∀ x : H, m ≤ Phi x

end Alvarez2000
