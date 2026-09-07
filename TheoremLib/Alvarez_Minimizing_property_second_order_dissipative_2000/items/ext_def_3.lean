import Foundation.Analysis.ExtendedRealFunctions

namespace Alvarez2000

open scoped InnerProductSpace

/-- The epsilon-subdifferential is the approximate subgradient relation. -/
def epsilonSubdifferential {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (eps : ℝ) (x : H) : Set H :=
  {p | ∀ y : H, f y ≥ f x + (⟪p, y - x⟫_ℝ : EReal) - eps}

end Alvarez2000
