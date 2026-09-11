import Foundation.SetValued.Monotone

open scoped InnerProductSpace

namespace BurachikSvaiterRobustnessHPE2001

/-- The normality operator with the sign convention used in the paper. -/
def normalityOperator {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) : SetValuedOperator H H := by
  classical
  exact fun z ↦ if z ∈ C then {w | ∀ u ∈ C, inner ℝ w (z - u) ≥ 0} else ∅

end BurachikSvaiterRobustnessHPE2001
