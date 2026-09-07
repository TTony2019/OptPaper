import Foundation.Operator.Linear

namespace Alvarez2000

open scoped InnerProductSpace

/-- Assumption `(h_Gamma)`: the damping operator is coercive. -/
def HasCoerciveDamping {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Gamma : H →L[ℝ] H) : Prop :=
  ∃ gamma : ℝ, 0 < gamma ∧ ∀ x : H, gamma * ‖x‖ ^ 2 ≤ ⟪Gamma x, x⟫_ℝ

end Alvarez2000
