import Foundation.SetValued.Resolvent
import TheoremLib.Alvarez_Attouch_Inertial_proximal_maximal_monotone_operators_2001.items.def_2

namespace AlvarezAttouch2001

open scoped Pointwise
open SetValuedOperator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The recurrence defining the inertial proximal point algorithm. -/
structure InertialProximalPointAlgorithm (A : SetValuedOperator H H)
    (x : ℕ → H) (alpha lambda : ℕ → ℝ) : Prop where
  alpha_mem : ∀ k : ℕ, 0 ≤ alpha k ∧ alpha k < 1
  lambda_pos : ∀ k : ℕ, 0 < lambda k
  update : ∀ k : ℕ, 1 ≤ k →
    x (k + 1) ∈ (lambda k • A).resolvent (x k + alpha k • (x k - x (k - 1)))

end AlvarezAttouch2001
