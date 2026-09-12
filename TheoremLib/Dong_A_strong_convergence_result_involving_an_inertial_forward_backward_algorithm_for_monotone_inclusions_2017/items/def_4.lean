import Mathlib.Tactic
import Foundation.SetValued.Monotone
import Foundation.FixedPoint.Nonexpansive

/-! Definition 2.3: monotone, strongly monotone, and inverse strongly monotone operators. -/

recall SetValuedOperator.IsMonotone
recall SetValuedOperator.IsMaximalMonotone
recall CocoerciveOn

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A single-valued operator is strongly monotone on `D` with modulus `beta`. -/
def IsStronglyMonotoneOn (beta : ℝ) (D : Set H) (A : D → H) : Prop :=
  0 < beta ∧ ∀ x y : D, beta * ‖(x : H) - y‖ ^ 2 ≤ inner ℝ ((x : H) - y) (A x - A y)
