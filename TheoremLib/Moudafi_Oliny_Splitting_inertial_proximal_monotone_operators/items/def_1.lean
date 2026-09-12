import Mathlib.Tactic
import Foundation.SetValued.Monotone

/-!
# Monotone operator

An operator `T` on a real Hilbert space `H` is said to be monotone if
`⟪u - v, x - y⟫_ℝ ≥ 0` whenever `u ∈ T(x)`, `v ∈ T(y)`.
-/

open SetValuedOperator
open scoped InnerProductSpace

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A set-valued operator `T : H ⇉ H` is monotone if for all `x, y` and all
`u ∈ T x`, `v ∈ T y`, we have `⟪u - v, x - y⟫_ℝ ≥ 0`. -/
recall SetValuedOperator.IsMonotone
