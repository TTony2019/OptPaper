import Mathlib.Tactic
import Foundation.SetValued.Basic

/-!
# Inverse of a set-valued operator

For a set-valued operator `T : H ⇉ H`, its inverse `T⁻¹` is defined by
`T⁻¹(y) := {x ∈ H : y ∈ T(x)}`.
-/

/-- The inverse of a set-valued operator. -/
recall SetValuedOperator.inverse
