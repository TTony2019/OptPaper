import Mathlib.Tactic
import Foundation.SetValued.Monotone

/-!
# Maximal monotone operator

An operator `T` is said to be maximal monotone if it is monotone and its graph is not
properly contained in the graph of any other monotone operator.
-/

open SetValuedOperator

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A set-valued operator `T` is maximal monotone if it is monotone and its graph
is maximal among graphs of monotone operators. -/
recall SetValuedOperator.IsMaximalMonotone
