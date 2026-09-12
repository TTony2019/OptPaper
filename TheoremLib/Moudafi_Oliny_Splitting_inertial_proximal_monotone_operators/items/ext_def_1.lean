import Mathlib.Tactic
import Foundation.SetValued.Basic

/-!
# Graph of a set-valued operator

The graph of a set-valued operator `T : H ⇉ H` on a Hilbert space `H` is the set
`gra T := {(x, y) ∈ H × H : y ∈ T(x)}`.
-/

/-- The graph of a set-valued operator. -/
recall SetValuedOperator.graph
