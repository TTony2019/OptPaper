import Foundation.SetValued.Basic
import Mathlib.Tactic

/-! The pointwise (Minkowski) sum of two set-valued operators is the canonical `+` on the
function type `SetValuedOperator X Y = X → Set Y` (pointwise set addition), whose membership is
`Set.mem_add`.  Foundation records the combined sum and scalar-multiple form of this operation in
`SetValuedOperator.mem_add_smul_iff`. -/
recall Set.mem_add
recall SetValuedOperator.mem_add_smul_iff
