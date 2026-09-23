import Mathlib
import Foundation.SetValued.Enlargement

/-!
# ε-enlargement of a monotone operator

For a monotone operator `T` and `ε ≥ 0`, the ε-enlargement `T_ε` is defined by
`T_ε(x) := {v ∈ H : ⟨u - v, y - x⟩ ≥ -ε ∀ y, ∀ u ∈ T(y)}`.

Since `T` is assumed to be maximal monotone, `T_0(x) = T(x)` for any `x`.
Furthermore, directly from the definition it follows that
`0 ≤ ε₁ ≤ ε₂ ⇒ T_{ε₁}(x) ⊂ T_{ε₂}(x)`.
-/

open SetValuedOperator
open scoped InnerProductSpace

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/- The definition and its monotonicity theorem now live in Foundation. -/
recall enlargement
recall enlargement_monotone
