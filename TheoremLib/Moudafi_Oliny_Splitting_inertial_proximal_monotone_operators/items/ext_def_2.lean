import Mathlib
import Foundation.SetValued.Basic

/-!
# Sum of two set-valued operators

For two set-valued operators `A, B : H ⇉ H`, their sum `A + B` is defined by
`(A + B)(x) := {a + b : a ∈ A(x), b ∈ B(x)}`.

This is the pointwise lift of `Set.add` to set-valued maps.
-/

open SetValuedOperator
open scoped Pointwise

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [InnerProductSpace ℝ H] in
/-- The sum of two set-valued operators, defined pointwise:
`(A + B)(x) = {a + b | a ∈ A(x), b ∈ B(x)}`. -/
theorem sum_apply (A B : SetValuedOperator H H) (x : H) : (A + B) x = A x + B x := rfl

omit [InnerProductSpace ℝ H] in
/-- Membership in the sum: `w ∈ (A + B)(x) ↔ ∃ a ∈ A(x), ∃ b ∈ B(x), w = a + b`. -/
theorem mem_sum_iff (A B : SetValuedOperator H H) (x : H) (w : H) :
    w ∈ (A + B) x ↔ ∃ a ∈ A x, ∃ b ∈ B x, w = a + b := by
  simpa [sum_apply, eq_comm] using Set.mem_add
