import Mathlib.Tactic
import Foundation.SetValued.Basic

/-! The pointwise sum of a single-valued and a set-valued operator. -/

open SetValuedOperator

variable {H : Type*} [AddCommGroup H]

/-- `(A + B)(x) = {A x + b | b ∈ B x}`. -/
def operatorSum (A : H → H) (B : SetValuedOperator H H) : SetValuedOperator H H :=
  fun x ↦ {u | ∃ b ∈ B x, u = A x + b}

/-- The paper's notation `(A + B)⁻¹(0)`. -/
def operatorSumZeroSet (A : H → H) (B : SetValuedOperator H H) : Set H :=
  (operatorSum A B).zeros
