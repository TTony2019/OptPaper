import Mathlib.Tactic
import Foundation.SetValued.Resolvent

open scoped Pointwise

/-!
# Resolvent of a maximal monotone operator

For a maximal monotone operator `T`, for each `x ∈ H` and `λ > 0` there is a unique
`z ∈ H` such that `x ∈ (I + λT)z`. The single-valued operator
`J_λ^T := (I + λT)⁻¹` is called the resolvent of `T` of parameter `λ`.

It is a nonexpansive mapping which is everywhere defined and satisfies:
`z = J_λ^T z` if and only if `0 ∈ Tz`.
-/

open SetValuedOperator
open scoped InnerProductSpace

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The resolvent of a set-valued operator `T` with parameter `lam > 0`:
`J_lam^T := (I + lam • T)⁻¹` where `(I + lam • T)(z) = {z + lam • v | v ∈ T(z)}`. -/
recall SetValuedOperator.resolvent
