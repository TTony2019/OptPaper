import Mathlib
import Foundation.SetValued.Basic
import TheoremLib.Moudafi_Oliny_Splitting_inertial_proximal_monotone_operators.items.ext_def_2
import TheoremLib.Moudafi_Oliny_Splitting_inertial_proximal_monotone_operators.items.ext_def_3

/-!
# β-cocoercivity with respect to the solution set

An operator `B` is said to be β-cocoercive with respect to the solution set
`S := (A + B)⁻¹(0)` if
`⟨B(x) - B(y), x - y⟩ ≥ β|B(x) - B(y)|²` for all `x ∈ H`, `y ∈ S`,
where `β > 0` is a real number.
-/

open SetValuedOperator
open scoped InnerProductSpace Pointwise

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Embedding of a single-valued map `f : H → H` as a set-valued operator:
`x ↦ {f x}`. -/
def svEmbed (f : H → H) : SetValuedOperator H H := fun x ↦ {f x}

/-- A single-valued operator `B : H → H` is β-cocoercive with respect to the
set-valued operator `A` and the solution set `S := (A + B)⁻¹(0)` if
`⟨B(x) - B(y), x - y⟩ ≥ β‖B(x) - B(y)‖²` for all `x ∈ H`, `y ∈ S`,
where `β > 0`. -/
def IsCocoerciveWRT (A : SetValuedOperator H H) (B : H → H) (β : ℝ) : Prop :=
  0 < β ∧ ∀ x, ∀ y ∈ ((A + svEmbed B).zeros), β * ‖B x - B y‖ ^ 2 ≤ ⟪B x - B y, x - y⟫_ℝ
