import Mathlib
import Foundation.SetValued.Basic
import TheoremLib.Moudafi_Oliny_Splitting_inertial_proximal_monotone_operators.items.def_1

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

/-- The ε-enlargement of a set-valued operator `T`. For ε ≥ 0,
`T_ε(x) := {v ∈ H : ⟨u - v, y - x⟩ ≥ -ε ∀ y, ∀ u ∈ T(y)}`. -/
def enlargement (T : SetValuedOperator H H) (ε : ℝ) : SetValuedOperator H H :=
  fun x ↦ {v | ∀ y, ∀ u ∈ T y, -ε ≤ ⟪u - v, y - x⟫_ℝ}

/-- Monotonicity of the enlargement with respect to ε:
if `ε₁ ≤ ε₂`, then `T_{ε₁}(x) ⊆ T_{ε₂}(x)` for all `x`. -/
theorem enlargement_monotone (T : SetValuedOperator H H) {ε₁ ε₂ : ℝ}
    (hε : ε₁ ≤ ε₂) (x : H) : enlargement T ε₁ x ⊆ enlargement T ε₂ x := by
  intro v hv
  rw [enlargement, Set.mem_setOf_eq] at hv ⊢
  intro y u hu
  have h := hv y u hu
  linarith
