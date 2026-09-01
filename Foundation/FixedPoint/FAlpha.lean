import Mathlib

/-!
# Class ℱ_α

The class `ℱ_α` introduced by Maingé (2007): self-mappings of a real Hilbert space
satisfying a lower bound on the inner product between the residual `x - T x` and the
direction to any fixed point.

For `α ∈ (0, 1]`, a mapping `T : H → H` belongs to `ℱ_α` if for all `x ∈ H` and
`q ∈ Fix(T)`:

`‖x - T x‖² / (2α) ≤ ⟪x - T x, x - q⟫`

This class is central to the convergence analysis of inertial iteration methods.

Reference: P.-E. Maingé, "Inertial Iterative Process for Fixed Points of Certain
Quasi-nonexpansive Mappings", Set-Valued Anal. 15 (2007), 67–79.
-/

open Set
open scoped RealInnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A mapping `T : H → H` belongs to the class `ℱ_α` (for `α ∈ (0, 1]`) if for all
`x ∈ H` and `q ∈ Fix(T)`, we have `(1/(2α)) * ‖x - T x‖² ≤ ⟪x - T x, x - q⟫`. -/
def IsInFAlpha (α : ℝ) (T : H → H) : Prop :=
  0 < α ∧ α ≤ 1 ∧
  ∀ (x q : H), q ∈ Function.fixedPoints T → ((1 : ℝ) / (2 * α)) * ‖x - T x‖ ^ 2 ≤ ⟪x - T x, x - q⟫
