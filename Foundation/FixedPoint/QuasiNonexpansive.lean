import Mathlib
import Foundation.FixedPoint.Nonexpansive

/-!
# Quasi-nonexpansive variants

α-averaged quasi-nonexpansive and δ-attracting quasi-nonexpansive mappings on a real
Hilbert space. These refine the basic quasi-nonexpansive property with quantitative
control on how much a point moves toward fixed points.

Reference: P.-E. Maingé, "Inertial Iterative Process for Fixed Points of Certain
Quasi-nonexpansive Mappings", Set-Valued Anal. 15 (2007), 67–79.
-/

open Set

section Quasinonexpansive

variable {H : Type*} [NormedAddCommGroup H]

/-- A whole-space quasi-nonexpansive map: `‖T x - q‖ ≤ ‖x - q‖` for all `x` and all
fixed points `q`. This is `QuasinonexpansiveOn Set.univ`. -/
abbrev Quasinonexpansive (T : H → H) : Prop :=
  QuasinonexpansiveOn Set.univ T

end Quasinonexpansive

section AveragedQuasinonexpansive

variable {H : Type*} [NormedAddCommGroup H] [Module ℝ H]

/-- A mapping `T : H → H` is `α`-averaged quasi-nonexpansive (where `α ∈ [0, 1)`)
if there exists a quasi-nonexpansive mapping `N : H → H` such that
`T = (1 - α) I + α N`. -/
def IsAlphaAveragedQuasiNonexpansive (α : ℝ) (T : H → H) : Prop :=
  α ∈ Set.Ico (0 : ℝ) 1 ∧
  ∃ (N : H → H), Quasinonexpansive N ∧ T = (fun x => ((1 : ℝ) - α) • x + α • N x)

end AveragedQuasinonexpansive

section AttractingQuasinonexpansive

variable {H : Type*} [NormedAddCommGroup H]

/-- A mapping `T : H → H` is `δ`-attracting quasi-nonexpansive (`δ ≥ 0`) if
`‖x - q‖² - ‖T x - q‖² ≥ δ * ‖x - T x‖²` for all `x ∈ H` and `q ∈ Fix(T)`. -/
def IsDeltaAttractingQuasiNonexpansive (δ : ℝ) (T : H → H) : Prop :=
  0 ≤ δ ∧
  ∀ (x q : H), q ∈ Function.fixedPoints T → δ * ‖x - T x‖ ^ 2 ≤ ‖x - q‖ ^ 2 - ‖T x - q‖ ^ 2

end AttractingQuasinonexpansive
