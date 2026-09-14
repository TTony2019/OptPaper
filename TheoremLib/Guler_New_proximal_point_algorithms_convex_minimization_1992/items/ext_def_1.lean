import Mathlib.Tactic
import Foundation.Analysis.ExtendedRealFunctions

/-- The paper's standing assumption on an extended-real-valued objective. -/
def ObjectiveAssumptions {H : Type*} [AddCommMonoid H] [Module ℝ H] [TopologicalSpace H]
    (f : H → EReal) : Prop :=
  ERealFunction.IsProper f ∧ Convex ℝ (ERealFunction.epigraph f) ∧ LowerSemicontinuous f

/-- A feasible point is one at which the objective is finite above. -/
def IsFeasible {H : Type*} (f : H → EReal) (x : H) : Prop := f x < ⊤
