import Mathlib
import Foundation.Projection.BestApproximation
namespace Alvarez2002
open scoped RealInnerProductSpace
/-- Projection membership together with its variational characterization. -/
def IsMetricProjection {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (C : Set H) (_hC : C.Nonempty) (_hclosed : IsClosed C) (_hconvex : Convex ℝ C) (u p : H) : Prop := IsBestApproximation u C p ∧
  ∀ v ∈ C, ⟪v - p, u - p⟫ ≤ 0
end Alvarez2002
