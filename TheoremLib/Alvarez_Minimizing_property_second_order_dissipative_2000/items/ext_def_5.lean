import Foundation.Topology.Sequences

namespace Alvarez2000

open Filter

/-- A weak limit point of a trajectory, represented by a sequence of times tending to infinity. -/
def IsWeakLimitPoint {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : ℝ → H) (y : H) : Prop :=
  ∃ t : ℕ → ℝ, Tendsto t Filter.atTop Filter.atTop ∧
    Tendsto (fun k => toWeakSpace ℝ H (u (t k))) Filter.atTop
      (nhds (toWeakSpace ℝ H y))

end Alvarez2000
