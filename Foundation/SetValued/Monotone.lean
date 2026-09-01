import Mathlib.Analysis.InnerProductSpace.Basic
import Foundation.SetValued.Basic

/-!
# Set-valued monotonicity

Core predicates for monotone and maximal monotone set-valued operators.
Operations built from these predicates live in the specialized modules.
-/

namespace SetValuedOperator

universe u

variable {H : Type u}

/-- A set-valued operator `A : H ⇉ H` is monotone if for all `x, y ∈ H`, `u ∈ A x`,
and `v ∈ A y`, we have `⟪u - v, x - y⟫ ≥ 0`. -/
def IsMonotone [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : SetValuedOperator H H) : Prop :=
  ∀ {x y : H}, ∀ u ∈ A x, ∀ v ∈ A y, 0 ≤ inner ℝ (u - v) (x - y)

/-- A set-valued operator `A` is maximal monotone if it is monotone and every monotone
extension has graph contained in the graph of `A`. -/
def IsMaximalMonotone [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : SetValuedOperator H H) : Prop :=
  IsMonotone A ∧
  ∀ (A' : SetValuedOperator H H), IsMonotone A' → A.graph ⊆ A'.graph →
    A'.graph ⊆ A.graph

/-! The order-theoretic maximality owner is equivalent to the graph formulation above. -/

theorem isMaximalMonotone_iff_maximal_isMonotone
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (A : SetValuedOperator H H) :
    IsMaximalMonotone A ↔ Maximal IsMonotone A := by
  constructor
  · intro hA
    refine ⟨hA.1, ?_⟩
    intro B hB hAB x u hu
    have hAB_graph : A.graph ⊆ B.graph := by
      intro p hp
      rcases p with ⟨y, v⟩
      exact hAB y hp
    have hBA_graph := hA.2 B hB hAB_graph
    exact hBA_graph (SetValuedOperator.mem_graph_iff B x u |>.mpr hu)
  · intro hA
    refine ⟨hA.1, ?_⟩
    intro B hB hAB
    intro p hp
    rcases p with ⟨x, u⟩
    change u ∈ B x at hp
    change u ∈ A x
    have hAB_point : A ≤ B := by
      intro y v hv
      exact hAB (SetValuedOperator.mem_graph_iff A y v |>.mpr hv)
    exact hA.2 hB hAB_point x hp

end SetValuedOperator
