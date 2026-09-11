import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.lem_2
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.lem_3

open Filter
open scoped Topology

namespace BurachikSvaiterRobustnessHPE2001

/-- Theorem 3.1: weak convergence in the feasible case and unboundedness otherwise. -/
theorem hpe_main_theorem {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {T : SetValuedOperator H H}
    (hT : T.IsMaximalMonotone) (A : HPEIterates H T) :
    (∃ xStar, (0 : H) ∈ T xStar ∧
      Tendsto (fun k ↦ toWeakSpace ℝ H (A.x k)) atTop
        (nhds (toWeakSpace ℝ H xStar))) ∨
    (T.zeros = ∅ ∧ ¬ Bornology.IsBounded (Set.range A.x)) := by
  classical
  by_cases hzeros : T.zeros = ∅
  · exact Or.inr ⟨hzeros, hpe_unbounded_of_no_zero hT A hzeros⟩
  · rcases Set.nonempty_iff_ne_empty.mpr hzeros with ⟨xStar, hxStar⟩
    have hzero : ∃ xStar, (0 : H) ∈ T xStar :=
      ⟨xStar, SetValuedOperator.mem_zeros_iff T xStar |>.mp hxStar⟩
    exact Or.inl (hpe_weakly_converges_to_zero hT A hzero)

end BurachikSvaiterRobustnessHPE2001
