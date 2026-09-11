import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.algo_1
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.cor_1
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.ext_lem_1

open Filter

namespace BurachikSvaiterRobustnessHPE2001

/-- Corollary 3.2: distances to any zero have a nonnegative limit. -/
theorem hpe_distance_converges {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : SetValuedOperator H H} (A : HPEIterates H T) {xStar : H}
    (hxStar : (0 : H) ∈ T xStar) :
    ∃ L : ℝ, 0 ≤ L ∧ Tendsto (fun k ↦ ‖A.x k - xStar‖) Filter.atTop (nhds L) := by
  refine polyak_scalar_convergence A.α A.δ (fun k ↦ ‖A.x k - xStar‖)
    A.α_nonneg A.δ_nonneg (fun k ↦ norm_nonneg _) A.summable_alpha A.summable_delta ?_
  intro k
  exact hpe_distance_bound A hxStar k

end BurachikSvaiterRobustnessHPE2001
