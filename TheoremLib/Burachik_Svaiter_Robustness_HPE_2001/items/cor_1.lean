import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.algo_1
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.def_2
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.lem_1

namespace BurachikSvaiterRobustnessHPE2001

/-- Corollary 3.1, equation (16). -/
theorem hpe_distance_bound {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : SetValuedOperator H H} (A : HPEIterates H T) {xStar : H}
    (hxStar : (0 : H) ∈ T xStar) (k : ℕ) :
    ‖A.x (k + 1) - xStar‖ ≤ A.α k + Real.sqrt (‖A.x k - xStar‖ ^ 2 + A.δ k) := by
  let z := extragradientStep A k
  have hupdate : ‖A.x (k + 1) - z‖ ≤ A.α k := by
    simpa [z] using A.update_error k
  let σbar := A.sigma_bound.choose
  have hσbar_lt_one : σbar < 1 := A.sigma_bound.choose_spec.2.1
  have hσ_nonneg : 0 ≤ A.σ k := A.σ_nonneg k
  have hσ_le : A.σ k ≤ σbar := (A.sigma_bound.choose_spec.2.2 k).2
  have hσsq : (A.σ k) ^ 2 ≤ 1 := by
    nlinarith [hσ_nonneg, hσ_le, hσbar_lt_one]
  have hcoeff : 0 ≤ 1 - (A.σ k) ^ 2 := sub_nonneg.mpr hσsq
  have hpenalty : 0 ≤ (1 - (A.σ k) ^ 2) * ‖A.y k - A.x k‖ ^ 2 :=
    mul_nonneg hcoeff (sq_nonneg _)
  have hdescent := hpe_descent A hxStar k
  have hsq : ‖xStar - z‖ ^ 2 ≤ ‖xStar - A.x k‖ ^ 2 + A.δ k := by
    simp only [z]
    nlinarith [hdescent, hpenalty]
  have hz_sqrt : ‖z - xStar‖ ≤ Real.sqrt (‖A.x k - xStar‖ ^ 2 + A.δ k) := by
    have hroot : ‖xStar - z‖ ≤ Real.sqrt (‖xStar - A.x k‖ ^ 2 + A.δ k) := by
      calc
        ‖xStar - z‖ = Real.sqrt (‖xStar - z‖ ^ 2) :=
          (Real.sqrt_sq (norm_nonneg _)).symm
        _ ≤ Real.sqrt (‖xStar - A.x k‖ ^ 2 + A.δ k) := Real.sqrt_le_sqrt hsq
    simpa only [norm_sub_rev] using hroot
  calc
    ‖A.x (k + 1) - xStar‖ = ‖(A.x (k + 1) - z) + (z - xStar)‖ := by
      rw [show A.x (k + 1) - xStar = (A.x (k + 1) - z) + (z - xStar) by abel]
    _ ≤ ‖A.x (k + 1) - z‖ + ‖z - xStar‖ := norm_add_le _ _
    _ ≤ A.α k + Real.sqrt (‖A.x k - xStar‖ ^ 2 + A.δ k) :=
      add_le_add hupdate hz_sqrt

end BurachikSvaiterRobustnessHPE2001
