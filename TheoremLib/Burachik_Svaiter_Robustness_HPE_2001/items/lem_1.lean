import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.def_1
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.algo_1
import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.def_2

namespace BurachikSvaiterRobustnessHPE2001

private theorem hpe_norm_difference_identity {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (xStar y x z : H) :
    ‖xStar - x‖ ^ 2 - ‖xStar - z‖ ^ 2 =
      2 * inner ℝ (z - x) (xStar - y) + ‖y - x‖ ^ 2 - ‖y - z‖ ^ 2 := by
  have hx : xStar - x = (xStar - y) + (y - x) := by abel
  have hz : xStar - z = (xStar - y) + (y - z) := by abel
  rw [hx, hz, norm_add_sq_real, norm_add_sq_real]
  simp only [inner_sub_right, inner_sub_left, real_inner_comm]
  ring

/-- Lemma 3.1. -/
theorem hpe_descent {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : SetValuedOperator H H} (A : HPEIterates H T) {xStar : H}
    (hxStar : (0 : H) ∈ T xStar) (k : ℕ) :
    ‖xStar - A.x k‖ ^ 2 - ‖xStar - extragradientStep A k‖ ^ 2 ≥
      (1 - (A.σ k) ^ 2) * ‖A.y k - A.x k‖ ^ 2 - A.δ k := by
  have hm := A.enlargement_mem k
  have hmem : -A.ε k ≤ inner ℝ ((0 : H) - A.v k) (xStar - A.y k) := by
    simpa [epsilonEnlargement] using hm xStar (0 : H) hxStar
  have hc0 : 0 ≤ A.c k := le_of_lt (A.c_pos k)
  have hinner : -A.c k * A.ε k ≤
      inner ℝ (extragradientStep A k - A.x k) (xStar - A.y k) := by
    have hscaled := mul_le_mul_of_nonneg_left hmem hc0
    rw [show extragradientStep A k - A.x k = -(A.c k • A.v k) by
      simp [extragradientStep], inner_neg_left, real_inner_smul_left]
    simpa [mul_neg, neg_mul] using hscaled
  have hnorm := hpe_norm_difference_identity xStar (A.y k) (A.x k)
    (extragradientStep A k)
  have hfirst : ‖xStar - A.x k‖ ^ 2 - ‖xStar - extragradientStep A k‖ ^ 2 ≥
      ‖A.y k - A.x k‖ ^ 2 - ‖A.y k - extragradientStep A k‖ ^ 2 -
        2 * A.c k * A.ε k := by
    nlinarith [hnorm, hinner]
  have hyz : A.y k - extragradientStep A k = A.c k • A.v k + A.y k - A.x k := by
    simp [extragradientStep]
    abel
  have hres : ‖A.y k - extragradientStep A k‖ ^ 2 + 2 * A.c k * A.ε k ≤
      A.δ k + (A.σ k) ^ 2 * ‖A.y k - A.x k‖ ^ 2 := by
    rw [hyz]
    exact A.residual_bound k
  nlinarith [hfirst, hres]

end BurachikSvaiterRobustnessHPE2001
