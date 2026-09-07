import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_1

namespace AttouchPeypouquetRedont2014

/-- The parameter `γ = (1-aλ)/(2bλ²)`. -/
noncomputable def gamma (a b lam : ℝ) : ℝ := (1 - a * lam) / (2 * b * lam ^ 2)

theorem gamma_pos {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (phi theta : H → EReal) (psi : H → ℝ) (gradPsi : H → H) (a b lam Lpsi : ℝ)
    (hH : IFBHypothesis phi theta psi gradPsi a b lam Lpsi) : 0 < gamma a b lam := by
  have hlam_lt_one_div_a : lam < 1 / a :=
    lt_of_lt_of_le hH.step_lt (min_le_left _ _)
  have hlam_mul_a_lt_one : lam * a < 1 :=
    (lt_div_iff₀ hH.a_pos).mp hlam_lt_one_div_a
  have hprod_lt_one : a * lam < 1 := by
    simpa [mul_comm] using hlam_mul_a_lt_one
  have hnum_pos : 0 < 1 - a * lam := sub_pos.mpr hprod_lt_one
  have htwo_b_pos : 0 < 2 * b :=
    mul_pos (by norm_num) hH.b_pos
  have hlam_sq_pos : 0 < lam ^ 2 := pow_pos hH.step_pos 2
  have hden_pos : 0 < 2 * b * lam ^ 2 :=
    mul_pos htwo_b_pos hlam_sq_pos
  unfold gamma
  exact div_pos hnum_pos hden_pos

end AttouchPeypouquetRedont2014
