import Mathlib
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.def_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.thm_1
import TheoremLib.Attouch_A_DYNAMICAL_APPROACH_TO_AN_INERTIAL_FORWARD_BACKWARD_ALGORITHM_FOR_CONVEX_MINIMIZATION_2014.items.ext_def_3

namespace AttouchPeypouquetRedont2014

private theorem finite_dimensional_weak_inverse_continuous {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [FiniteDimensional ℝ H] :
    Continuous ((toWeakSpace ℝ H).symm : WeakSpace ℝ H → H) :=
  (List.TFAE.out realHilbertSpace_tfae_finiteDimensional_compactUnitBall_weakTopology 0 2).mp
    (show FiniteDimensional ℝ H from inferInstance)

theorem ifb_lipschitz_constant_pos {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi) : 0 < Lpsi := by
  have hstepBound : lam < 2 * (a + b) / (b * Lpsi) :=
    lt_of_lt_of_le hH.step_lt (min_le_right _ _)
  have hquot : 0 < 2 * (a + b) / (b * Lpsi) := lt_trans hH.step_pos hstepBound
  have hnum : 0 < 2 * (a + b) := by nlinarith [hH.a_pos, hH.b_pos]
  rcases (div_pos_iff.mp hquot) with hden | hden
  · rcases (mul_pos_iff.mp hden.2) with hpos | hneg
    · exact hpos.2
    · linarith [hH.b_pos, hneg.1]
  · linarith [hnum, hden.1]

/-- Corollary 9: in finite dimension the weak IFB limit is a strong limit. -/
theorem corollary9 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (phi Θ : H → EReal) (psi : H → ℝ) (gradPsi : H → H)
    (a b lam Lpsi : ℝ) (u y : ℕ → H) (hH : IFBHypothesis phi Θ psi gradPsi a b lam Lpsi)
    (hIFB : IsIFBTrajectory phi psi gradPsi a b lam u y)
    (hS : (Optimization.argminSet Θ).Nonempty) :
    ∃ q ∈ Optimization.argminSet Θ, Filter.Tendsto u Filter.atTop (nhds q) := by
  letI : CompleteSpace H := FiniteDimensional.complete ℝ H
  have hweakSymm : Continuous ((toWeakSpace ℝ H).symm : WeakSpace ℝ H → H) :=
    finite_dimensional_weak_inverse_continuous
  have hLpsi : 0 < Lpsi := ifb_lipschitz_constant_pos phi Θ psi gradPsi a b lam Lpsi hH
  have hLip : LipschitzWith Lpsi.toNNReal gradPsi := by
    rw [lipschitzWith_iff_dist_le_mul]
    intro x y
    simpa [dist_eq_norm, Real.coe_toNNReal Lpsi hLpsi.le] using hH.psi_lipschitz x y
  have hgradCont : Continuous gradPsi := hLip.continuous
  have hgradWeak : IsWeakToWeakSequentiallyContinuous gradPsi := by
    unfold IsWeakToWeakSequentiallyContinuous
    intro x x₀ hx
    have hxStrong : Filter.Tendsto x Filter.atTop (nhds x₀) := by
      simpa using (hweakSymm.tendsto (toWeakSpace ℝ H x₀)).comp hx
    have hgradStrong : Filter.Tendsto (fun n => gradPsi (x n)) Filter.atTop
        (nhds (gradPsi x₀)) :=
      (hgradCont.tendsto x₀).comp hxStrong
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      ((toWeakSpaceCLM ℝ H).continuous.tendsto (gradPsi x₀)).comp hgradStrong
  rcases (theorem1 phi Θ psi gradPsi a b lam Lpsi u y hH hIFB).2.1
      ⟨hS, Or.inr (Or.inr (Or.inl hgradWeak))⟩ with
    ⟨q, hqS, hweak⟩
  exact ⟨q, hqS, by simpa using (hweakSymm.tendsto (toWeakSpace ℝ H q)).comp hweak⟩

end AttouchPeypouquetRedont2014
