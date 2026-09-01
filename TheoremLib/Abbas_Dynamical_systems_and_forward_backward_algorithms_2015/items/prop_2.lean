import Mathlib
import Foundation.Convex.Subdifferential
import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.prop_1
import TheoremLib.Abbas_Dynamical_systems_and_forward_backward_algorithms_associated_with_the_sum_of_a_correction_math_2015.items.thm_2

namespace AbbasDynamical2015

open Filter MeasureTheory

/-- Proposition 2.15: the subgradient gap of an orbit tends to zero on `S`. -/
theorem subgradient_gap_tendsto_zero {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (S : Set H) (Phi : H → Set.Ioi (⊥ : EReal))
    (hPhi : Phi ∈ ERealFunction.gammaZero H) (B : H → H) (x v : ℝ → H) (z : H)
    (lam mu beta : ℝ) (hS : S.Nonempty) (hz : z ∈ S) (hlam : 0 < lam)
    (hmu : 0 < mu) (hmu_lam : mu * lam = 1) (hbeta : 0 < beta)
    (hB : CocoerciveOn beta Set.univ (fun w : Set.univ ↦ B w))
    (hx_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (hv_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval v 0 b)
    (hx_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt x (deriv x t) t)
    (hv_deriv : ∀ T, 0 < T →
      ∀ᵐ t ∂volume.restrict (Set.Icc 0 T), HasDerivAt v (deriv v t) t)
    (hvL2 : ∀ T, 0 < T → MemLp v 2 (volume.restrict (Set.Icc 0 T)))
    (hdxL2 : ∀ T, 0 < T → MemLp (deriv x) 2 (volume.restrict (Set.Icc 0 T)))
    (hsubgradient : ∀ t, 0 ≤ t → v t ∈ ERealFunction.subdifferential Phi (x t))
    (horbit : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
      lam • deriv x t + deriv v t + v t + B (x t) = 0)
    (hsolution : ∀ w, w ∈ S ↔ -B w ∈ ERealFunction.subdifferential Phi w)
    (hdom : ∀ t, 0 ≤ t → x t ∈ ERealFunction.effectiveDomain Phi)
    (hdomS : ∀ w, w ∈ S → w ∈ ERealFunction.effectiveDomain Phi) :
    Tendsto (fun t ↦ (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
      inner ℝ (v t) (z - x t)) atTop (nhds 0) := by
  have hnonneg : ∀ t, 0 ≤ t → 0 ≤ (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
      inner ℝ (v t) (z - x t) := by
    intro t ht
    have hineq := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
      (hsubgradient t ht) (hdomS z hz)
    linarith
  have horbit_pair : ∀ᵐ t ∂volume.restrict (Set.Ici 0),
      v t ∈ ERealFunction.subdifferential Phi (x t) ∧
        lam • deriv x t + deriv v t + v t + B (x t) = 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ici, horbit] with t ht hEq
    exact ⟨hsubgradient t ht, hEq⟩
  have hLyapunov := proposition_2_12 S Phi hPhi B x v z lam mu beta hS hz
    hlam hmu hmu_lam hbeta hB hx_ac hv_ac hx_deriv hv_deriv hsubgradient
    hvL2 hdxL2 horbit_pair (fun w hw => (hsolution w).1 hw) ⟨hdom, hdomS⟩
  obtain ⟨C, hC⟩ := hLyapunov.2.2.2.1
  have hconvergence := theorem_2_8_convergence S Phi hPhi B x v lam beta hS
    hlam hbeta hB horbit hx_ac hv_ac hx_deriv hv_deriv hvL2 hdxL2
    hsubgradient hsolution
  have hvlim : Tendsto (fun t => v t + B z) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => B z) atTop (nhds (B z)) := tendsto_const_nhds
    have h := (hconvergence.2.2.1 z hz).add hconst
    simpa using h
  have hupperlim : Tendsto (fun t => ‖v t + B z‖ * (C + ‖z‖)) atTop (nhds 0) := by
    have hconst : Tendsto (fun _ : ℝ => C + ‖z‖) atTop (nhds (C + ‖z‖)) :=
      tendsto_const_nhds
    simpa using hvlim.norm.mul hconst
  have hnonneg' : ∀ᶠ t in atTop,
      0 ≤ (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
        inner ℝ (v t) (z - x t) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact hnonneg t ht
  have hupper : ∀ᶠ t in atTop,
      (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
          inner ℝ (v t) (z - x t) ≤ ‖v t + B z‖ * (C + ‖z‖) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have hzineq := ERealFunction.subgradient_ineq_toReal_of_mem_gammaZero hPhi
      ((hsolution z).1 hz) (hdom t ht)
    have hxz : ‖x t - z‖ ≤ C + ‖z‖ := by
      calc
        ‖x t - z‖ ≤ ‖x t‖ + ‖z‖ := norm_sub_le _ _
        _ ≤ C + ‖z‖ := add_le_add (hC t ht) le_rfl
    have hinner : inner ℝ (v t + B z) (x t - z) ≤
        ‖v t + B z‖ * ‖x t - z‖ := by
      exact (le_abs_self _).trans (abs_real_inner_le_norm _ _)
    have hmul : ‖v t + B z‖ * ‖x t - z‖ ≤
        ‖v t + B z‖ * (C + ‖z‖) :=
      mul_le_mul_of_nonneg_left hxz (norm_nonneg _)
    have hzineq' : (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal ≤
        inner ℝ (B z) (x t - z) := by
      rw [inner_neg_left] at hzineq
      linarith
    have hgap : (Phi z : EReal).toReal - (Phi (x t) : EReal).toReal -
        inner ℝ (v t) (z - x t) ≤ inner ℝ (v t + B z) (x t - z) := by
      rw [show z - x t = -(x t - z) by abel, inner_neg_right, inner_add_left]
      linarith [hzineq']
    exact hgap.trans (hinner.trans hmul)
  exact squeeze_zero' hnonneg' hupper hupperlim

end AbbasDynamical2015
