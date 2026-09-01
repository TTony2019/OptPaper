import Mathlib
import Foundation.Convex.Subdifferential

namespace AbbasDynamical2015

open MeasureTheory

private theorem inner_deriv_nonneg_of_monotone
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {T : SetValuedOperator H H} {x v dx dv : ℝ → H}
    (hT : T.IsMonotone) (hmem : ∀ s : ℝ, 0 ≤ s → v s ∈ T (x s))
    {t : ℝ} (ht : 0 < t) (hxd : HasDerivAt x (dx t) t)
    (hvd : HasDerivAt v (dv t) t) : 0 ≤ inner ℝ (dx t) (dv t) := by
  let qx : ℝ → H := fun h => h⁻¹ • (x (t + h) - x t)
  let qv : ℝ → H := fun h => h⁻¹ • (v (t + h) - v t)
  have hqx : Filter.Tendsto qx (nhdsWithin 0 {0}ᶜ) (nhds (dx t)) := hxd.tendsto_slope_zero
  have hqv : Filter.Tendsto qv (nhdsWithin 0 {0}ᶜ) (nhds (dv t)) := hvd.tendsto_slope_zero
  have hlim : Filter.Tendsto (fun h => inner ℝ (qx h) (qv h))
      (nhdsWithin 0 {0}ᶜ) (nhds (inner ℝ (dx t) (dv t))) := hqx.inner hqv
  rw [← neg_nonpos]
  apply le_of_tendsto hlim.neg
  rw [eventually_nhdsWithin_iff]
  refine Metric.eventually_nhds_iff.2 ⟨t, ht, ?_⟩
  intro h hh hne
  have hth : 0 ≤ t + h := by
    rw [Real.dist_eq] at hh
    nlinarith [abs_lt.mp hh]
  have hmono := hT (v (t + h)) (hmem (t + h) hth) (v t) (hmem t ht.le)
  dsimp only [qx, qv]
  rw [real_inner_smul_left, inner_smul_right]
  have hrewrite : h⁻¹ * (h⁻¹ * inner ℝ (x (t + h) - x t) (v (t + h) - v t)) =
      (h⁻¹ * h⁻¹) * inner ℝ (v (t + h) - v t) (x (t + h) - x t) := by
    rw [real_inner_comm]
    ring
  rw [hrewrite]
  exact neg_nonpos.mpr (mul_nonneg (mul_self_nonneg _) hmono)

/-- Lemma 2.14 follows from monotonicity of the subdifferential along the orbit. -/
theorem derivative_inner_nonnegative {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (x v : ℝ → H)
    (hsubgradient : ∀ t, 0 ≤ t →
      v t ∈ ERealFunction.subdifferential Phi (x t))
    (_hx_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval x 0 b)
    (_hv_ac : ∀ b : ℝ, 0 < b → AbsolutelyContinuousOnInterval v 0 b)
    (hx_deriv : ∀ᵐ t ∂volume.restrict (Set.Ioi 0), HasDerivAt x (deriv x t) t)
    (hv_deriv : ∀ᵐ t ∂volume.restrict (Set.Ioi 0), HasDerivAt v (deriv v t) t) :
    ∀ᵐ t ∂volume.restrict (Set.Ioi 0), 0 ≤ inner ℝ (deriv x t) (deriv v t) := by
  have hmono : SetValuedOperator.IsMonotone
      (ERealFunction.subdifferential (fun y : H => (Phi y : EReal))) :=
    ERealFunction.isMonotone_subdifferential
      (fun y : H => (Phi y : EReal))
      (ERealFunction.isProper_of_mem_gammaZero hPhi)
  filter_upwards [hx_deriv, hv_deriv,
    MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t hxt hvt ht
  exact inner_deriv_nonneg_of_monotone hmono hsubgradient ht hxt hvt

end AbbasDynamical2015
