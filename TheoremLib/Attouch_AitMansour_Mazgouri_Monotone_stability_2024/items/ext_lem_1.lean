import Mathlib
import Foundation.Differentiation.ODE
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_3

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-! Item `ext_lem_1`: the nonlinear Gronwall inequality and its proof helpers
  are supplied canonically by Foundation (`Foundation.Differentiation.ODE`).
  The paper-local helpers `ac_exp_neg_intervalIntegral` and
  `ac_nonincreasing_of_ae_deriv_nonpos` are dropped in favour of the canonical
  Foundation publics with the same statements. -/

/-- Composition of an absolutely continuous function with a locally Lipschitz
  function on the image is absolutely continuous.  Supplied canonically by
  Foundation. -/
recall ac_comp_of_lipschitzOn_image

/-- `(exp(-A/q))^q = exp(-A)` for `q > 0`.  Supplied canonically by Foundation. -/
recall exp_neg_div_rpow

/-- `x^α (x+ε)^{-α} ≤ 1`.  Supplied canonically by Foundation. -/
recall rpow_ratio_le_one

/-- A positive-shifted power of an absolutely continuous nonnegative function
  is absolutely continuous.  Supplied canonically by Foundation. -/
recall shifted_rpow_ac

/-- The linear Gronwall inequality on an interval.  Supplied canonically by
  Foundation. -/
recall linear_gronwall_interval

/-- The conjugated shifted-power subsolution estimate.  Supplied canonically by
  Foundation. -/
recall conjugated_shifted_rpow_subsolution

/-- Lemma 2.6 (nonlinear Gronwall inequality), supplied canonically by
  Foundation as `nonlinear_gronwall_inequality`. -/
recall nonlinear_gronwall_inequality

/-- Lemma 2.6 (nonlinear Gronwall inequality): Let T>0, a,b∈L¹(t₀,t₀+T;ℝ)
  with b(t)≥0 for a.e. t, 0≤α<1, and let w:[t₀,t₀+T]→ℝ₊ be absolutely continuous
  satisfying (1-α)w'(t)≤a(t)w(t)+b(t)w^α(t) for a.e. t∈[t₀,t₀+T].
  Then for all t∈[t₀,t₀+T],
  w^{1-α}(t) ≤ w^{1-α}(t₀)e^{∫_{t₀}^t a(τ)dτ} + ∫_{t₀}^t e^{∫_s^t a(τ)dτ}b(s)ds.
  Supplied canonically by Foundation. -/
abbrev ext_lem_1 {w a b : ℝ → ℝ} {t₀ T α : ℝ} (hT : 0 < T) (hα₁ : 0 ≤ α) (hα₂ : α < 1)
    (hac : AbsolutelyContinuousOnInterval w t₀ (t₀ + T))
    (hw_nonneg : ∀ t, t ∈ Set.Icc t₀ (t₀ + T) → 0 ≤ w t)
    (ha_int : MeasureTheory.IntegrableOn a (Set.Icc t₀ (t₀ + T)) MeasureTheory.volume)
    (hb_int : MeasureTheory.IntegrableOn b (Set.Icc t₀ (t₀ + T)) MeasureTheory.volume)
    (hb_nonneg : ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc t₀ (t₀ + T) → 0 ≤ b t)
    (hineq : ∀ᵐ t ∂ MeasureTheory.volume, t ∈ Set.Icc t₀ (t₀ + T) →
      (1 - α) * deriv w t ≤ a t * w t + b t * (w t) ^ α) :
    ∀ t : ℝ, t₀ ≤ t → t ≤ t₀ + T →
      w t ^ (1 - α) ≤ w t₀ ^ (1 - α) * Real.exp (∫ τ in t₀..t, a τ) +
        ∫ s in t₀..t, Real.exp (∫ τ in s..t, a τ) * b s :=
  nonlinear_gronwall_inequality hT hα₁ hα₂ hac hw_nonneg ha_int hb_int hb_nonneg hineq

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
