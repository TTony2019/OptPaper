import Mathlib

namespace AttouchAdlyDryFrictionDynamics2023

/- EXTERNAL DEPENDENCY: Fubini--Tonelli theorem for nonnegative integrands
   Source: Fubini--Tonelli theorem
   Status: proof supplied by the referenced result.
-/
/-- Tonelli's interchange formula for a nonnegative measurable integrand. -/
theorem fubini_tonelli_nonnegative {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : MeasureTheory.Measure α) (ν : MeasureTheory.Measure β)
    [MeasureTheory.SFinite μ] [MeasureTheory.SFinite ν] (K : α → β → ENNReal)
    (hK : Measurable (fun p : α × β => K p.1 p.2)) :
    ∫⁻ x, ∫⁻ y, K x y ∂ν ∂μ = ∫⁻ y, ∫⁻ x, K x y ∂μ ∂ν :=
  MeasureTheory.lintegral_lintegral_swap (μ := μ) (ν := ν) (f := K) hK.aemeasurable

end AttouchAdlyDryFrictionDynamics2023
