import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_8
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.thm_10

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Set Filter

/-- Remark 7.9: The exact estimate (25) of Theorem 7.1 is an immediate
  consequence of the approximate estimate (29) in Theorem 7.8 by passage
  to the limit as ε→0. -/
theorem rem_5 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedSpace ℝ H] [NormedAddCommGroup M] (V : Set M) (A : M → H → H)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (α γ T : ℝ)
    (hα : 0 < α) (hT : 0 < T)
    (hcoco : ∀ μ ∈ V, CocoerciveOn α Set.univ (fun x : Set.univ => A μ x))
    (hsol : ∀ μ ∈ V,
      ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ) ∧
        (∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t → HasDerivAt (x μ) (dx μ t) t) ∧
        ∀ᵐ t ∂ MeasureTheory.volume, 0 ≤ t → HasDerivAt (dx μ) (ddx μ t) t)
    (θ₁ θ₂ : ℝ) (hC₂ : 0 < θ₁ ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧
      ∀ u μ μ', μ ∈ V → μ' ∈ V → ‖A μ u - A μ' u‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂)
    (hγT : γ * T + T ^ 2 / α < 1) :
    (∀ μ ∈ V, ∀ μ' ∈ V,
      pathSupNorm T (fun t => x μ t - x μ' t) ≤
        α / (α - α * γ * T - T ^ 2) *
        (‖u₀ μ - u₀ μ'‖ + T * ‖v₀ μ - v₀ μ'‖ + T ^ 2 * θ₁ * ‖μ - μ'‖ ^ θ₂)) :=
  thm_8 V A x dx ddx u₀ v₀ α γ T hα hT hcoco (fun μ hμ => (hsol μ hμ).1) θ₁ θ₂ hC₂ hγT

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
