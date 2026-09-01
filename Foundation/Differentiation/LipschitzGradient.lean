import Mathlib

/-!
# Lipschitz-gradient functions

`HasDifferentiableLipschitzGradient`: an `L`-smooth function — differentiable,
with its Fréchet derivative represented as an inner product against a gradient
field that is `L`-Lipschitz.  This is the standard smoothness hypothesis for
gradient-descent analyses.

Promoted from
`TheoremLib/Attouch_Adly_Le_Threshold_dry_friction_2023/items/ext_def_2`.

See also `fderiv_continuous_of_bounded_lipschitz` below, promoted from
`TheoremLib/Attouch_Balhag_Chbani_Riahi_Tikhonov_Inertial_Dynamics_2022/items/thm_4`.
-/

open scoped InnerProductSpace

/-- An `L`-smooth function: `f` is differentiable, `grad` is its gradient field in the
sense `fderiv ℝ f x v = inner ℝ (grad x) v`, and `grad` is `L`-Lipschitz. -/
def HasDifferentiableLipschitzGradient {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (L : ℝ) (grad : H → H) : Prop :=
  Differentiable ℝ f ∧ (∀ x v, fderiv ℝ f x v = inner ℝ (grad x) v) ∧
    ∀ x y, dist (grad x) (grad y) ≤ L * dist x y

/-- A function with a differentiable Lipschitz gradient is differentiable. -/
theorem hasDifferentiableLipschitzGradient_differentiable {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : H → ℝ) (L : ℝ) (grad : H → H) :
    HasDifferentiableLipschitzGradient f L grad → Differentiable ℝ f := by
  intro h
  exact h.1

/-- If the Fréchet derivative of `f : H → ℝ` is Lipschitz with a (local) constant `L` on
every bounded set `{x | ‖x‖ ≤ r}`, then `fderiv ℝ f` is continuous.

A "bounded derivative on bounded sets implies continuous derivative" fact (via a
mean-value/Lipschitz argument), used as a proof helper for Theorem 4 of
Attouch, Balhag, Chbani, Riahi, *Tikhonov inertial dynamics and convergence rates* (2022);
promoted from
`TheoremLib/Attouch_Balhag_Chbani_Riahi_Tikhonov_Inertial_Dynamics_2022/items/thm_4`. -/
theorem fderiv_continuous_of_bounded_lipschitz
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ)
    (h : ∀ r : ℝ, 0 < r → ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : H,
      ‖x‖ ≤ r → ‖y‖ ≤ r → ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ L * ‖x - y‖) :
    Continuous (fderiv ℝ f) := by
  rw [continuous_iff_continuousAt]
  intro x
  obtain ⟨L, hL, hLip⟩ := h (‖x‖ + 1) (by positivity)
  rw [Metric.continuousAt_iff]
  intro η hη
  by_cases hL0 : L = 0
  · refine ⟨1, zero_lt_one, ?_⟩
    intro y hy
    have hxy : ‖x - y‖ < 1 := by
      simpa [dist_eq_norm, norm_sub_rev] using hy
    have hybound : ‖y‖ ≤ ‖x‖ + 1 := by
      calc
        ‖y‖ ≤ ‖y - x‖ + ‖x‖ := norm_le_norm_sub_add _ _
        _ ≤ 1 + ‖x‖ := by gcongr; simpa [norm_sub_rev] using hxy.le
        _ = ‖x‖ + 1 := by ring
    have hbound := hLip x y (by linarith) hybound
    rw [hL0] at hbound
    simp only [zero_mul] at hbound
    have heq : fderiv ℝ f x = fderiv ℝ f y := by
      apply sub_eq_zero.mp
      apply norm_eq_zero.mp
      exact le_antisymm hbound (norm_nonneg _)
    rw [heq]
    simpa using hη
  · refine ⟨min 1 (η / L), lt_min zero_lt_one
      (div_pos hη (lt_of_le_of_ne hL (Ne.symm hL0))), ?_⟩
    intro y hy
    have hxy : ‖x - y‖ < 1 := by
      have : dist y x < 1 := lt_of_lt_of_le hy (min_le_left _ _)
      simpa [dist_eq_norm, norm_sub_rev] using this
    have hybound : ‖y‖ ≤ ‖x‖ + 1 := by
      calc
        ‖y‖ ≤ ‖y - x‖ + ‖x‖ := norm_le_norm_sub_add _ _
        _ ≤ 1 + ‖x‖ := by gcongr; simpa [norm_sub_rev] using hxy.le
        _ = ‖x‖ + 1 := by ring
    have hbound := hLip x y (by linarith) hybound
    rw [dist_eq_norm]
    calc
      ‖fderiv ℝ f y - fderiv ℝ f x‖ = ‖fderiv ℝ f x - fderiv ℝ f y‖ := norm_sub_rev _ _
      _ ≤ L * ‖x - y‖ := hbound
      _ < L * (η / L) := by
        gcongr
        simpa [dist_eq_norm, norm_sub_rev] using lt_of_lt_of_le hy (min_le_right _ _)
      _ = η := by field_simp
