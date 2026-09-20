import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_4

namespace AttouchAdlyDryFrictionDynamics2023

/- EXTERNAL DEPENDENCY: Time scaling and averaging theorem
   Source: H. Attouch, R.I. Bot, D.-K. Nguyen, Fast convex optimization via time scale and averaging of the steepest descent.
   Status: proof supplied by the referenced result.
-/
/-- The cited weighted-average representation under an increasing time scale. -/
theorem time_scaling_and_averaging_theorem {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [CompleteSpace H]
    (z : ℝ → H) (τ : ℝ → ℝ) (x y : ℝ → H) (s₀ : ℝ)
    (_hy : y = timeScaledTrajectory z τ)
    (haverage : IsWeightedAverageOn τ (deriv τ) x y (deriv x) s₀)
    (hdτ_pos : ∀ s ∈ Set.Ici s₀, 0 < deriv τ s)
    (hy_diff : Differentiable ℝ y)
    (hx : ContDiff ℝ 2 x) (hτ : ContDiff ℝ 2 τ) :
    (∀ s ∈ Set.Ici s₀, x s = x s₀ + ∫ u in s₀..s, deriv x u) ∧
      ∀ s ∈ Set.Ioi s₀,
        deriv (deriv x) s - (deriv (deriv τ) s / (deriv τ s) ^ 2) • (x s - y s) +
          (deriv τ s)⁻¹ • (deriv x s - deriv y s) = 0 := by
  rcases haverage with ⟨_hτscale, _hxy0, haverage⟩
  have hdx : ∀ s ∈ Set.Ici s₀, HasDerivAt x (deriv x s) s := fun s hs =>
    (haverage s hs).1
  have hode : ∀ s ∈ Set.Ici s₀,
      deriv x s + (deriv τ s)⁻¹ • (x s - y s) = 0 := fun s hs =>
    (haverage s hs).2
  have hdx_diff : Differentiable ℝ (deriv x) := by
    have h := (contDiff_nat_iff_iteratedDeriv.mp hx).2 1 (by norm_num)
    simpa [iteratedDeriv_one] using h
  have hdτ_diff : Differentiable ℝ (deriv τ) := by
    have h := (contDiff_nat_iff_iteratedDeriv.mp hτ).2 1 (by norm_num)
    simpa [iteratedDeriv_one] using h
  constructor
  · intro s hs
    have hsle : s₀ ≤ s := hs
    have hxDeriv : ∀ u ∈ Set.uIcc s₀ s, HasDerivAt x (deriv x u) u := by
      rw [Set.uIcc_of_le hsle]
      intro u hu
      exact hdx u (Set.mem_Ici.mpr hu.1)
    have hdxCont : ContinuousOn (deriv x) (Set.uIcc s₀ s) := by
      exact hdx_diff.continuous.continuousOn
    have hdxInt : IntervalIntegrable (deriv x) MeasureTheory.volume s₀ s :=
      hdxCont.intervalIntegrable
    have hftc : ∫ u in s₀..s, deriv x u = x s - x s₀ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hxDeriv hdxInt
    rw [hftc]
    abel
  · intro s hs
    have hsIci : s ∈ Set.Ici s₀ := Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hs))
    have hdτne : deriv τ s ≠ 0 := ne_of_gt (hdτ_pos s hsIci)
    let F : ℝ → H := fun t => deriv x t + (deriv τ t)⁻¹ • (x t - y t)
    have hinv : HasDerivAt (fun t : ℝ => (deriv τ t)⁻¹)
        (-deriv (deriv τ) s / (deriv τ s) ^ 2) s :=
      (hdτ_diff s).hasDerivAt.inv hdτne
    have hdiff : HasDerivAt (fun t : ℝ => x t - y t) (deriv x s - deriv y s) s :=
      (hdx s hsIci).sub (hy_diff s).hasDerivAt
    have hFderiv : HasDerivAt F
        (deriv (deriv x) s - (deriv (deriv τ) s / (deriv τ s) ^ 2) • (x s - y s) +
          (deriv τ s)⁻¹ • (deriv x s - deriv y s)) s := by
      dsimp [F]
      convert (hdx_diff s).hasDerivAt.add (hinv.smul hdiff) using 1
      all_goals simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, div_eq_mul_inv]
    have hFzero : (fun _ : ℝ => (0 : H)) =ᶠ[nhds s] F := by
      filter_upwards [eventually_gt_nhds hs] with t ht
      simpa [F] using (hode t (le_of_lt ht)).symm
    have hconst : HasDerivAt (fun _ : ℝ => (0 : H))
        (deriv (deriv x) s - (deriv (deriv τ) s / (deriv τ s) ^ 2) • (x s - y s) +
          (deriv τ s)⁻¹ • (deriv x s - deriv y s)) s :=
      hFderiv.congr_of_eventuallyEq hFzero
    exact hconst.unique (hasDerivAt_const s (0 : H))

end AttouchAdlyDryFrictionDynamics2023
