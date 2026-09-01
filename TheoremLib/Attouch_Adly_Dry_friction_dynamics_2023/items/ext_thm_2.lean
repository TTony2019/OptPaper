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
    (z : ℝ → H) (τ dτ ddτ : ℝ → ℝ) (x y dx dy ddx : ℝ → H) (s₀ : ℝ)
    (hy : y = timeScaledTrajectory z τ) (haverage : IsWeightedAverage τ dτ x y dx s₀)
    (hdτ_pos : ∀ s ∈ Set.Ici s₀, 0 < dτ s)
    (hdy : ∀ s ∈ Set.Ici s₀, HasDerivAt y (dy s) s)
    (hddx : ∀ s ∈ Set.Ici s₀, HasDerivAt dx (ddx s) s)
    (hddτ : ∀ s ∈ Set.Ici s₀, HasDerivAt dτ (ddτ s) s) :
    (∀ s ∈ Set.Ici s₀, x s = x s₀ + ∫ u in s₀..s, dx u) ∧
      ∀ s ∈ Set.Ioi s₀,
        ddx s - (ddτ s / (dτ s) ^ 2) • (x s - y s) +
          (dτ s)⁻¹ • (dx s - dy s) = 0 := by
  rcases haverage with ⟨hτ, hxy0, haverage⟩
  have hdx : ∀ s ∈ Set.Ici s₀, HasDerivAt x (dx s) s := fun s hs =>
    (haverage s hs).1
  have hode : ∀ s ∈ Set.Ici s₀, dx s + (dτ s)⁻¹ • (x s - y s) = 0 := fun s hs =>
    (haverage s hs).2
  constructor
  · intro s hs
    have hsle : s₀ ≤ s := hs
    have hxDeriv : ∀ u ∈ Set.uIcc s₀ s, HasDerivAt x (dx u) u := by
      rw [Set.uIcc_of_le hsle]
      intro u hu
      exact hdx u (Set.mem_Ici.mpr hu.1)
    have hdxCont : ContinuousOn dx (Set.uIcc s₀ s) := by
      rw [Set.uIcc_of_le hsle]
      intro u hu
      exact (hddx u (Set.mem_Ici.mpr hu.1)).continuousAt.continuousWithinAt
    have hdxInt : IntervalIntegrable dx MeasureTheory.volume s₀ s := hdxCont.intervalIntegrable
    have hftc : ∫ u in s₀..s, dx u = x s - x s₀ :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hxDeriv hdxInt
    rw [hftc]
    abel
  · intro s hs
    have hsIci : s ∈ Set.Ici s₀ := Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hs))
    have hdτne : dτ s ≠ 0 := ne_of_gt (hdτ_pos s hsIci)
    let F : ℝ → H := fun t => dx t + (dτ t)⁻¹ • (x t - y t)
    have hinv : HasDerivAt (fun t : ℝ => (dτ t)⁻¹)
        (-ddτ s / (dτ s) ^ 2) s :=
      (hddτ s hsIci).inv hdτne
    have hdiff : HasDerivAt (fun t : ℝ => x t - y t) (dx s - dy s) s :=
      (hdx s hsIci).sub (hdy s hsIci)
    have hFderiv : HasDerivAt F
        (ddx s - (ddτ s / (dτ s) ^ 2) • (x s - y s) +
          (dτ s)⁻¹ • (dx s - dy s)) s := by
      dsimp [F]
      convert (hddx s hsIci).add (hinv.smul hdiff) using 1
      all_goals simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, div_eq_mul_inv]
    have hFzero : (fun _ : ℝ => (0 : H)) =ᶠ[nhds s] F := by
      filter_upwards [eventually_gt_nhds hs] with t ht
      simpa [F] using (hode t (le_of_lt ht)).symm
    have hconst : HasDerivAt (fun _ : ℝ => (0 : H))
        (ddx s - (ddτ s / (dτ s) ^ 2) • (x s - y s) +
          (dτ s)⁻¹ • (dx s - dy s)) s :=
      hFderiv.congr_of_eventuallyEq hFzero
    exact hconst.unique (hasDerivAt_const s (0 : H))

end AttouchAdlyDryFrictionDynamics2023
