import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.thm_4
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.thm_5
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_3
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_4
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_thm_2

namespace AttouchAdlyDryFrictionDynamics2023

private theorem scaled_time_mem_Ici {s₀ α s : ℝ} (hs₀ : 0 < s₀) (hα : 1 < α)
    (hs : s ∈ Set.Ici s₀) :
    s ^ 2 / (2 * (α - 1)) ∈ Set.Ici (s₀ ^ 2 / (2 * (α - 1))) := by
  have hspos : 0 < s := lt_of_lt_of_le hs₀ hs
  have hden : 0 < 2 * (α - 1) := mul_pos (by norm_num) (sub_pos.mpr hα)
  apply (div_le_div_iff_of_pos_right hden).mpr
  nlinarith [mul_nonneg (sub_nonneg.mpr hs)
    (add_nonneg (le_of_lt hs₀) (le_of_lt hspos))]

private theorem scaled_exponent_eq {α rate s : ℝ} (hα : 1 < α) :
    -rate * (s ^ 2 / (2 * (α - 1))) = -(rate / (2 * (α - 1))) * s ^ 2 := by
  have hden : 2 * (α - 1) ≠ 0 :=
    ne_of_gt (mul_pos (by norm_num) (sub_pos.mpr hα))
  field_simp [hden]

/-- Theorem 4.3: the quadratic DRYSTAR trajectory has an `exp (-μ s²)` rate. -/
theorem theorem_4_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {s₀ r α : ℝ} (hr : 0 < r) (hα : 1 < α) (hs₀ : 0 < s₀)
    (A : H →L[ℝ] H) (f : H → ℝ) (hf : Differentiable ℝ f) (x dx ddx p g q : ℝ → H)
    (hsymm : A.IsSymmetric) (hpos : ∀ u ≠ 0, 0 < inner ℝ (A u) u)
    (_hsolution : IsDryStarTrajectory r α s₀ f hf x dx ddx p)
    (hbridge : ∀ s ∈ Set.Ici s₀,
      g (s ^ 2 / (2 * (α - 1))) = A (x s + (s / (α - 1)) • dx s))
    (hdualDrygrad : ∀ t, q t ∈ frictionBallProjector r (g t) ∧
      HasDerivAt g (A (q t - g t)) t)
    (hcoercive : ∃ rate ν : ℝ, 0 < rate ∧ 0 < ν ∧ ∀ ξ : H,
      rate * ‖ξ‖ ^ 2 ≤ inner ℝ (A ξ) ξ ∧ inner ℝ (A ξ) ξ ≤ ν * ‖ξ‖ ^ 2)
    (henergyDeriv : ∀ t : ℝ, HasDerivAt
      (fun u => Metric.infDist (g u) (frictionBall r) ^ 2 / 2)
      (- inner ℝ (g t - q t) (A (g t - q t))) t)
    (hinitial : r < ‖g (s₀ ^ 2 / (2 * (α - 1)))‖) :
    ∃ C μ : ℝ, 0 < C ∧ 0 < μ ∧ ∀ s ∈ Set.Ici s₀,
      Metric.infDist (A (x s + (s / (α - 1)) • dx s)) (frictionBall r) ≤ C * Real.exp (-μ * s ^ 2) := by
  rcases theorem_3_3 (t₀ := s₀ ^ 2 / (2 * (α - 1))) hr A g q hsymm hpos
    hdualDrygrad hcoercive henergyDeriv hinitial with
    ⟨Cupper, Clower, rate, ν, hCupper, hClower, hrate, hν, hupper, hlower, hnotmem⟩
  refine ⟨Cupper, rate / (2 * (α - 1)), hCupper,
    div_pos hrate (mul_pos (by norm_num) (sub_pos.mpr hα)), ?_⟩
  intro s hs
  have hbound := hupper (s ^ 2 / (2 * (α - 1)))
    (scaled_time_mem_Ici hs₀ hα hs)
  rw [hbridge s hs, scaled_exponent_eq hα] at hbound
  exact hbound

end AttouchAdlyDryFrictionDynamics2023
