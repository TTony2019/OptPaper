import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.thm_5
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.thm_6
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_4

namespace AttouchAdlyDryFrictionDynamics2023

private theorem integrating_factor_deriv_zero {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] {s p : ℝ} {x dx : ℝ → H} {xLimit : H} (hs : 0 < s)
    (hx : HasDerivAt x (dx s) s)
    (hode : dx s + (p / s) • (x s - xLimit) = 0) :
    HasDerivAt (fun t => Real.rpow t p • (x t - xLimit)) 0 s := by
  have hsne : s ≠ 0 := ne_of_gt hs
  have hraw := (Real.hasDerivAt_rpow_const (p := p) (Or.inl hsne)).smul
    (hx.sub_const xLimit)
  convert hraw using 1
  rw [eq_neg_of_add_eq_zero_left hode, Real.rpow_sub_one hsne]
  simp only [smul_neg, smul_smul]
  field_simp [hsne]
  ring_nf
  simp

/-- Remark 4.1: after finite stabilization of `y`, the averaged trajectory has a polynomial tail. -/
theorem remark_4_1 {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] {sbar α : ℝ}
    (x y dx : ℝ → H) (xLimit : H)
    (hα : 1 < α) (hpositiveTime : 0 < sbar)
    (haverage : ∀ s ∈ Set.Ici sbar, HasDerivAt x (dx s) s ∧
      dx s + ((α - 1) / s) • (x s - y s) = 0)
    (hstab : ∀ s ∈ Set.Ici sbar, y s = xLimit) :
    ∃ C : H, ∀ s ∈ Set.Ici sbar, x s = xLimit + (Real.rpow s (α - 1))⁻¹ • C := by
  have _hp : 0 < α - 1 := sub_pos.mpr hα
  let F : ℝ → H := fun t => Real.rpow t (α - 1) • (x t - xLimit)
  have hFzero : ∀ s ∈ Set.Ici sbar, HasDerivAt F 0 s := by
    intro s hs
    have hspos : 0 < s := lt_of_lt_of_le hpositiveTime hs
    have havg := haverage s hs
    rw [hstab s hs] at havg
    exact integrating_factor_deriv_zero hspos havg.1 havg.2
  refine ⟨F sbar, ?_⟩
  intro s hs
  have hdiff : ∀ t ∈ Set.Ici sbar, DifferentiableWithinAt ℝ F (Set.Ici sbar) t := by
    intro t ht
    exact (hFzero t ht).differentiableAt.differentiableWithinAt
  have hderiv : ∀ t ∈ Set.Ici sbar, fderivWithin ℝ F (Set.Ici sbar) t = 0 := by
    intro t ht
    simpa using HasFDerivWithinAt.fderivWithin
      (hFzero t ht).hasDerivWithinAt.hasFDerivWithinAt (uniqueDiffOn_Ici sbar t ht)
  have hF : F s = F sbar :=
    (convex_Ici sbar).is_const_of_fderivWithin_eq_zero hdiff hderiv
      hs (Set.mem_Ici.mpr le_rfl)
  have hspos : 0 < s := lt_of_lt_of_le hpositiveTime hs
  have hpow_ne : Real.rpow s (α - 1) ≠ 0 :=
    (Real.rpow_pos_of_pos hspos (α - 1)).ne'
  have hdiv := congrArg (fun v : H => (Real.rpow s (α - 1))⁻¹ • v) hF
  change x s = xLimit + (Real.rpow s (α - 1))⁻¹ • F sbar
  rw [show F s = Real.rpow s (α - 1) • (x s - xLimit) from rfl] at hdiv
  change (Real.rpow s (α - 1))⁻¹ • (Real.rpow s (α - 1) • (x s - xLimit)) =
    (Real.rpow s (α - 1))⁻¹ • F sbar at hdiv
  rw [smul_smul, inv_mul_cancel₀ hpow_ne, one_smul] at hdiv
  exact sub_eq_iff_eq_add'.mp hdiv

end AttouchAdlyDryFrictionDynamics2023
