import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.thm_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_lem_1

namespace AttouchAdlyDryFrictionDynamics2023

private theorem drygrad_subgradient_eq_radial {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {r : ℝ} (hr : 0 < r) {v u : H} (hv : v ≠ 0)
    (hu : ∀ y : H,
      (dryFrictionPotential (H := H) r v : EReal) +
          (inner ℝ u (y - v) : EReal) ≤
        (dryFrictionPotential (H := H) r y : EReal)) :
    u = (r / ‖v‖) • v := by
  obtain ⟨hwork, hnorm_le⟩ := drygrad_subgradient_radial hr hu
  have hvnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hcs : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm _ _
  have hnorm_ge : r ≤ ‖u‖ := by
    rw [hwork] at hcs
    nlinarith
  have hnorm : ‖u‖ = r := le_antisymm hnorm_le hnorm_ge
  have heq : inner ℝ u v = ‖u‖ * ‖v‖ := by simpa [hnorm] using hwork
  have hsmul : ‖v‖ • u = ‖u‖ • v := inner_eq_norm_mul_iff_real.mp heq
  rw [hnorm] at hsmul
  calc
    u = ‖v‖⁻¹ • (‖v‖ • u) := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hvnorm_pos), one_smul]
    _ = ‖v‖⁻¹ • (r • v) := by rw [hsmul]
    _ = (r / ‖v‖) • v := by
      rw [smul_smul, show ‖v‖⁻¹ * r = r / ‖v‖ by field_simp]

/-- Theorem 3.1: decreasing velocity and its `o(1/t)` decay under convexity. -/
theorem theorem_3_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    {t₀ r : ℝ} (hr : 0 < r) (f : H → ℝ) (fgrad : H → H) (z dz : ℝ → H)
    (_hconvex : ConvexOn ℝ Set.univ f)
    (hgradient : ∀ x v, fderiv ℝ f x v = inner ℝ (fgrad x) v)
    (hsol : IsDrygradTrajectory r hr fgrad z dz t₀)
    (hf_lower : ∃ m : ℝ, ∀ x : H, m ≤ f x) (hfgrad_lip : LocallyLipschitz fgrad)
    (hinitial : r < ‖fgrad (z t₀)‖)
    (hchain : ∀ t ∈ Set.Ici t₀,
      HasDerivAt (fun s => f (z s)) (inner ℝ (fgrad (z t)) (dz t)) t)
    (hcomp_cont : ContinuousOn (fun t => f (z t)) (Set.Ici t₀))
    (V : H → H) (hV_lip : LocallyLipschitz V)
    (hV_zero : ∀ x, V x = 0 ↔ ‖fgrad x‖ ≤ r)
    (hvelocity : ∀ t ∈ Set.Ici t₀, dz t = V (z t))
    (hvelocity_limit : Filter.Tendsto dz Filter.atTop (nhds 0))
    (hstationary : ∀ S ∈ Set.Ici t₀, V (z S) = 0 →
      ∀ t ∈ Set.Ici S, z t = z S)
    (ddz : ℝ → H) (A : ℝ → H → H)
    (hdz_deriv : ∀ t ∈ Set.Ici t₀, HasDerivAt dz (ddz t) t)
    (hgrad_deriv : ∀ t ∈ Set.Ici t₀,
      HasDerivAt (fun s => fgrad (z s)) (A t (dz t)) t)
    (hA_nonneg : ∀ t ∈ Set.Ici t₀, 0 ≤ inner ℝ (A t (dz t)) (dz t)) :
    AntitoneOn (fun t => ‖dz t‖) (Set.Ici t₀) ∧
      Filter.Tendsto (fun t : ℝ => t * ‖dz t‖) Filter.atTop (nhds 0) := by
  have hL1 : MeasureTheory.IntegrableOn (fun t => ‖dz t‖) (Set.Ici t₀) := by
    rcases theorem_2_1 hr f fgrad z dz hgradient hf_lower hfgrad_lip hinitial hchain
      hcomp_cont hsol V hV_lip hV_zero hvelocity hvelocity_limit hstationary with
      ⟨_, _, hL1, _⟩
    exact hL1
  have hradial : ∀ t ∈ Set.Ici t₀, dz t ≠ 0 →
      dz t + (r / ‖dz t‖) • dz t + fgrad (z t) = 0 := by
    intro t ht hv
    rcases hsol t ht with ⟨_, u, hu, hsum⟩
    rw [drygrad_subgradient_eq_radial hr hv hu] at hsum
    exact hsum
  have hacc : ∀ t ∈ interior (Set.Ici t₀), inner ℝ (ddz t) (dz t) ≤ 0 := by
    intro t ht
    have ht₀ : t ∈ Set.Ici t₀ := interior_subset ht
    by_cases hv : dz t = 0
    · simp [hv]
    · have hvnorm : ‖dz t‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hn : HasDerivAt (fun s => ‖dz s‖)
          (inner ℝ (ddz t) (dz t) / ‖dz t‖) t := by
        have hs := (hdz_deriv t ht₀).norm_sq.sqrt (pow_ne_zero 2 hvnorm)
        convert hs using 1
        all_goals simp [real_inner_comm, norm_nonneg]
        all_goals field_simp
      have hc : HasDerivAt (fun s : ℝ => r / ‖dz s‖)
          (-(r * (inner ℝ (ddz t) (dz t) / ‖dz t‖)) / ‖dz t‖ ^ 2) t := by
        convert (hasDerivAt_const t r).div hn hvnorm using 1
        all_goals ring
      have hd : HasDerivAt (fun s =>
          dz s + (r / ‖dz s‖) • dz s + fgrad (z s))
          (ddz t + ((r / ‖dz t‖) • ddz t +
            (-(r * (inner ℝ (ddz t) (dz t) / ‖dz t‖)) / ‖dz t‖ ^ 2) • dz t) +
            A t (dz t)) t :=
        ((hdz_deriv t ht₀).add (hc.smul (hdz_deriv t ht₀))).add (hgrad_deriv t ht₀)
      have hneigh : ∀ᶠ s in nhds t, dz s ≠ 0 :=
        (hdz_deriv t ht₀).continuousAt.eventually_ne hv
      have hEq : (fun _ : ℝ => (0 : H)) =ᶠ[nhds t]
          fun s => dz s + (r / ‖dz s‖) • dz s + fgrad (z s) := by
        filter_upwards [mem_interior_iff_mem_nhds.mp ht, hneigh] with s hs hsnz
        exact (hradial s hs hsnz).symm
      have hDzero : ddz t + ((r / ‖dz t‖) • ddz t +
          (-(r * (inner ℝ (ddz t) (dz t) / ‖dz t‖)) / ‖dz t‖ ^ 2) • dz t) +
          A t (dz t) = 0 := by
        exact (hd.congr_of_eventuallyEq hEq).unique (hasDerivAt_const t 0)
      have hinner := congrArg (fun w => inner ℝ w (dz t)) hDzero
      simp only [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq,
        inner_zero_left] at hinner
      simp at hinner
      field_simp [hvnorm] at hinner
      nlinarith [hA_nonneg t ht₀, norm_pos_iff.mpr hv]
  have hsq_anti : AntitoneOn (fun t => ‖dz t‖ ^ 2) (Set.Ici t₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici t₀)
      (fun t ht => ((hdz_deriv t ht).continuousAt.norm).continuousWithinAt.pow 2)
    · intro t ht
      exact ((hdz_deriv t (interior_subset ht)).norm_sq).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [((hdz_deriv t (interior_subset ht)).norm_sq).deriv]
      rw [real_inner_comm]
      nlinarith [hacc t ht]
  have hspeed : AntitoneOn (fun t => ‖dz t‖) (Set.Ici t₀) := by
    intro s hs t ht hst
    nlinarith [hsq_anti hs ht hst, norm_nonneg (dz s), norm_nonneg (dz t)]
  exact ⟨hspeed, lemma_3_1 (fun t => ‖dz t‖) (fun _ _ => norm_nonneg _) hspeed hL1⟩

end AttouchAdlyDryFrictionDynamics2023
