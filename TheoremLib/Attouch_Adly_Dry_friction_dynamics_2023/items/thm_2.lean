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

private theorem gradient_monotone_of_convex {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → ℝ)
    (hconvex : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f) :
    ∀ x y : H, 0 ≤ inner ℝ (gradient f x - gradient f y) (x - y) := by
  have hgrad : ∀ x, HasGradientAt f (gradient f x) x := fun x => (hf x).hasGradientAt
  intro x y
  have hxy := convex_supporting_baillon_haddad f (gradient f) hconvex hgrad x y
  have hyx := convex_supporting_baillon_haddad f (gradient f) hconvex hgrad y x
  rw [inner_sub_left]
  have hy : inner ℝ (gradient f y) (x - y) =
      -inner ℝ (gradient f y) (y - x) := by
    rw [show x - y = -(y - x) by abel, inner_neg_right]
  have hx : inner ℝ (gradient f x) (x - y) =
      -inner ℝ (gradient f x) (y - x) := by
    rw [show x - y = -(y - x) by abel, inner_neg_right]
  linarith

/-- Along a differentiable curve, the derivative of a convex gradient has
nonnegative pairing with the curve velocity. -/
theorem gradient_derivative_inner_nonnegative {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → ℝ) (hconvex : ConvexOn ℝ Set.univ f) (hf : Differentiable ℝ f)
    (x : ℝ → H) {t : ℝ} (hx : DifferentiableAt ℝ x t)
    (hv : DifferentiableAt ℝ (fun s => gradient f (x s)) t) :
    0 ≤ inner ℝ (deriv x t) (deriv (fun s => gradient f (x s)) t) := by
  let qx : ℝ → H := fun h => h⁻¹ • (x (t + h) - x t)
  let qv : ℝ → H := fun h => h⁻¹ • (gradient f (x (t + h)) - gradient f (x t))
  have hqx : Filter.Tendsto qx (nhdsWithin 0 {0}ᶜ) (nhds (deriv x t)) := by
    simpa [qx, add_comm] using hx.hasDerivAt.tendsto_slope_zero
  have hqv : Filter.Tendsto qv (nhdsWithin 0 {0}ᶜ)
      (nhds (deriv (fun s => gradient f (x s)) t)) := by
    simpa [qv, add_comm] using hv.hasDerivAt.tendsto_slope_zero
  have hlim : Filter.Tendsto (fun h => inner ℝ (qx h) (qv h))
      (nhdsWithin 0 {0}ᶜ)
      (nhds (inner ℝ (deriv x t) (deriv (fun s => gradient f (x s)) t))) :=
    hqx.inner hqv
  rw [← neg_nonpos]
  apply le_of_tendsto hlim.neg
  rw [eventually_nhdsWithin_iff]
  refine Metric.eventually_nhds_iff.2 ⟨1, zero_lt_one, ?_⟩
  intro h _ hne
  have hmono := gradient_monotone_of_convex f hconvex hf (x (t + h)) (x t)
  dsimp only [qx, qv]
  rw [real_inner_smul_left, inner_smul_right]
  have hrewrite : h⁻¹ * (h⁻¹ * inner ℝ (x (t + h) - x t)
      (gradient f (x (t + h)) - gradient f (x t))) =
      (h⁻¹ * h⁻¹) * inner ℝ (gradient f (x (t + h)) - gradient f (x t))
        (x (t + h) - x t) := by
    rw [real_inner_comm]
    ring
  rw [hrewrite]
  exact neg_nonpos.mpr (mul_nonneg (mul_self_nonneg _) hmono)

/-- Theorem 3.1: decreasing velocity and its `o(1/t)` decay under convexity. -/
theorem theorem_3_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    {t₀ r : ℝ} (hr : 0 < r) (f : H → ℝ) (z : ℝ → H)
    (hf : ContDiff ℝ 2 f)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hsol : IsDrygradTrajectory r f z t₀)
    (hf_lower : ∃ m : ℝ, ∀ x : H, m ≤ f x) (hgradient_lip : LocallyLipschitz (gradient f))
    (hz_contdiff : ContDiff ℝ 2 z)
    (hinitial : r < ‖gradient f (z t₀)‖) :
    AntitoneOn (fun t => ‖deriv z t‖) (Set.Ici t₀) ∧
      Filter.Tendsto (fun t : ℝ => t * ‖deriv z t‖) Filter.atTop (nhds 0) := by
  have hf_diff : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hfderiv_contdiff : ContDiff ℝ 1 (fderiv ℝ f) := by
    exact (contDiff_succ_iff_fderiv.mp (show ContDiff ℝ (1 + 1) f by simpa using hf)).2.2
  have hgradient_contdiff : ContDiff ℝ 1 (gradient f) := by
    simpa [gradient, Function.comp_def] using
      (InnerProductSpace.toDual ℝ H).symm.contDiff.comp hfderiv_contdiff
  have hgradient_diff : Differentiable ℝ (gradient f) :=
    hgradient_contdiff.differentiable (by norm_num)
  have hz_diff : Differentiable ℝ z := hz_contdiff.differentiable (by norm_num)
  have hz_second_deriv : ∀ t : ℝ,
      HasDerivAt (deriv z) (deriv (deriv z) t) t := by
    intro t
    exact (hz_contdiff.differentiable_deriv_two t).hasDerivAt
  have hgrad_deriv : ∀ t : ℝ, HasDerivAt (fun s => gradient f (z s))
      (fderiv ℝ (gradient f) (z t) (deriv z t)) t := by
    intro t
    simpa [Function.comp_def] using
      (hgradient_diff (z t)).hasFDerivAt.comp_hasDerivAt t (hz_diff t).hasDerivAt
  have hHessian_nonneg : ∀ t : ℝ,
      0 ≤ inner ℝ (fderiv ℝ (gradient f) (z t) (deriv z t)) (deriv z t) := by
    intro t
    have hmono := gradient_derivative_inner_nonnegative f hconvex hf_diff z
      (hz_diff t) (hgrad_deriv t).differentiableAt
    rw [(hgrad_deriv t).deriv] at hmono
    simpa [real_inner_comm] using hmono
  have hL1 : MeasureTheory.IntegrableOn (fun t => ‖deriv z t‖) (Set.Ici t₀) := by
    rcases theorem_2_1 hr f z (hf.of_le (by norm_num)) hf_lower hgradient_lip hz_diff hinitial
      hsol with
      ⟨_, _, hL1, _⟩
    exact hL1
  have hradial : ∀ t ∈ Set.Ici t₀, deriv z t ≠ 0 →
      deriv z t + (r / ‖deriv z t‖) • deriv z t + gradient f (z t) = 0 := by
    intro t ht hv
    rcases hsol t ht with ⟨u, hu, hsum⟩
    have hu' : ∀ y : H,
        (dryFrictionPotential (H := H) r (deriv z t) : EReal) +
            (inner ℝ u (y - deriv z t) : EReal) ≤
          (dryFrictionPotential (H := H) r y : EReal) := by
      intro y
      have hy := (ERealFunction.mem_subdifferential_iff
        (dryFrictionPotential (H := H) r) (deriv z t) u).mp hu y
      simpa [real_inner_comm, add_comm] using hy
    rw [drygrad_subgradient_eq_radial hr hv hu'] at hsum
    exact hsum
  have hacc : ∀ t ∈ interior (Set.Ici t₀),
      inner ℝ (deriv (deriv z) t) (deriv z t) ≤ 0 := by
    intro t ht
    have ht₀ : t ∈ Set.Ici t₀ := interior_subset ht
    by_cases hv : deriv z t = 0
    · simp [hv]
    · have hvnorm : ‖deriv z t‖ ≠ 0 := norm_ne_zero_iff.mpr hv
      have hn : HasDerivAt (fun s => ‖deriv z s‖)
          (inner ℝ (deriv (deriv z) t) (deriv z t) / ‖deriv z t‖) t := by
        have hs := (hz_second_deriv t).norm_sq.sqrt (pow_ne_zero 2 hvnorm)
        convert hs using 1
        all_goals simp [real_inner_comm, norm_nonneg]
        all_goals field_simp
      have hc : HasDerivAt (fun s : ℝ => r / ‖deriv z s‖)
          (-(r * (inner ℝ (deriv (deriv z) t) (deriv z t) / ‖deriv z t‖)) /
            ‖deriv z t‖ ^ 2) t := by
        convert (hasDerivAt_const t r).div hn hvnorm using 1
        all_goals ring
      have hd : HasDerivAt (fun s =>
          deriv z s + (r / ‖deriv z s‖) • deriv z s + gradient f (z s))
          (deriv (deriv z) t + ((r / ‖deriv z t‖) • deriv (deriv z) t +
            (-(r * (inner ℝ (deriv (deriv z) t) (deriv z t) / ‖deriv z t‖)) /
              ‖deriv z t‖ ^ 2) • deriv z t) +
            fderiv ℝ (gradient f) (z t) (deriv z t)) t :=
        ((hz_second_deriv t).add (hc.smul (hz_second_deriv t))).add (hgrad_deriv t)
      have hneigh : ∀ᶠ s in nhds t, deriv z s ≠ 0 :=
        (hz_second_deriv t).continuousAt.eventually_ne hv
      have hEq : (fun _ : ℝ => (0 : H)) =ᶠ[nhds t]
          fun s => deriv z s + (r / ‖deriv z s‖) • deriv z s + gradient f (z s) := by
        filter_upwards [mem_interior_iff_mem_nhds.mp ht, hneigh] with s hs hsnz
        exact (hradial s hs hsnz).symm
      have hDzero : deriv (deriv z) t + ((r / ‖deriv z t‖) • deriv (deriv z) t +
          (-(r * (inner ℝ (deriv (deriv z) t) (deriv z t) / ‖deriv z t‖)) /
            ‖deriv z t‖ ^ 2) • deriv z t) +
          fderiv ℝ (gradient f) (z t) (deriv z t) = 0 := by
        exact (hd.congr_of_eventuallyEq hEq).unique (hasDerivAt_const t 0)
      have hinner := congrArg (fun w => inner ℝ w (deriv z t)) hDzero
      simp only [inner_add_left, inner_smul_left, real_inner_self_eq_norm_sq,
        inner_zero_left] at hinner
      simp at hinner
      field_simp [hvnorm] at hinner
      nlinarith [hHessian_nonneg t, norm_pos_iff.mpr hv]
  have hsq_anti : AntitoneOn (fun t => ‖deriv z t‖ ^ 2) (Set.Ici t₀) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici t₀)
      (fun t _ => ((hz_second_deriv t).continuousAt.norm).continuousWithinAt.pow 2)
    · intro t ht
      exact (hz_second_deriv t).norm_sq.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hz_second_deriv t).norm_sq.deriv]
      rw [real_inner_comm]
      nlinarith [hacc t ht]
  have hspeed : AntitoneOn (fun t => ‖deriv z t‖) (Set.Ici t₀) := by
    intro s hs t ht hst
    nlinarith [hsq_anti hs ht hst, norm_nonneg (deriv z s), norm_nonneg (deriv z t)]
  exact ⟨hspeed, lemma_3_1 (fun t => ‖deriv z t‖) (fun _ _ => norm_nonneg _) hspeed hL1⟩

end AttouchAdlyDryFrictionDynamics2023
