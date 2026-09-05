import Mathlib
import Foundation.Differentiation.ODE
import Foundation.FixedPoint.Nonexpansive
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_3

namespace AttouchAdlyDryFrictionDynamics2023

private theorem hasDerivAt_comp_gradient {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {f : H → ℝ} {z : ℝ → H}
    (hf : Differentiable ℝ f) (hz_diff : Differentiable ℝ z) (t : ℝ) :
    HasDerivAt (fun s => f (z s)) (inner ℝ (gradient f (z t)) (deriv z t)) t := by
  have hgradient : ∀ x v, fderiv ℝ f x v = inner ℝ (gradient f x) v := by
    intro x v
    rw [(hf x).hasGradientAt.hasFDerivAt.fderiv]
    rfl
  have hcomp := (hf (z t)).hasFDerivAt.comp_hasDerivAt t (hz_diff t).hasDerivAt
  simpa [Function.comp_def, hgradient] using hcomp

private theorem drygrad_subgradient_work_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {r : ℝ} {v u : H}
    (hu : ∀ y : H,
      (dryFrictionPotential (H := H) r v : EReal) +
          (inner ℝ u (y - v) : EReal) ≤
        (dryFrictionPotential (H := H) r y : EReal)) :
    r * ‖v‖ ≤ inner ℝ u v := by
  have hzero := hu 0
  norm_num [dryFrictionPotential] at hzero
  have hreal : r * ‖v‖ - inner ℝ u v ≤ 0 := by
    exact_mod_cast hzero
  linarith

/-- A subgradient of `v ↦ r * ‖v‖` has the expected radial work and norm bounds. -/
theorem drygrad_subgradient_radial {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {r : ℝ} (hr : 0 < r) {v u : H}
    (hu : ∀ y : H,
      (dryFrictionPotential (H := H) r v : EReal) +
          (inner ℝ u (y - v) : EReal) ≤
        (dryFrictionPotential (H := H) r y : EReal)) :
    inner ℝ u v = r * ‖v‖ ∧ ‖u‖ ≤ r := by
  have hlower : r * ‖v‖ ≤ inner ℝ u v :=
    drygrad_subgradient_work_le hu
  have htwo := hu ((2 : ℝ) • v)
  norm_num [dryFrictionPotential] at htwo
  have hupper : inner ℝ u v ≤ r * ‖v‖ := by
    have htwo_real : r * ‖v‖ + inner ℝ u ((2 : ℝ) • v - v) ≤ r * ‖(2 : ℝ) • v‖ := by
      exact_mod_cast htwo
    have htwo_simplified : r * ‖v‖ + inner ℝ u v ≤ 2 * (r * ‖v‖) := by
      rw [show (2 : ℝ) • v - v = v by module] at htwo_real
      have hnorm : ‖(2 : ℝ) • v‖ = 2 * ‖v‖ := by
        rw [norm_smul]
        norm_num
      rw [hnorm] at htwo_real
      nlinarith

    linarith
  have hwork : inner ℝ u v = r * ‖v‖ := le_antisymm hupper hlower
  constructor
  · exact hwork
  · have hforall : ∀ y : H, inner ℝ u y ≤ r * ‖y‖ := by
      intro y
      have hy := hu y
      have hy_real : r * ‖v‖ + inner ℝ u (y - v) ≤ r * ‖y‖ := by
        exact_mod_cast hy
      rw [inner_sub_right, hwork] at hy_real
      linarith
    have huu := hforall u
    rw [real_inner_self_eq_norm_sq] at huu
    by_cases hu0 : ‖u‖ = 0
    · simp [hu0, le_of_lt hr]
    · have hu_pos : 0 < ‖u‖ := (norm_pos_iff.mpr (by simpa using hu0))
      nlinarith

/-- The DRYGRAD inclusion is equivalent to the soft-thresholded velocity formula. -/
theorem drygrad_velocity_formula {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {r : ℝ} (hr : 0 < r) {v g : H}
    (hsol : ∃ u : H,
      u ∈ ERealFunction.subdifferential (dryFrictionPotential (H := H) r) v ∧
        v + u + g = 0) :
    v = -softThresholder r g := by
  rcases hsol with ⟨u, hsub, hforce⟩
  have hu : ∀ y : H,
      (dryFrictionPotential (H := H) r v : EReal) +
          (inner ℝ u (y - v) : EReal) ≤
        (dryFrictionPotential (H := H) r y : EReal) := by
    intro y
    have hy := (ERealFunction.mem_subdifferential_iff
      (dryFrictionPotential (H := H) r) v u).mp hsub y
    simpa [real_inner_comm, add_comm] using hy
  obtain ⟨hwork, hunorm⟩ := drygrad_subgradient_radial hr hu
  by_cases hv : v = 0
  · have hgrad : g = -u := by
      rw [hv] at hforce
      apply eq_neg_of_add_eq_zero_left
      simpa [add_comm] using hforce
    have hnormg : ‖g‖ ≤ r := by
      rw [hgrad, norm_neg]
      exact hunorm
    rw [softThresholder_apply, if_neg (not_lt_of_ge hnormg)]
    simp [hv]
  · have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hcs : inner ℝ u v ≤ ‖u‖ * ‖v‖ := real_inner_le_norm _ _
    have hnorm_ge : r ≤ ‖u‖ := by
      rw [hwork] at hcs
      nlinarith
    have hnorm : ‖u‖ = r := le_antisymm hunorm hnorm_ge
    have heq : inner ℝ u v = ‖u‖ * ‖v‖ := by simpa [hnorm] using hwork
    have hsmul : ‖v‖ • u = ‖u‖ • v := inner_eq_norm_mul_iff_real.mp heq
    rw [hnorm] at hsmul
    have hu_eq : u = (r / ‖v‖) • v := by
      calc
        u = ‖v‖⁻¹ • (‖v‖ • u) := by
          rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hvnorm), one_smul]
        _ = ‖v‖⁻¹ • (r • v) := by rw [hsmul]
        _ = (r / ‖v‖) • v := by
          rw [smul_smul, show ‖v‖⁻¹ * r = r / ‖v‖ by field_simp]
    have hg : g = -(1 + r / ‖v‖) • v := by
      calc
        g = -(v + u) := by
          apply eq_neg_of_add_eq_zero_left
          simpa [add_assoc, add_comm, add_left_comm] using hforce
        _ = -(v + (r / ‖v‖) • v) := by rw [hu_eq]
        _ = -(1 + r / ‖v‖) • v := by module
    have hgnorm : ‖g‖ = ‖v‖ + r := by
      rw [hg, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg]
      · field_simp
      · positivity
    have hgr : r < ‖g‖ := by rw [hgnorm]; linarith
    have hsoft : softThresholder r g = -v := by
      have hnorm_expr : ‖-(1 + r / ‖v‖) • v‖ = ‖v‖ + r := by
        rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_nonneg]
        · field_simp
        · positivity
      rw [softThresholder_apply, if_pos hgr, hg, hnorm_expr, smul_smul]
      have hcoef : (1 - r / (‖v‖ + r)) * -(1 + r / ‖v‖) = -1 := by
        field_simp [ne_of_gt hvnorm, ne_of_gt (by linarith : 0 < ‖v‖ + r)]
        ring
      rw [hcoef]
      simpa using (neg_one_smul ℝ v)
    rw [hsoft]
    simp

private theorem drygrad_energy_deriv_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {t₀ r : ℝ} (f : H → ℝ)
    (z : ℝ → H) (hr : 0 < r) (hf : Differentiable ℝ f)
    (hz_diff : Differentiable ℝ z) (hsol : IsDrygradTrajectory r f z t₀)
    {t : ℝ} (ht : t ∈ Set.Ici t₀) :
    ‖deriv z t‖ ^ 2 + r * ‖deriv z t‖ + deriv (fun s => f (z s)) t ≤ 0 := by
  have hsol_t := hsol t ht
  obtain ⟨u, hsub, hsum⟩ := hsol_t
  have hu : ∀ y : H,
      (dryFrictionPotential (H := H) r (deriv z t) : EReal) +
          (inner ℝ u (y - deriv z t) : EReal) ≤
        (dryFrictionPotential (H := H) r y : EReal) := by
    intro y
    have hy := (ERealFunction.mem_subdifferential_iff
      (dryFrictionPotential (H := H) r) (deriv z t) u).mp hsub y
    simpa [real_inner_comm, add_comm] using hy
  have hwork : r * ‖deriv z t‖ ≤ inner ℝ u (deriv z t) :=
    drygrad_subgradient_work_le hu
  have hinner := congrArg (fun w => inner ℝ w (deriv z t)) hsum
  simp only [inner_add_left, real_inner_self_eq_norm_sq, inner_zero_left] at hinner
  have hderiv : deriv (fun s => f (z s)) t = inner ℝ (gradient f (z t)) (deriv z t) :=
    (hasDerivAt_comp_gradient hf hz_diff t).deriv
  rw [hderiv]
  nlinarith

private theorem drygrad_energy_antitone {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {t₀ r : ℝ} (f : H → ℝ)
    (z : ℝ → H) (hr : 0 < r) (hf : Differentiable ℝ f)
    (hz_diff : Differentiable ℝ z) (hsol : IsDrygradTrajectory r f z t₀) :
    AntitoneOn (fun t => f (z t)) (Set.Ici t₀) := by
  have hcont : ContinuousOn (fun t => f (z t)) (Set.Ici t₀) :=
    hf.continuous.comp_continuousOn hz_diff.continuous.continuousOn
  apply antitoneOn_of_deriv_nonpos (convex_Ici t₀) hcont
  · intro t ht
    exact (hasDerivAt_comp_gradient hf hz_diff t).differentiableAt.differentiableWithinAt
  · intro t ht
    have henergy := drygrad_energy_deriv_le f z hr hf hz_diff hsol (interior_subset ht)
    have hsq : 0 ≤ ‖deriv z t‖ ^ 2 := sq_nonneg _
    have hnorm : 0 ≤ r * ‖deriv z t‖ := mul_nonneg (le_of_lt hr) (norm_nonneg _)
    linarith

/-- A continuous nonnegative function with uniformly bounded prefix integrals is integrable. -/
private theorem integrableOn_Ici_of_nonneg_prefix_bound {g : ℝ → ℝ} {t₀ B : ℝ}
    (hgcont : ContinuousOn g (Set.Ici t₀))
    (hgnonneg : ∀ t ∈ Set.Ici t₀, 0 ≤ g t)
    (hprefix : ∀ T, t₀ ≤ T → ∫ t in t₀..T, g t ≤ B) :
    MeasureTheory.IntegrableOn g (Set.Ici t₀) := by
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  apply MeasureTheory.integrableOn_Ioi_of_intervalIntegral_norm_bounded
    (l := Filter.atTop) B t₀ (b := fun n : ℕ => max t₀ n)
  · intro n
    rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le
      (le_max_left _ _)]
    exact (hgcont.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc
      (le_max_left _ _)
  · exact Filter.tendsto_atTop_mono (fun n => le_max_right t₀ (n : ℝ))
      tendsto_natCast_atTop_atTop
  · filter_upwards [] with n
    have hnorm : (∫ t : ℝ in t₀..max t₀ n, ‖g t‖) =
        ∫ t : ℝ in t₀..max t₀ n, g t := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [] with t ht
      rw [Set.uIoc_of_le (le_max_left _ _)] at ht
      exact Real.norm_of_nonneg (hgnonneg t ht.1.le)
    rw [hnorm]
    exact hprefix _ (le_max_left _ _)

/-- Theorem 2.1: descent, finite energy and length, and convergence for a DRYGRAD trajectory. -/
theorem theorem_2_1 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] {t₀ r : ℝ} (hr : 0 < r) (f : H → ℝ)
    (z : ℝ → H) (hf : ContDiff ℝ 1 f)
    (hf_lower : ∃ m : ℝ, ∀ x : H, m ≤ f x)
    (hgradient_lip : LocallyLipschitz (gradient f))
    (hz_diff : Differentiable ℝ z)
    (hinitial : r < ‖gradient f (z t₀)‖)
    (hsol : IsDrygradTrajectory r f z t₀) :
    AntitoneOn (fun t => f (z t)) (Set.Ici t₀) ∧
      MeasureTheory.IntegrableOn (fun t => ‖deriv z t‖ ^ 2) (Set.Ici t₀) ∧
      MeasureTheory.IntegrableOn (fun t => ‖deriv z t‖) (Set.Ici t₀) ∧
      ∃ zLimit, Filter.Tendsto z Filter.atTop (nhds zLimit) ∧ ‖gradient f zLimit‖ = r ∧
        ((∃ T ∈ Set.Ici t₀, ∀ t ∈ Set.Ici T, z t = zLimit) ∨
          ∀ t ∈ Set.Ici t₀, r < ‖gradient f (z t)‖) := by
  let V : H → H := fun x => -softThresholder r (gradient f x)
  have hsoft_lip : LipschitzWith 1 (softThresholder r : H → H) :=
    lipschitzWith_one_of_firmlyNonexpansive (softThresholder_firmlyNonexpansive r hr)
  have hV_lip : LocallyLipschitz V := by
    have hneg : LocallyLipschitz (fun x : H => -x) :=
      LipschitzWith.id.neg.locallyLipschitz
    simpa [V, Function.comp_def] using
      hneg.comp (hsoft_lip.locallyLipschitz.comp hgradient_lip)
  have hV_zero : ∀ x, V x = 0 ↔ ‖gradient f x‖ ≤ r := by
    intro x
    constructor
    · intro hx
      by_contra hnot
      have hlt : r < ‖gradient f x‖ := lt_of_not_ge hnot
      have hgrad : gradient f x ≠ 0 := by
        exact norm_ne_zero_iff.mp (ne_of_gt (lt_trans hr hlt))
      have hcoef : 1 - r / ‖gradient f x‖ ≠ 0 := by
        apply ne_of_gt
        rw [sub_pos, div_lt_one (lt_trans hr hlt)]
        exact hlt
      change -softThresholder r (gradient f x) = 0 at hx
      rw [softThresholder_apply, if_pos hlt] at hx
      exact (neg_ne_zero.mpr (smul_ne_zero hcoef hgrad)) hx
    · intro hx
      simp [V, softThresholder_apply, if_neg (not_lt_of_ge hx)]
  have hvelocity : ∀ t ∈ Set.Ici t₀, deriv z t = V (z t) := by
    intro t ht
    exact drygrad_velocity_formula hr (hsol t ht)
  have hV_ode_lip : ∀ x, ∃ U ∈ nhds x, ∃ L : ℝ, 0 ≤ L ∧
      ∀ y ∈ U, ∀ w ∈ U, ‖V y - V w‖ ≤ L * ‖y - w‖ := by
    intro x
    rcases hV_lip x with ⟨K, U, hU, hKU⟩
    refine ⟨U, hU, K, K.coe_nonneg, ?_⟩
    intro y hy w hw
    simpa [dist_eq_norm] using hKU.dist_le_mul y hy w hw
  have hstationary : ∀ S ∈ Set.Ici t₀, V (z S) = 0 →
      ∀ t ∈ Set.Ici S, z t = z S := by
    intro S hS hVS t ht
    have hSstrict : t₀ < S := by
      have hSne : t₀ ≠ S := by
        intro heq
        subst S
        have hball := (hV_zero (z t₀)).mp hVS
        exact (not_lt_of_ge hball) hinitial
      exact lt_of_le_of_ne hS hSne
    have hzode : ∀ s ∈ Set.Ioo t₀ (t + 1), HasDerivAt z (V (z s)) s := by
      intro s hs
      rw [← hvelocity s hs.1.le]
      exact (hz_diff s).hasDerivAt
    have hconstode : ∀ s ∈ Set.Ioo t₀ (t + 1),
        HasDerivAt (fun _ : ℝ => z S) (V (z S)) s := by
      intro s _
      simpa [hVS] using (hasDerivAt_const s (z S))
    have heq := ode_eqOn_Ioo_of_locally_lipschitz V hV_ode_lip
      (show S ∈ Set.Ioo t₀ (t + 1) by
        exact ⟨hSstrict, lt_of_le_of_lt ht (by linarith)⟩)
      z (fun _ : ℝ => z S) hzode hconstode rfl
    exact heq ⟨lt_of_lt_of_le hSstrict ht, by linarith⟩
  have hanti : AntitoneOn (fun t => f (z t)) (Set.Ici t₀) :=
    drygrad_energy_antitone f z hr (hf.differentiable (by norm_num)) hz_diff hsol
  have hchain : ∀ t ∈ Set.Ici t₀,
      HasDerivAt (fun s => f (z s)) (inner ℝ (gradient f (z t)) (deriv z t)) t := by
    intro t _
    exact hasDerivAt_comp_gradient (hf.differentiable (by norm_num)) hz_diff t
  have hVcont : Continuous V := hV_lip.continuous
  have hzcont : ContinuousOn z (Set.Ici t₀) := by
    intro t ht
    exact (hz_diff t).continuousAt.continuousWithinAt
  have hdzcont : ContinuousOn (deriv z) (Set.Ici t₀) := by
    have hVz : ContinuousOn (fun t => V (z t)) (Set.Ici t₀) :=
      hVcont.comp_continuousOn hzcont
    exact hVz.congr (by
      intro t ht
      exact hvelocity t ht)
  have hnormcont : ContinuousOn (fun t => ‖deriv z t‖) (Set.Ici t₀) := hdzcont.norm
  have hsqcont : ContinuousOn (fun t => ‖deriv z t‖ ^ 2) (Set.Ici t₀) :=
    hnormcont.pow 2
  obtain ⟨m, hm⟩ := hf_lower
  have hprefix : ∀ T : ℝ, t₀ ≤ T →
      ∫ t in t₀..T, (‖deriv z t‖ ^ 2 + r * ‖deriv z t‖) ≤ f (z t₀) - m := by
    intro T hT
    have hfgcont : ContinuousOn (fun t => gradient f (z t)) (Set.Icc t₀ T) :=
      hgradient_lip.continuous.comp_continuousOn (hzcont.mono Set.Icc_subset_Ici_self)
    have hdzIcc : ContinuousOn (deriv z) (Set.Icc t₀ T) := hdzcont.mono Set.Icc_subset_Ici_self
    have hintercont : ContinuousOn (fun t => inner ℝ (gradient f (z t)) (deriv z t))
        (Set.Icc t₀ T) := hfgcont.inner hdzIcc
    have hderivcont : ContinuousOn (deriv (fun s => f (z s))) (Set.Icc t₀ T) :=
      hintercont.congr (by
        intro t ht
        exact (hchain t (Set.Icc_subset_Ici_self ht)).deriv)
    have hleftint : IntervalIntegrable (fun t => ‖deriv z t‖ ^ 2 + r * ‖deriv z t‖)
        MeasureTheory.volume t₀ T := by
      apply ContinuousOn.intervalIntegrable_of_Icc hT
      exact hsqcont.mono Set.Icc_subset_Ici_self |>.add
        ((continuousOn_const.mul (hnormcont.mono Set.Icc_subset_Ici_self)))
    have hrightint : IntervalIntegrable (fun t => - deriv (fun s => f (z s)) t)
        MeasureTheory.volume t₀ T :=
      (hderivcont.neg).intervalIntegrable_of_Icc hT
    have hpoint : ∀ t ∈ Set.Icc t₀ T,
        ‖deriv z t‖ ^ 2 + r * ‖deriv z t‖ ≤ - deriv (fun s => f (z s)) t := by
      intro t ht
      have h := drygrad_energy_deriv_le f z hr (hf.differentiable (by norm_num)) hz_diff hsol
        (Set.Icc_subset_Ici_self ht)
      linarith
    have hint := intervalIntegral.integral_mono_on hT hleftint hrightint hpoint
    have hftc : ∫ t in t₀..T, deriv (fun s => f (z s)) t = f (z T) - f (z t₀) :=
      intervalIntegral.integral_deriv_eq_sub
        (fun t ht => by
          rw [Set.uIcc_of_le hT] at ht
          exact (hchain t (Set.Icc_subset_Ici_self ht)).differentiableAt)
        (hderivcont.intervalIntegrable_of_Icc hT)
    rw [intervalIntegral.integral_neg, hftc] at hint
    have hbound : f (z t₀) - f (z T) ≤ f (z t₀) - m := by linarith [hm (z T)]
    calc
      ∫ t in t₀..T, (‖deriv z t‖ ^ 2 + r * ‖deriv z t‖) ≤
          -(f (z T) - f (z t₀)) := hint
      _ = f (z t₀) - f (z T) := by ring
      _ ≤ f (z t₀) - m := hbound
  have hsqprefix : ∀ T : ℝ, t₀ ≤ T → ∫ t in t₀..T, ‖deriv z t‖ ^ 2 ≤ f (z t₀) - m := by
    intro T hT
    have hnonneg : 0 ≤ ∫ t in t₀..T, r * ‖deriv z t‖ :=
      intervalIntegral.integral_nonneg hT (fun t _ => mul_nonneg hr.le (norm_nonneg _))
    have hadd := hprefix T hT
    have hadd' : (∫ t in t₀..T, ‖deriv z t‖ ^ 2) +
        (∫ t in t₀..T, r * ‖deriv z t‖) ≤ f (z t₀) - m := by
      calc
        (∫ t in t₀..T, ‖deriv z t‖ ^ 2) + (∫ t in t₀..T, r * ‖deriv z t‖) =
            ∫ t in t₀..T, (‖deriv z t‖ ^ 2 + r * ‖deriv z t‖) :=
          (intervalIntegral.integral_add
            ((hsqcont.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hT)
            ((continuousOn_const.mul (hnormcont.mono Set.Icc_subset_Ici_self)).intervalIntegrable_of_Icc hT)).symm
        _ ≤ f (z t₀) - m := hadd
    linarith
  have hnormprefix : ∀ T : ℝ, t₀ ≤ T → ∫ t in t₀..T, ‖deriv z t‖ ≤ (f (z t₀) - m) / r := by
    intro T hT
    have hnonneg : 0 ≤ ∫ t in t₀..T, ‖deriv z t‖ ^ 2 :=
      intervalIntegral.integral_nonneg hT (fun t _ => sq_nonneg _)
    have hadd := hprefix T hT
    have hadd' : (∫ t in t₀..T, ‖deriv z t‖ ^ 2) +
        r * (∫ t in t₀..T, ‖deriv z t‖) ≤ f (z t₀) - m := by
      rw [← intervalIntegral.integral_const_mul]
      calc
        (∫ t in t₀..T, ‖deriv z t‖ ^ 2) + (∫ t in t₀..T, r * ‖deriv z t‖) =
            ∫ t in t₀..T, (‖deriv z t‖ ^ 2 + r * ‖deriv z t‖) :=
          (intervalIntegral.integral_add
            ((hsqcont.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hT)
            ((continuousOn_const.mul (hnormcont.mono Set.Icc_subset_Ici_self)).intervalIntegrable_of_Icc hT)).symm
        _ ≤ f (z t₀) - m := hadd
    exact (le_div_iff₀ hr).mpr (by linarith)
  have hsqint : MeasureTheory.IntegrableOn (fun t => ‖deriv z t‖ ^ 2) (Set.Ici t₀) :=
    integrableOn_Ici_of_nonneg_prefix_bound hsqcont (fun _ _ => sq_nonneg _) hsqprefix
  have hnormint : MeasureTheory.IntegrableOn (fun t => ‖deriv z t‖) (Set.Ici t₀) :=
    integrableOn_Ici_of_nonneg_prefix_bound hnormcont (fun _ _ => norm_nonneg _) hnormprefix
  refine ⟨hanti, hsqint, hnormint, ?_⟩
  let zLimit := Filter.atTop.limUnder z
  have hnormint' : MeasureTheory.IntegrableOn (fun t => ‖deriv z t‖) (Set.Ioi t₀) := by
    rw [← integrableOn_Ici_iff_integrableOn_Ioi]
    exact hnormint
  have hdzint' : MeasureTheory.IntegrableOn (deriv z) (Set.Ioi t₀) := by
    rw [MeasureTheory.IntegrableOn]
    apply (MeasureTheory.integrable_norm_iff
      ((hdzcont.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)).mp
    exact hnormint'.integrable
  have hzlim : Filter.Tendsto z Filter.atTop (nhds zLimit) :=
    MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi
      (f := z) (f' := deriv z) (a := t₀)
        (fun t ht => (hz_diff t).hasDerivAt) hdzint'
  have hVzlim : Filter.Tendsto (fun t => V (z t)) Filter.atTop (nhds (V zLimit)) :=
    (hVcont.tendsto zLimit).comp hzlim
  have hVnormint : MeasureTheory.IntegrableOn (fun t => ‖V (z t)‖) (Set.Ici t₀) :=
    hnormint.congr_fun (fun t ht => congrArg norm (hvelocity t ht)) measurableSet_Ici
  have hVzero_from_integrability : V zLimit = 0 := by
    by_contra hne
    let c : ℝ := ‖V zLimit‖ / 2
    have hc : 0 < c := by
      dsimp [c]
      exact half_pos (norm_pos_iff.mpr hne)
    have hVnormlim : Filter.Tendsto (fun t => ‖V (z t)‖) Filter.atTop
        (nhds ‖V zLimit‖) := hVzlim.norm
    have hevent : ∀ᶠ t in Filter.atTop, c < ‖V (z t)‖ :=
      (tendsto_order.1 hVnormlim).1 c (by dsimp [c]; linarith [norm_pos_iff.mpr hne])
    rcases Filter.eventually_atTop.1 hevent with ⟨T, hT⟩
    let A := max t₀ T
    have htailint : MeasureTheory.IntegrableOn (fun t => ‖V (z t)‖) (Set.Ici A) :=
      hVnormint.mono_set (Set.Ici_subset_Ici.mpr (le_max_left t₀ T))
    have hconstint : MeasureTheory.IntegrableOn (fun _ : ℝ => c) (Set.Ici A) := by
      rw [MeasureTheory.IntegrableOn] at htailint ⊢
      apply MeasureTheory.Integrable.mono' htailint
      · exact MeasureTheory.aestronglyMeasurable_const
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with t ht
        rw [Real.norm_of_nonneg hc.le]
        exact (hT t (le_trans (le_max_right t₀ T) ht)).le
    exact (by
      simp [MeasureTheory.integrableOn_const_iff, hc.ne'] :
        ¬ MeasureTheory.IntegrableOn (fun _ : ℝ => c) (Set.Ici A)) hconstint
  have hvelocity_limit : Filter.Tendsto (deriv z) Filter.atTop (nhds 0) := by
    have hVlimit : Filter.Tendsto (fun t => V (z t)) Filter.atTop (nhds 0) := by
      simpa [hVzero_from_integrability] using hVzlim
    apply hVlimit.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨t₀, fun t ht => ht⟩] with t ht
    exact (hvelocity t ht).symm
  have hdzV : Filter.Tendsto (fun t => V (z t)) Filter.atTop (nhds 0) := by
    apply hvelocity_limit.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨t₀, fun t ht => ht⟩] with t ht
    exact hvelocity t ht
  have hVzero : V zLimit = 0 := tendsto_nhds_unique hVzlim hdzV
  have hball : ‖gradient f zLimit‖ ≤ r := (hV_zero zLimit).mp hVzero
  have hqcont : Continuous (fun x : H => ‖gradient f x‖) := hgradient_lip.continuous.norm
  have hqlim : Filter.Tendsto (fun t => ‖gradient f (z t)‖) Filter.atTop
      (nhds ‖gradient f zLimit‖) := (hqcont.tendsto zLimit).comp hzlim
  by_cases hhit : ∃ T ∈ Set.Ici t₀, ‖gradient f (z T)‖ ≤ r
  · rcases hhit with ⟨T, hT, hTball⟩
    have hqIcc : ContinuousOn (fun t => ‖gradient f (z t)‖) (Set.Icc t₀ T) :=
      hqcont.comp_continuousOn (hzcont.mono Set.Icc_subset_Ici_self)
    have hrmem : r ∈ Set.Icc (‖gradient f (z T)‖) (‖gradient f (z t₀)‖) :=
      ⟨hTball, hinitial.le⟩
    rcases intermediate_value_Icc' hT hqIcc hrmem with ⟨S, hS, hqS⟩
    have hVSzero : V (z S) = 0 := (hV_zero (z S)).mpr (le_of_eq hqS)
    have hev : z =ᶠ[Filter.atTop] fun _ : ℝ => z S := by
      filter_upwards [Filter.eventually_atTop.2 ⟨S, fun t ht => ht⟩] with t ht
      exact hstationary S hS.1 hVSzero t ht
    have hzS : Filter.Tendsto z Filter.atTop (nhds (z S)) :=
      tendsto_const_nhds.congr' hev.symm
    have hzEq : zLimit = z S := tendsto_nhds_unique hzlim hzS
    refine ⟨zLimit, hzlim, ?_, Or.inl ⟨S, hS.1, ?_⟩⟩
    · rw [hzEq]
      exact hqS
    · intro t ht
      rw [hzEq]
      exact hstationary S hS.1 hVSzero t ht
  · have hexterior : ∀ t ∈ Set.Ici t₀, r < ‖gradient f (z t)‖ := by
      intro t ht
      exact lt_of_not_ge (fun h => hhit ⟨t, ht, h⟩)
    have hlower : r ≤ ‖gradient f zLimit‖ := by
      by_contra hnot
      have hless : ‖gradient f zLimit‖ < r := lt_of_not_ge hnot
      have hevent : ∀ᶠ t in Filter.atTop, ‖gradient f (z t)‖ < r :=
        (tendsto_order.1 hqlim).2 r hless
      have htail : ∀ᶠ t in Filter.atTop, t ∈ Set.Ici t₀ :=
        Filter.eventually_atTop.2 ⟨t₀, fun t ht => ht⟩
      rcases (hevent.and htail).exists with ⟨t, ht, ht0⟩
      exact (not_lt_of_ge (le_of_lt (hexterior t ht0))) ht
    refine ⟨zLimit, hzlim, le_antisymm hball hlower, Or.inr hexterior⟩

end AttouchAdlyDryFrictionDynamics2023
