import Mathlib
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.def_2
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_1
import TheoremLib.Attouch_Adly_Dry_friction_dynamics_2023.items.ext_def_3

namespace AttouchAdlyDryFrictionDynamics2023

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

private theorem drygrad_energy_deriv_le {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {t₀ r : ℝ} (f : H → ℝ) (fgrad : H → H)
    (z dz : ℝ → H) (hr : 0 < r) (hsol : IsDrygradTrajectory r hr fgrad z dz t₀)
    (hchain : ∀ t ∈ Set.Ici t₀,
      HasDerivAt (fun s => f (z s)) (inner ℝ (fgrad (z t)) (dz t)) t)
    {t : ℝ} (ht : t ∈ Set.Ici t₀) :
    ‖dz t‖ ^ 2 + r * ‖dz t‖ + deriv (fun s => f (z s)) t ≤ 0 := by
  rcases hsol t ht with ⟨_, u, hu, hsum⟩
  have hwork : r * ‖dz t‖ ≤ inner ℝ u (dz t) :=
    drygrad_subgradient_work_le hu
  have hinner := congrArg (fun w => inner ℝ w (dz t)) hsum
  simp only [inner_add_left, real_inner_self_eq_norm_sq, inner_zero_left] at hinner
  have hderiv : deriv (fun s => f (z s)) t = inner ℝ (fgrad (z t)) (dz t) :=
    (hchain t ht).deriv
  rw [hderiv]
  nlinarith

private theorem drygrad_energy_antitone {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {t₀ r : ℝ} (f : H → ℝ) (fgrad : H → H)
    (z dz : ℝ → H) (hr : 0 < r) (hsol : IsDrygradTrajectory r hr fgrad z dz t₀)
    (hchain : ∀ t ∈ Set.Ici t₀,
      HasDerivAt (fun s => f (z s)) (inner ℝ (fgrad (z t)) (dz t)) t)
    (hcont : ContinuousOn (fun t => f (z t)) (Set.Ici t₀)) :
    AntitoneOn (fun t => f (z t)) (Set.Ici t₀) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici t₀) hcont
  · intro t ht
    exact (hchain t (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    have henergy := drygrad_energy_deriv_le f fgrad z dz hr hsol hchain (interior_subset ht)
    have hsq : 0 ≤ ‖dz t‖ ^ 2 := sq_nonneg _
    have hnorm : 0 ≤ r * ‖dz t‖ := mul_nonneg (le_of_lt hr) (norm_nonneg _)
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
    [CompleteSpace H] {t₀ r : ℝ} (hr : 0 < r) (f : H → ℝ) (fgrad : H → H)
    (z dz : ℝ → H) (_hgradient : ∀ x v, fderiv ℝ f x v = inner ℝ (fgrad x) v)
    (hf_lower : ∃ m : ℝ, ∀ x : H, m ≤ f x) (hfgrad_lip : LocallyLipschitz fgrad)
    (hinitial : r < ‖fgrad (z t₀)‖)
    (hchain : ∀ t ∈ Set.Ici t₀,
      HasDerivAt (fun s => f (z s)) (inner ℝ (fgrad (z t)) (dz t)) t)
    (hcomp_cont : ContinuousOn (fun t => f (z t)) (Set.Ici t₀))
    (hsol : IsDrygradTrajectory r hr fgrad z dz t₀)
    (V : H → H) (hV_lip : LocallyLipschitz V)
    (hV_zero : ∀ x, V x = 0 ↔ ‖fgrad x‖ ≤ r)
    (hvelocity : ∀ t ∈ Set.Ici t₀, dz t = V (z t))
    (hvelocity_limit : Filter.Tendsto dz Filter.atTop (nhds 0))
    (hstationary : ∀ S ∈ Set.Ici t₀, V (z S) = 0 →
      ∀ t ∈ Set.Ici S, z t = z S) :
    AntitoneOn (fun t => f (z t)) (Set.Ici t₀) ∧
      MeasureTheory.IntegrableOn (fun t => ‖dz t‖ ^ 2) (Set.Ici t₀) ∧
      MeasureTheory.IntegrableOn (fun t => ‖dz t‖) (Set.Ici t₀) ∧
      ∃ zLimit, Filter.Tendsto z Filter.atTop (nhds zLimit) ∧ ‖fgrad zLimit‖ = r ∧
        ((∃ T ∈ Set.Ici t₀, ∀ t ∈ Set.Ici T, z t = zLimit) ∨
          ∀ t ∈ Set.Ici t₀, r < ‖fgrad (z t)‖) := by
  have hanti : AntitoneOn (fun t => f (z t)) (Set.Ici t₀) :=
    drygrad_energy_antitone f fgrad z dz hr hsol hchain hcomp_cont
  have hVcont : Continuous V := hV_lip.continuous
  have hzcont : ContinuousOn z (Set.Ici t₀) := by
    intro t ht
    exact (hsol t ht).1.continuousAt.continuousWithinAt
  have hdzcont : ContinuousOn dz (Set.Ici t₀) := by
    have hVz : ContinuousOn (fun t => V (z t)) (Set.Ici t₀) :=
      hVcont.comp_continuousOn hzcont
    exact hVz.congr (by
      intro t ht
      exact hvelocity t ht)
  have hnormcont : ContinuousOn (fun t => ‖dz t‖) (Set.Ici t₀) := hdzcont.norm
  have hsqcont : ContinuousOn (fun t => ‖dz t‖ ^ 2) (Set.Ici t₀) :=
    hnormcont.pow 2
  obtain ⟨m, hm⟩ := hf_lower
  have hprefix : ∀ T : ℝ, t₀ ≤ T →
      ∫ t in t₀..T, (‖dz t‖ ^ 2 + r * ‖dz t‖) ≤ f (z t₀) - m := by
    intro T hT
    have hfgcont : ContinuousOn (fun t => fgrad (z t)) (Set.Icc t₀ T) :=
      hfgrad_lip.continuous.comp_continuousOn (hzcont.mono Set.Icc_subset_Ici_self)
    have hdzIcc : ContinuousOn dz (Set.Icc t₀ T) := hdzcont.mono Set.Icc_subset_Ici_self
    have hintercont : ContinuousOn (fun t => inner ℝ (fgrad (z t)) (dz t))
        (Set.Icc t₀ T) := hfgcont.inner hdzIcc
    have hderivcont : ContinuousOn (deriv (fun s => f (z s))) (Set.Icc t₀ T) :=
      hintercont.congr (by
        intro t ht
        exact (hchain t (Set.Icc_subset_Ici_self ht)).deriv)
    have hleftint : IntervalIntegrable (fun t => ‖dz t‖ ^ 2 + r * ‖dz t‖)
        MeasureTheory.volume t₀ T := by
      apply ContinuousOn.intervalIntegrable_of_Icc hT
      exact hsqcont.mono Set.Icc_subset_Ici_self |>.add
        ((continuousOn_const.mul (hnormcont.mono Set.Icc_subset_Ici_self)))
    have hrightint : IntervalIntegrable (fun t => - deriv (fun s => f (z s)) t)
        MeasureTheory.volume t₀ T :=
      (hderivcont.neg).intervalIntegrable_of_Icc hT
    have hpoint : ∀ t ∈ Set.Icc t₀ T,
        ‖dz t‖ ^ 2 + r * ‖dz t‖ ≤ - deriv (fun s => f (z s)) t := by
      intro t ht
      have h := drygrad_energy_deriv_le f fgrad z dz hr hsol hchain
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
      ∫ t in t₀..T, (‖dz t‖ ^ 2 + r * ‖dz t‖) ≤
          -(f (z T) - f (z t₀)) := hint
      _ = f (z t₀) - f (z T) := by ring
      _ ≤ f (z t₀) - m := hbound
  have hsqprefix : ∀ T : ℝ, t₀ ≤ T → ∫ t in t₀..T, ‖dz t‖ ^ 2 ≤ f (z t₀) - m := by
    intro T hT
    have hnonneg : 0 ≤ ∫ t in t₀..T, r * ‖dz t‖ :=
      intervalIntegral.integral_nonneg hT (fun t _ => mul_nonneg hr.le (norm_nonneg _))
    have hadd := hprefix T hT
    have hadd' : (∫ t in t₀..T, ‖dz t‖ ^ 2) +
        (∫ t in t₀..T, r * ‖dz t‖) ≤ f (z t₀) - m := by
      calc
        (∫ t in t₀..T, ‖dz t‖ ^ 2) + (∫ t in t₀..T, r * ‖dz t‖) =
            ∫ t in t₀..T, (‖dz t‖ ^ 2 + r * ‖dz t‖) :=
          (intervalIntegral.integral_add
            ((hsqcont.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hT)
            ((continuousOn_const.mul (hnormcont.mono Set.Icc_subset_Ici_self)).intervalIntegrable_of_Icc hT)).symm
        _ ≤ f (z t₀) - m := hadd
    linarith
  have hnormprefix : ∀ T : ℝ, t₀ ≤ T → ∫ t in t₀..T, ‖dz t‖ ≤ (f (z t₀) - m) / r := by
    intro T hT
    have hnonneg : 0 ≤ ∫ t in t₀..T, ‖dz t‖ ^ 2 :=
      intervalIntegral.integral_nonneg hT (fun t _ => sq_nonneg _)
    have hadd := hprefix T hT
    have hadd' : (∫ t in t₀..T, ‖dz t‖ ^ 2) +
        r * (∫ t in t₀..T, ‖dz t‖) ≤ f (z t₀) - m := by
      rw [← intervalIntegral.integral_const_mul]
      calc
        (∫ t in t₀..T, ‖dz t‖ ^ 2) + (∫ t in t₀..T, r * ‖dz t‖) =
            ∫ t in t₀..T, (‖dz t‖ ^ 2 + r * ‖dz t‖) :=
          (intervalIntegral.integral_add
            ((hsqcont.mono Set.Icc_subset_Ici_self).intervalIntegrable_of_Icc hT)
            ((continuousOn_const.mul (hnormcont.mono Set.Icc_subset_Ici_self)).intervalIntegrable_of_Icc hT)).symm
        _ ≤ f (z t₀) - m := hadd
    exact (le_div_iff₀ hr).mpr (by linarith)
  have hsqint : MeasureTheory.IntegrableOn (fun t => ‖dz t‖ ^ 2) (Set.Ici t₀) :=
    integrableOn_Ici_of_nonneg_prefix_bound hsqcont (fun _ _ => sq_nonneg _) hsqprefix
  have hnormint : MeasureTheory.IntegrableOn (fun t => ‖dz t‖) (Set.Ici t₀) :=
    integrableOn_Ici_of_nonneg_prefix_bound hnormcont (fun _ _ => norm_nonneg _) hnormprefix
  refine ⟨hanti, hsqint, hnormint, ?_⟩
  let zLimit := Filter.atTop.limUnder z
  have hnormint' : MeasureTheory.IntegrableOn (fun t => ‖dz t‖) (Set.Ioi t₀) := by
    rw [← integrableOn_Ici_iff_integrableOn_Ioi]
    exact hnormint
  have hdzint' : MeasureTheory.IntegrableOn dz (Set.Ioi t₀) := by
    rw [MeasureTheory.IntegrableOn]
    apply (MeasureTheory.integrable_norm_iff
      ((hdzcont.mono Set.Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi)).mp
    exact hnormint'.integrable
  have hzlim : Filter.Tendsto z Filter.atTop (nhds zLimit) :=
    MeasureTheory.tendsto_limUnder_of_hasDerivAt_of_integrableOn_Ioi
      (f := z) (f' := dz) (a := t₀)
      (fun t ht => (hsol t (show t ∈ Set.Ici t₀ from
        le_of_lt (show t₀ < t from ht))).1) hdzint'
  have hVzlim : Filter.Tendsto (fun t => V (z t)) Filter.atTop (nhds (V zLimit)) :=
    (hVcont.tendsto zLimit).comp hzlim
  have hdzV : Filter.Tendsto (fun t => V (z t)) Filter.atTop (nhds 0) := by
    apply hvelocity_limit.congr'
    filter_upwards [Filter.eventually_atTop.2 ⟨t₀, fun t ht => ht⟩] with t ht
    exact hvelocity t ht
  have hVzero : V zLimit = 0 := tendsto_nhds_unique hVzlim hdzV
  have hball : ‖fgrad zLimit‖ ≤ r := (hV_zero zLimit).mp hVzero
  have hqcont : Continuous (fun x : H => ‖fgrad x‖) := hfgrad_lip.continuous.norm
  have hqlim : Filter.Tendsto (fun t => ‖fgrad (z t)‖) Filter.atTop
      (nhds ‖fgrad zLimit‖) := (hqcont.tendsto zLimit).comp hzlim
  by_cases hhit : ∃ T ∈ Set.Ici t₀, ‖fgrad (z T)‖ ≤ r
  · rcases hhit with ⟨T, hT, hTball⟩
    have hqIcc : ContinuousOn (fun t => ‖fgrad (z t)‖) (Set.Icc t₀ T) :=
      hqcont.comp_continuousOn (hzcont.mono Set.Icc_subset_Ici_self)
    have hrmem : r ∈ Set.Icc (‖fgrad (z T)‖) (‖fgrad (z t₀)‖) :=
      ⟨hTball, hinitial.le⟩
    rcases intermediate_value_Icc' hT hqIcc hrmem with ⟨S, hS, hqS⟩
    have hVSzero : V (z S) = 0 := (hV_zero (z S)).mpr (by simp [hqS])
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
  · have hexterior : ∀ t ∈ Set.Ici t₀, r < ‖fgrad (z t)‖ := by
      intro t ht
      exact lt_of_not_ge (fun h => hhit ⟨t, ht, h⟩)
    have hlower : r ≤ ‖fgrad zLimit‖ := by
      by_contra hnot
      have hless : ‖fgrad zLimit‖ < r := lt_of_not_ge hnot
      have hevent : ∀ᶠ t in Filter.atTop, ‖fgrad (z t)‖ < r :=
        (tendsto_order.1 hqlim).2 r hless
      have htail : ∀ᶠ t in Filter.atTop, t ∈ Set.Ici t₀ :=
        Filter.eventually_atTop.2 ⟨t₀, fun t ht => ht⟩
      rcases (hevent.and htail).exists with ⟨t, ht, ht0⟩
      exact (not_lt_of_ge (le_of_lt (hexterior t ht0))) ht
    refine ⟨zLimit, hzlim, le_antisymm hball hlower, Or.inr hexterior⟩

end AttouchAdlyDryFrictionDynamics2023
