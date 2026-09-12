import Mathlib
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_1
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_3
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.def_4
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_thm_2
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_2
import TheoremLib.Attouch_AitMansour_Mazgouri_Monotone_stability_2024.items.ext_def_4

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open Set
open MeasureTheory Filter Function IsUnifLocDoublingMeasure
open scoped Topology

/- Mathlib's interval differentiation wrapper is scalar-valued.  This local
   Banach-valued version is the corresponding Vitali differentiation argument. -/
theorem locallyIntegrable_ae_hasDerivAt_integral_vector
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {g : ℝ → H} (hg : LocallyIntegrable g volume) :
    ∀ᵐ x, ∀ c, HasDerivAt (fun z ↦ ∫ t in c..z, g t) (g x) x := by
  have hg_interval (x y : ℝ) : IntervalIntegrable g volume x y :=
    intervalIntegrable_iff.mpr <|
      (hg.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc
  have hLDT := (vitaliFamily volume 1).ae_tendsto_average hg
  have hIcc {x y : ℝ} : ∫ t in Set.Ioc x y, g t = ∫ t in Set.Icc x y, g t :=
    (integral_Icc_eq_integral_Ioc (x := x) (y := y) (X := ℝ)).symm
  filter_upwards [hLDT] with x hx
  intro c
  rw [hasDerivAt_iff_tendsto_slope_left_right]
  constructor
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_left)
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : y ≤ x := by grind
    simp [slope, average, intervalIntegral.integral_interval_sub_left, hg_interval,
      intervalIntegral.integral_of_ge, hy', hIcc]
    rw [← neg_smul, ← inv_neg]
    congr 1
    ring
  · refine Filter.tendsto_congr' ?_ |>.mpr (hx.comp x.tendsto_Icc_vitaliFamily_right)
    filter_upwards [self_mem_nhdsWithin] with y hy
    have hy' : x ≤ y := by grind
    simp [slope, average, intervalIntegral.integral_interval_sub_left, hg_interval,
      intervalIntegral.integral_of_le, hy', hIcc]

theorem intervalIntegrable_ae_hasDerivAt_integral_vector
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {g : ℝ → H} {a b : ℝ} (hg : IntervalIntegrable g volume a b) :
    ∀ᵐ x, x ∈ Set.uIcc a b → ∀ c ∈ Set.uIcc a b,
      HasDerivAt (fun x ↦ ∫ t in c..x, g t) (g x) x := by
  wlog hab : a ≤ b
  · exact Set.uIcc_comm b a ▸ @this H _ _ _ g b a hg.symm (by linarith)
  rw [Set.uIcc_of_le hab]
  have hleft : ∀ᵐ x, x ≠ a := by simp [ae_iff, measure_singleton]
  have hright : ∀ᵐ x, x ≠ b := by simp [ae_iff, measure_singleton]
  let g' : ℝ → H := fun x ↦ if x ∈ Set.Ioc a b then g x else 0
  have hg' : LocallyIntegrable g' volume :=
    integrableOn_congr_fun (by grind [EqOn]) (by simp) |>.mpr hg.1
      |>.integrable_of_forall_notMem_eq_zero (by grind) |>.locallyIntegrable
  filter_upwards [locallyIntegrable_ae_hasDerivAt_integral_vector hg', hleft, hright]
    with x hx _ _ _
  intro c hc
  refine HasDerivWithinAt.hasDerivAt (s := Set.Ioo a b) ?_
    (Ioo_mem_nhds (by grind) (by grind))
  rw [show g x = g' x by grind]
  refine (hx c).hasDerivWithinAt.congr (fun y hy ↦ ?_) ?_
  · exact intervalIntegral.integral_congr_ae' (μ := volume) (a := c) (b := y) (f := g) (g := g')
      (Filter.Eventually.of_forall fun z hz ↦ by
        simp only [g']
        rw [if_pos]
        constructor <;> grind)
      (Filter.Eventually.of_forall fun z hz ↦ by
        simp only [g']
        rw [if_pos]
        constructor <;> grind)
  · exact intervalIntegral.integral_congr_ae' (μ := volume) (a := c) (b := x) (f := g) (g := g')
      (Filter.Eventually.of_forall fun z hz ↦ by
        simp only [g']
        rw [if_pos]
        constructor <;> grind)
      (Filter.Eventually.of_forall fun z hz ↦ by
        simp only [g']
        rw [if_pos]
        constructor <;> grind)

/- A Bochner interval integral of an interval-integrable Banach-valued
   function is absolutely continuous. -/
theorem intervalIntegrable_absolutelyContinuousOnInterval_vector
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {g : ℝ → H} {a b c : ℝ} (hg : IntervalIntegrable g volume a b)
    (hc : c ∈ Set.uIcc a b) :
    AbsolutelyContinuousOnInterval (fun x ↦ ∫ t in c..x, g t) a b := by
  let s := fun E : ℕ × (ℕ → ℝ × ℝ) ↦
    ⋃ i ∈ Finset.range E.1, Set.uIoc (E.2 i).1 (E.2 i).2
  have hzero : Tendsto (fun i ↦ ∫⁻ (x : ℝ) in s i, ‖g x‖ₑ ∂volume.restrict (Set.uIoc a b))
      (AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b)) (𝓝 0) :=
    tendsto_setLIntegral_zero
      (ne_of_lt <| intervalIntegrable_iff.mp hg |>.hasFiniteIntegral)
      (AbsolutelyContinuousOnInterval.tendsto_volume_restrict_totalLengthFilter_disjWithin_nhds_zero _ _)
  have hzero' := ENNReal.toReal_zero ▸
    (ENNReal.continuousAt_toReal (by simp)).tendsto.comp hzero
  refine squeeze_zero' ?_ ?_ hzero'
  · filter_upwards with (n, I)
    exact Finset.sum_nonneg (fun _ _ ↦ dist_nonneg)
  simp only [Function.comp_apply, s]
  have hmem : ∀ᶠ (E : ℕ × (ℕ → ℝ × ℝ)) in
      AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
        𝓟 (AbsolutelyContinuousOnInterval.disjWithin a b),
      E ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    eventually_inf_principal.mpr (by simp)
  filter_upwards [hmem] with (n, I) hnI
  obtain ⟨hnI1, hnI2⟩ := mem_setOf_eq ▸ hnI
  simp only
  rw [← integral_norm_eq_lintegral_enorm (hg.aestronglyMeasurable_restrict_uIoc.restrict),
      integral_biUnion_finset _ (by simp +contextual [Set.uIoc]) hnI2]
  · refine Finset.sum_le_sum (fun i hi ↦ ?_)
    rw [dist_eq_norm,
        intervalIntegral.integral_interval_sub_left
          (by apply IntervalIntegrable.mono_set' hg; grind [Set.uIoc, Set.uIcc])
          (by apply IntervalIntegrable.mono_set' hg; grind [Set.uIoc, Set.uIcc]),
        Measure.restrict_restrict_of_subset
          (AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hnI
            (Finset.mem_range.mp hi)),
        intervalIntegral.integral_symm, norm_neg,
        intervalIntegral.norm_intervalIntegral_eq]
    exact norm_integral_le_integral_norm _
  · intro i hi
    unfold IntegrableOn
    have hsubset := AbsolutelyContinuousOnInterval.uIoc_subset_of_mem_disjWithin hnI
      (Finset.mem_range.mp hi)
    rw [Measure.restrict_restrict_of_subset hsubset]
    exact IntegrableOn.mono_set hg.def'.norm hsubset |>.integrable

theorem intervalIntegral_eq_sub_of_ac_ae_hasDerivAt_vector
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    {f g : ℝ → H} {a b : ℝ} (hAC : AbsolutelyContinuousOnInterval f a b)
    (hg : IntervalIntegrable g volume a b)
    (hderiv : ∀ᵐ t, t ∈ Set.uIcc a b → HasDerivAt f (g t) t) :
    ∫ t in a..b, g t = f b - f a := by
  let F : ℝ → H := fun z ↦ ∫ t in a..z, g t
  have hFAC : AbsolutelyContinuousOnInterval F a b :=
    intervalIntegrable_absolutelyContinuousOnInterval_vector hg (by simp)
  have hqAC : AbsolutelyContinuousOnInterval (fun z ↦ f z - F z) a b := hAC.sub hFAC
  have hFderiv := intervalIntegrable_ae_hasDerivAt_integral_vector hg
  have hqderiv : ∀ᵐ t, t ∈ Set.uIcc a b →
      HasDerivAt (fun z ↦ f z - F z) 0 t := by
    filter_upwards [hderiv, hFderiv] with t hft hFt
    intro ht
    simpa [F] using (hft ht).sub (hFt ht a (by simp))
  obtain ⟨C, hC⟩ := hqAC.const_of_ae_hasDerivAt_zero hqderiv
  have ha := hC a (by simp)
  have hb := hC b (by simp)
  simp [F] at ha hb
  apply eq_sub_iff_add_eq'.mpr
  calc
    f a + (∫ t in a..b, g t) = C + (∫ t in a..b, g t) := by rw [ha]
    _ = (∫ t in a..b, g t) + C := add_comm _ _
    _ = f b := (sub_eq_iff_eq_add'.mp hb).symm

/-- Every pointwise norm of a continuous path on `[0,T]` is bounded by its
supremum norm. -/
theorem norm_le_pathSupNorm_of_continuousOn
    {H : Type*} [NormedAddCommGroup H] {T : ℝ} {f : ℝ → H}
    (hf : ContinuousOn f (Set.Icc (0 : ℝ) T)) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ‖f t‖ ≤ pathSupNorm T f := by
  unfold pathSupNorm
  apply le_csSup
  · rcases isCompact_Icc.bddAbove_image hf.norm with ⟨C, hC⟩
    refine ⟨C, ?_⟩
    rintro q ⟨s, hs, rfl⟩
    exact hC ⟨s, hs, rfl⟩
  · exact ⟨t, ht, rfl⟩

/-- The supremum norm of a continuous path on a nonempty interval is
nonnegative. -/
theorem pathSupNorm_nonneg_of_continuousOn
    {H : Type*} [NormedAddCommGroup H] {T : ℝ} {f : ℝ → H}
    (hT : 0 ≤ T) (hf : ContinuousOn f (Set.Icc (0 : ℝ) T)) :
    0 ≤ pathSupNorm T f :=
  (norm_nonneg (f 0)).trans
    (norm_le_pathSupNorm_of_continuousOn hf ⟨le_rfl, hT⟩)

/-- A uniform pointwise estimate gives an estimate of `pathSupNorm`. -/
theorem pathSupNorm_le_of_forall
    {H : Type*} [NormedAddCommGroup H] {T C : ℝ} {f : ℝ → H}
    (hT : 0 ≤ T) (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ‖f t‖ ≤ C) :
    pathSupNorm T f ≤ C := by
  unfold pathSupNorm
  refine csSup_le ⟨‖f 0‖, 0, ⟨le_rfl, hT⟩, rfl⟩ ?_
  rintro q ⟨t, ht, rfl⟩
  exact h t ht

/-- A classical solution, recentered at its initial position, satisfies the
Volterra identity on which the short-time stability estimate is based.  The
recentring is essential: it makes the damping integration-by-parts boundary
term vanish. -/
theorem centered_solution_integral_identity
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedSpace ℝ H]
    (A : H → H) (x dx ddx : ℝ → H) (u₀ v₀ : H) (α γ t : ℝ)
    (hcoco : CocoerciveOn α Set.univ (fun z : Set.univ => A z))
    (hsol : ext_def_2 A γ u₀ v₀ x dx ddx) (ht : 0 ≤ t) :
    x t - u₀ = t • v₀ - γ • (∫ s in (0 : ℝ)..t, x s - u₀) +
      ∫ s in (0 : ℝ)..t, (s - t) • A (x s) := by
  rcases hsol with ⟨_, hstrong⟩
  rcases hstrong with ⟨hlac, hx0, hdx0, hxderiv, hdxderiv, hode⟩
  have hT : 0 < t + 1 := by linarith
  obtain ⟨hxAC', hdxAC'⟩ := hlac (t + 1) hT
  have hsub : Set.uIcc (0 : ℝ) t ⊆ Set.uIcc (0 : ℝ) (t + 1) := by
    rw [Set.uIcc_of_le ht, Set.uIcc_of_le hT.le]
    exact Set.Icc_subset_Icc_right (by linarith)
  have hxAC : AbsolutelyContinuousOnInterval x 0 t := hxAC'.mono hsub
  have hdxAC : AbsolutelyContinuousOnInterval dx 0 t := hdxAC'.mono hsub
  have hxcont : ContinuousOn x (Set.Icc 0 t) :=
    hxAC.continuousOn.mono Set.Icc_subset_uIcc
  have hdxcont : ContinuousOn dx (Set.Icc 0 t) :=
    hdxAC.continuousOn.mono Set.Icc_subset_uIcc
  have hAlip : LipschitzWith (Real.toNNReal (1 / α)) A :=
    cocoercive_implies_lipschitz A α hcoco
  have hAcont : ContinuousOn (fun s => A (x s)) (Set.Icc 0 t) :=
    hAlip.continuous.continuousOn.comp hxcont (mapsTo_univ _ _)
  have hdxII : IntervalIntegrable dx volume 0 t := hdxcont.intervalIntegrable_of_Icc ht
  have hforceII : IntervalIntegrable (fun s => -(γ • dx s + A (x s))) volume 0 t :=
    ((hdxcont.const_smul γ).add hAcont).neg.intervalIntegrable_of_Icc ht
  have hode_ae := (MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hode
  have hddxII : IntervalIntegrable ddx volume 0 t := by
    apply hforceII.congr_ae
    filter_upwards [MeasureTheory.ae_restrict_of_ae hode_ae,
      MeasureTheory.ae_restrict_mem measurableSet_uIoc] with s hsode hs
    apply Eq.symm
    apply eq_neg_iff_add_eq_zero.mpr
    calc
      ddx s + (γ • dx s + A (x s)) = ddx s + γ • dx s + A (x s) := by ac_rfl
      _ = 0 := hsode (by
        have hsu : s ∈ Set.uIcc (0 : ℝ) t := Set.uIoc_subset_uIcc hs
        rw [Set.uIcc_of_le ht] at hsu
        exact hsu.1)
  have hxcenterII : IntervalIntegrable (fun s => x s - u₀) volume 0 t :=
    (hxcont.sub continuousOn_const).intervalIntegrable_of_Icc ht
  have hAII : IntervalIntegrable (fun s => A (x s)) volume 0 t :=
    hAcont.intervalIntegrable_of_Icc ht
  have hkernelDxII : IntervalIntegrable (fun s => (s - t) • dx s) volume 0 t :=
    hdxII.continuousOn_smul (continuous_id.sub continuous_const).continuousOn
  have hgammaKernelDxII :
      IntervalIntegrable (fun s => γ • ((s - t) • dx s)) volume 0 t :=
    (continuousOn_const.smul
      ((continuous_id.sub continuous_const).continuousOn.smul hdxcont)).intervalIntegrable_of_Icc ht
  have hkernelAII : IntervalIntegrable (fun s => (s - t) • A (x s)) volume 0 t :=
    hAII.continuousOn_smul (continuous_id.sub continuous_const).continuousOn
  have hxFTC : (∫ s in (0 : ℝ)..t, dx s) = x t - u₀ := by
    have hxderiv' : ∀ᵐ s, s ∈ Set.uIcc (0 : ℝ) t → HasDerivAt x (dx s) s := by
      filter_upwards [(MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hxderiv]
        with s hsderiv
      intro hs
      apply hsderiv
      rw [Set.uIcc_of_le ht] at hs
      exact hs.1
    simpa [hx0] using
      intervalIntegral_eq_sub_of_ac_ae_hasDerivAt_vector hxAC hdxII hxderiv'
  have haccParts :
      (∫ s in (0 : ℝ)..t, (s - t) • ddx s) = t • v₀ - (x t - u₀) := by
    have hqAC : AbsolutelyContinuousOnInterval (fun s : ℝ => s - t) 0 t := by
      simpa only [id_eq] using
        (LipschitzWith.id.sub (LipschitzWith.const t)).lipschitzOnWith.absolutelyContinuousOnInterval
    have hpAC : AbsolutelyContinuousOnInterval (fun s => (s - t) • dx s) 0 t := by
      simpa only [Pi.smul_apply] using hqAC.smul hdxAC
    have hqddxII : IntervalIntegrable (fun s => (s - t) • ddx s) volume 0 t :=
      hddxII.continuousOn_smul (continuous_id.sub continuous_const).continuousOn
    have hpII : IntervalIntegrable (fun s => dx s + (s - t) • ddx s) volume 0 t :=
      hdxII.add hqddxII
    have hpderiv : ∀ᵐ s, s ∈ Set.uIcc (0 : ℝ) t →
        HasDerivAt (fun r => (r - t) • dx r) (dx s + (s - t) • ddx s) s := by
      filter_upwards [(MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hdxderiv]
        with s hsderiv
      intro hs
      have hs0 : 0 ≤ s := by
        rw [Set.uIcc_of_le ht] at hs
        exact hs.1
      simpa only [id_eq, one_smul, add_comm] using
        ((hasDerivAt_id s).sub_const t).smul (hsderiv hs0)
    have hparts := intervalIntegral_eq_sub_of_ac_ae_hasDerivAt_vector hpAC hpII hpderiv
    rw [intervalIntegral.integral_add hdxII hqddxII, hxFTC] at hparts
    simp only [sub_self, zero_smul, zero_sub, neg_smul, neg_neg] at hparts
    rw [hdx0] at hparts
    apply eq_sub_iff_add_eq.mpr
    rw [add_comm]
    exact hparts
  have hdampParts :
      (∫ s in (0 : ℝ)..t, (s - t) • dx s) =
        -(∫ s in (0 : ℝ)..t, x s - u₀) := by
    have hqAC : AbsolutelyContinuousOnInterval (fun s : ℝ => s - t) 0 t := by
      simpa only [id_eq] using
        (LipschitzWith.id.sub (LipschitzWith.const t)).lipschitzOnWith.absolutelyContinuousOnInterval
    have hpAC : AbsolutelyContinuousOnInterval (fun s => (s - t) • (x s - u₀)) 0 t := by
      have hconstAC : AbsolutelyContinuousOnInterval (fun _ : ℝ => u₀) 0 t :=
        (LipschitzWith.const u₀).lipschitzOnWith.absolutelyContinuousOnInterval
      simpa only [Pi.smul_apply] using hqAC.smul (hxAC.fun_sub hconstAC)
    have hkernelDxII : IntervalIntegrable (fun s => (s - t) • dx s) volume 0 t :=
      hdxII.continuousOn_smul (continuous_id.sub continuous_const).continuousOn
    have hpII : IntervalIntegrable
        (fun s => (x s - u₀) + (s - t) • dx s) volume 0 t :=
      hxcenterII.add hkernelDxII
    have hpderiv : ∀ᵐ s, s ∈ Set.uIcc (0 : ℝ) t →
        HasDerivAt (fun r => (r - t) • (x r - u₀))
          ((x s - u₀) + (s - t) • dx s) s := by
      filter_upwards [(MeasureTheory.ae_restrict_iff' measurableSet_Ici).mp hxderiv]
        with s hsderiv
      intro hs
      have hs0 : 0 ≤ s := by
        rw [Set.uIcc_of_le ht] at hs
        exact hs.1
      simpa only [id_eq, one_smul, add_comm] using
        ((hasDerivAt_id s).sub_const t).smul ((hsderiv hs0).sub_const u₀)
    have hparts := intervalIntegral_eq_sub_of_ac_ae_hasDerivAt_vector hpAC hpII hpderiv
    rw [intervalIntegral.integral_add hxcenterII hkernelDxII] at hparts
    rw [hx0] at hparts
    have hparts' : (∫ s in (0 : ℝ)..t, x s - u₀) +
        (∫ s in (0 : ℝ)..t, (s - t) • dx s) = 0 := by
      simpa only [sub_self, zero_smul, smul_zero, sub_zero] using hparts
    exact eq_neg_of_add_eq_zero_right hparts'
  have hforce :
      (∫ s in (0 : ℝ)..t, (s - t) • (γ • dx s + A (x s))) =
        -(∫ s in (0 : ℝ)..t, (s - t) • ddx s) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr_ae
    filter_upwards [hode_ae] with s hsode
    intro hs
    change (s - t) • (γ • dx s + A (x s)) = -((s - t) • ddx s)
    have hs : γ • dx s + A (x s) = -ddx s := by
      apply eq_neg_iff_add_eq_zero.mpr
      calc
        (γ • dx s + A (x s)) + ddx s = ddx s + γ • dx s + A (x s) := by
          ac_rfl
        _ = 0 := hsode (by
          have hsu : s ∈ Set.uIcc (0 : ℝ) t := Set.uIoc_subset_uIcc hs
          rw [Set.uIcc_of_le ht] at hsu
          exact hsu.1)
    rw [hs, smul_neg]
  have hsplit :
      (∫ s in (0 : ℝ)..t, (s - t) • (γ • dx s + A (x s))) =
        γ • (∫ s in (0 : ℝ)..t, (s - t) • dx s) +
          ∫ s in (0 : ℝ)..t, (s - t) • A (x s) := by
    calc
      (∫ s in (0 : ℝ)..t, (s - t) • (γ • dx s + A (x s))) =
          ∫ s in (0 : ℝ)..t,
            γ • ((s - t) • dx s) + (s - t) • A (x s) := by
              apply intervalIntegral.integral_congr
              intro s _
              module
      _ = (∫ s in (0 : ℝ)..t, γ • ((s - t) • dx s)) +
          ∫ s in (0 : ℝ)..t, (s - t) • A (x s) := by
            exact intervalIntegral.integral_add hgammaKernelDxII hkernelAII
      _ = γ • (∫ s in (0 : ℝ)..t, (s - t) • dx s) +
          ∫ s in (0 : ℝ)..t, (s - t) • A (x s) := by
            rw [intervalIntegral.integral_smul]
  have hforceValue :
      (∫ s in (0 : ℝ)..t, (s - t) • (γ • dx s + A (x s))) =
        x t - u₀ - t • v₀ := by
    rw [hforce, haccParts]
    module
  calc
    x t - u₀ = t • v₀ + (x t - u₀ - t • v₀) := by module
    _ = t • v₀ +
        ∫ s in (0 : ℝ)..t, (s - t) • (γ • dx s + A (x s)) := by
          rw [hforceValue]
    _ = t • v₀ - γ • (∫ s in (0 : ℝ)..t, x s - u₀) +
        ∫ s in (0 : ℝ)..t, (s - t) • A (x s) := by
          rw [hsplit, hdampParts]
          module

/-- Theorem 7.1: Assume for some α>0 that A_μ is α-cocoercive for each
  μ∈V(μ̄) and (C₂). Let x_μ be the unique strong global solution of
  S(A_μ,u₀^μ,v₀^μ). Given T>0 with γT+T²/α∈[0,1), the ‖·‖_∞ estimate
  (25) holds.

  Deviations: the operator discrepancy is abstracted as an arbitrary bound `D`
  (it is used at a single place in the paper's argument), and `thm_8` below
  recovers the paper's instance `D = θ₁‖μ-μ'‖^{θ₂}` from (C₂); the estimate is
  proved directly from the centered integral identity (26) rather than by
  identifying the solution as the unique fixed point of Γ as the paper does
  (that fixed-point statement is available separately, see `thm_10`); and the
  existence/uniqueness of the solutions is supplied by `hsol`. -/
theorem thm_8_general {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedSpace ℝ H] [NormedAddCommGroup M] (V : Set M) (A : M → H → H)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (α γ T : ℝ)
    (hα : 0 < α) (hT : 0 < T)
    (hcoco : ∀ μ ∈ V, CocoerciveOn α Set.univ (fun x : Set.univ => A μ x))
    (hsol : ∀ μ ∈ V,
      ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (hγT : γ * T + T ^ 2 / α < 1) (μ : M) (hμ : μ ∈ V) (μ' : M) (hμ' : μ' ∈ V)
    (D : ℝ) (hDbound : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ v : H,
      ‖v - x μ' s‖ ≤ ‖u₀ μ - u₀ μ'‖ → ‖A μ v - A μ' v‖ ≤ D) :
    pathSupNorm T (fun t => x μ t - x μ' t) ≤ α / (α - α * γ * T - T ^ 2) *
        (‖u₀ μ - u₀ μ'‖ + T * ‖v₀ μ - v₀ μ'‖ + T ^ 2 * D) := by
  have hextμ := hsol μ hμ
  have hextμ' := hsol μ' hμ'
  have hcenterμ (t : ℝ) (ht : 0 ≤ t) :=
    centered_solution_integral_identity (A μ) (x μ) (dx μ) (ddx μ)
      (u₀ μ) (v₀ μ) α γ t (hcoco μ hμ) hextμ ht
  have hcenterμ' (t : ℝ) (ht : 0 ≤ t) :=
    centered_solution_integral_identity (A μ') (x μ') (dx μ') (ddx μ')
      (u₀ μ') (v₀ μ') α γ t (hcoco μ' hμ') hextμ' ht
  rcases hextμ with ⟨hγ, hstrongμ⟩
  rcases hextμ' with ⟨_, hstrongμ'⟩
  rcases hstrongμ with ⟨hlacμ, hx0μ, _, _, _, _⟩
  rcases hstrongμ' with ⟨hlacμ', hx0μ', _, _, _, _⟩
  have hDnn : 0 ≤ D := by
    have h := hDbound 0 ⟨le_refl 0, hT.le⟩ (x μ' 0)
      (by rw [sub_self, norm_zero]; exact norm_nonneg _)
    have h0 := norm_nonneg (A μ (x μ' 0) - A μ' (x μ' 0))
    linarith
  let p : ℝ → H := fun s => x μ s - u₀ μ
  let p' : ℝ → H := fun s => x μ' s - u₀ μ'
  let w : ℝ → H := fun s => p s - p' s
  let z : ℝ → H := fun s => x μ s - x μ' s
  let W : ℝ := pathSupNorm T w
  have hxcontμ : ContinuousOn (x μ) (Set.Icc (0 : ℝ) T) :=
    (hlacμ T hT).1.continuousOn.mono Set.Icc_subset_uIcc
  have hxcontμ' : ContinuousOn (x μ') (Set.Icc (0 : ℝ) T) :=
    (hlacμ' T hT).1.continuousOn.mono Set.Icc_subset_uIcc
  have hpcont : ContinuousOn p (Set.Icc (0 : ℝ) T) := hxcontμ.sub continuousOn_const
  have hpcont' : ContinuousOn p' (Set.Icc (0 : ℝ) T) := hxcontμ'.sub continuousOn_const
  have hwcont : ContinuousOn w (Set.Icc (0 : ℝ) T) := hpcont.sub hpcont'
  have hzcont : ContinuousOn z (Set.Icc (0 : ℝ) T) := hxcontμ.sub hxcontμ'
  have hWnonneg : 0 ≤ W :=
    pathSupNorm_nonneg_of_continuousOn hT.le hwcont
  have hw_le (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) : ‖w s‖ ≤ W :=
    norm_le_pathSupNorm_of_continuousOn hwcont hs
  have hLμ (a b : H) : ‖A μ a - A μ b‖ ≤ α⁻¹ * ‖a - b‖ := by
    have h := (cocoercive_implies_lipschitz (A μ) α (hcoco μ hμ)).dist_le_mul a b
    simpa [dist_eq_norm, Real.coe_toNNReal', max_eq_left (inv_nonneg.mpr hα.le)] using h
  have hLμ' (a b : H) : ‖A μ' a - A μ' b‖ ≤ α⁻¹ * ‖a - b‖ := by
    have h := (cocoercive_implies_lipschitz (A μ') α (hcoco μ' hμ')).dist_le_mul a b
    simpa [dist_eq_norm, Real.coe_toNNReal', max_eq_left (inv_nonneg.mpr hα.le)] using h
  have hAcontμ : ContinuousOn (fun s => A μ (x μ s)) (Set.Icc (0 : ℝ) T) :=
    (cocoercive_implies_lipschitz (A μ) α (hcoco μ hμ)).continuous.continuousOn.comp
      hxcontμ (mapsTo_univ _ _)
  have hAcontμ' : ContinuousOn (fun s => A μ' (x μ' s)) (Set.Icc (0 : ℝ) T) :=
    (cocoercive_implies_lipschitz (A μ') α (hcoco μ' hμ')).continuous.continuousOn.comp
      hxcontμ' (mapsTo_univ _ _)
  have hwIdentity (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      w t = t • (v₀ μ - v₀ μ') - γ • (∫ s in (0 : ℝ)..t, w s) +
        ∫ s in (0 : ℝ)..t, (s - t) • (A μ (x μ s) - A μ' (x μ' s)) := by
    have hsub : Set.Icc (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := Set.Icc_subset_Icc_right ht.2
    have hpII : IntervalIntegrable p volume 0 t :=
      (hpcont.mono hsub).intervalIntegrable_of_Icc ht.1
    have hpII' : IntervalIntegrable p' volume 0 t :=
      (hpcont'.mono hsub).intervalIntegrable_of_Icc ht.1
    have hAII : IntervalIntegrable (fun s => A μ (x μ s)) volume 0 t :=
      (hAcontμ.mono hsub).intervalIntegrable_of_Icc ht.1
    have hAII' : IntervalIntegrable (fun s => A μ' (x μ' s)) volume 0 t :=
      (hAcontμ'.mono hsub).intervalIntegrable_of_Icc ht.1
    have hkernelAII : IntervalIntegrable
        (fun s => (s - t) • A μ (x μ s)) volume 0 t :=
      hAII.continuousOn_smul (continuous_id.sub continuous_const).continuousOn
    have hkernelAII' : IntervalIntegrable
        (fun s => (s - t) • A μ' (x μ' s)) volume 0 t :=
      hAII'.continuousOn_smul (continuous_id.sub continuous_const).continuousOn
    have hpEq : p t = t • v₀ μ - γ • (∫ s in (0 : ℝ)..t, p s) +
        ∫ s in (0 : ℝ)..t, (s - t) • A μ (x μ s) := by
      simpa [p] using hcenterμ t ht.1
    have hpEq' : p' t = t • v₀ μ' - γ • (∫ s in (0 : ℝ)..t, p' s) +
        ∫ s in (0 : ℝ)..t, (s - t) • A μ' (x μ' s) := by
      simpa [p'] using hcenterμ' t ht.1
    have hpSub : (∫ s in (0 : ℝ)..t, w s) =
        (∫ s in (0 : ℝ)..t, p s) - ∫ s in (0 : ℝ)..t, p' s := by
      simpa [w] using intervalIntegral.integral_sub hpII hpII'
    have hASub :
        (∫ s in (0 : ℝ)..t, (s - t) • (A μ (x μ s) - A μ' (x μ' s))) =
          (∫ s in (0 : ℝ)..t, (s - t) • A μ (x μ s)) -
            ∫ s in (0 : ℝ)..t, (s - t) • A μ' (x μ' s) := by
      rw [← intervalIntegral.integral_sub hkernelAII hkernelAII']
      apply intervalIntegral.integral_congr
      intro s _
      module
    rw [show w t = p t - p' t by rfl, hpEq, hpEq', hpSub, hASub]
    module
  have hopBound (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T) :
      ‖A μ (x μ s) - A μ' (x μ' s)‖ ≤
        α⁻¹ * W + α⁻¹ * ‖u₀ μ - u₀ μ'‖ + D := by
    let q : H := u₀ μ + p' s
    have hfirst : ‖A μ (x μ s) - A μ q‖ ≤ α⁻¹ * W := by
      calc
        ‖A μ (x μ s) - A μ q‖ ≤ α⁻¹ * ‖x μ s - q‖ := hLμ _ _
        _ = α⁻¹ * ‖w s‖ := by congr 2 <;> dsimp [q, w, p, p'] <;> module
        _ ≤ α⁻¹ * W := by
          exact mul_le_mul_of_nonneg_left (hw_le s hs) (inv_nonneg.mpr hα.le)
    have hmiddle : ‖A μ q - A μ' q‖ ≤ D := by
      have hq : ‖q - x μ' s‖ ≤ ‖u₀ μ - u₀ μ'‖ := by
        have hq' : q - x μ' s = u₀ μ - u₀ μ' := by
          dsimp [q, p']
          abel
        rw [hq']
      exact hDbound s hs q hq
    have hlast : ‖A μ' q - A μ' (x μ' s)‖ ≤
        α⁻¹ * ‖u₀ μ - u₀ μ'‖ := by
      calc
        ‖A μ' q - A μ' (x μ' s)‖ ≤ α⁻¹ * ‖q - x μ' s‖ := hLμ' _ _
        _ = α⁻¹ * ‖u₀ μ - u₀ μ'‖ := by
          congr 2
          dsimp [q, p']
          module
    calc
      ‖A μ (x μ s) - A μ' (x μ' s)‖ =
          ‖(A μ (x μ s) - A μ q) + (A μ q - A μ' q) +
            (A μ' q - A μ' (x μ' s))‖ := by
              congr 1
              abel
      _ ≤ (‖A μ (x μ s) - A μ q‖ + ‖A μ q - A μ' q‖) +
          ‖A μ' q - A μ' (x μ' s)‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
      _ ≤ (α⁻¹ * W + D) +
          α⁻¹ * ‖u₀ μ - u₀ μ'‖ := by gcongr
      _ = α⁻¹ * W + α⁻¹ * ‖u₀ μ - u₀ μ'‖ +
          D := by ring
  have hCnonneg :
      0 ≤ α⁻¹ * W + α⁻¹ * ‖u₀ μ - u₀ μ'‖ + D := by
    positivity
  have hwPoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      ‖w t‖ ≤ T * ‖v₀ μ - v₀ μ'‖ + γ * T * W +
        T ^ 2 * (α⁻¹ * W + α⁻¹ * ‖u₀ μ - u₀ μ'‖ +
          D) := by
    have hdamp : ‖γ • (∫ s in (0 : ℝ)..t, w s)‖ ≤ γ * T * W := by
      have hint : ‖∫ s in (0 : ℝ)..t, w s‖ ≤ W * t := by
        have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
          (C := W) (f := w) (a := (0 : ℝ)) (b := t) (fun s hs => by
            apply hw_le s
            have hsu := Set.uIoc_subset_uIcc hs
            rw [Set.uIcc_of_le ht.1] at hsu
            exact ⟨hsu.1, hsu.2.trans ht.2⟩)
        simpa [abs_of_nonneg ht.1] using hbound
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hγ]
      calc
        γ * ‖∫ s in (0 : ℝ)..t, w s‖ ≤ γ * (W * t) :=
          mul_le_mul_of_nonneg_left hint hγ.le
        _ ≤ γ * (W * T) := by
          apply mul_le_mul_of_nonneg_left _ hγ.le
          exact mul_le_mul_of_nonneg_left ht.2 hWnonneg
        _ = γ * T * W := by ring
    have hopInt :
        ‖∫ s in (0 : ℝ)..t, (s - t) • (A μ (x μ s) - A μ' (x μ' s))‖ ≤
          T ^ 2 * (α⁻¹ * W + α⁻¹ * ‖u₀ μ - u₀ μ'‖ +
            D) := by
      let C : ℝ := α⁻¹ * W + α⁻¹ * ‖u₀ μ - u₀ μ'‖ +
        D
      have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
        (C := T * C)
        (f := fun s => (s - t) • (A μ (x μ s) - A μ' (x μ' s)))
        (a := (0 : ℝ)) (b := t) (fun s hs => by
          have hsu := Set.uIoc_subset_uIcc hs
          rw [Set.uIcc_of_le ht.1] at hsu
          have hsT : s ∈ Set.Icc (0 : ℝ) T := ⟨hsu.1, hsu.2.trans ht.2⟩
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hsu.2)]
          exact mul_le_mul (by linarith [hsu.1, ht.2]) (hopBound s hsT)
            (norm_nonneg _) hT.le)
      have hbound' :
          ‖∫ s in (0 : ℝ)..t, (s - t) • (A μ (x μ s) - A μ' (x μ' s))‖ ≤
            (T * C) * t := by
        simpa [abs_of_nonneg ht.1] using hbound
      have hTCnonneg : 0 ≤ T * C := by
        apply mul_nonneg hT.le
        simpa [C] using hCnonneg
      calc
        ‖∫ s in (0 : ℝ)..t, (s - t) • (A μ (x μ s) - A μ' (x μ' s))‖ ≤
            (T * C) * t := hbound'
        _ ≤ (T * C) * T := mul_le_mul_of_nonneg_left ht.2 hTCnonneg
        _ = T ^ 2 * (α⁻¹ * W + α⁻¹ * ‖u₀ μ - u₀ μ'‖ +
            D) := by dsimp [C]; ring
    rw [hwIdentity t ht]
    calc
      ‖t • (v₀ μ - v₀ μ') - γ • (∫ s in (0 : ℝ)..t, w s) +
          ∫ s in (0 : ℝ)..t, (s - t) • (A μ (x μ s) - A μ' (x μ' s))‖ ≤
          (‖t • (v₀ μ - v₀ μ')‖ + ‖γ • (∫ s in (0 : ℝ)..t, w s)‖) +
            ‖∫ s in (0 : ℝ)..t,
              (s - t) • (A μ (x μ s) - A μ' (x μ' s))‖ :=
        (norm_add_le _ _).trans (by gcongr; exact norm_sub_le _ _)
      _ ≤ (T * ‖v₀ μ - v₀ μ'‖ + γ * T * W) +
          T ^ 2 * (α⁻¹ * W + α⁻¹ * ‖u₀ μ - u₀ μ'‖ +
            D) := by
        apply add_le_add
        · apply add_le_add
          · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
            exact mul_le_mul_of_nonneg_right ht.2 (norm_nonneg _)
          · exact hdamp
        · exact hopInt
      _ = T * ‖v₀ μ - v₀ μ'‖ + γ * T * W +
          T ^ 2 * (α⁻¹ * W + α⁻¹ * ‖u₀ μ - u₀ μ'‖ +
            D) := by ring
  have hWbound : W ≤ T * ‖v₀ μ - v₀ μ'‖ + γ * T * W +
      T ^ 2 * (α⁻¹ * W + α⁻¹ * ‖u₀ μ - u₀ μ'‖ +
        D) :=
    pathSupNorm_le_of_forall hT.le hwPoint
  have hdenom : 0 < α - α * γ * T - T ^ 2 := by
    have hcore : α * γ * T + T ^ 2 < α := by
      calc
        α * γ * T + T ^ 2 = α * (γ * T + T ^ 2 / α) := by
          field_simp [hα.ne']
        _ < α * 1 := mul_lt_mul_of_pos_left hγT hα
        _ = α := by ring
    nlinarith
  have hscaledW :
      (α - α * γ * T - T ^ 2) * W ≤
        α * T * ‖v₀ μ - v₀ μ'‖ + T ^ 2 * ‖u₀ μ - u₀ μ'‖ +
          α * T ^ 2 * D := by
    have hclean : α * W ≤
        α * T * ‖v₀ μ - v₀ μ'‖ + α * γ * T * W + T ^ 2 * W +
          T ^ 2 * ‖u₀ μ - u₀ μ'‖ + α * T ^ 2 * D := by
      calc
        α * W ≤ α * (T * ‖v₀ μ - v₀ μ'‖ + γ * T * W +
            T ^ 2 * (α⁻¹ * W + α⁻¹ * ‖u₀ μ - u₀ μ'‖ +
              D)) :=
          mul_le_mul_of_nonneg_left hWbound hα.le
        _ = α * T * ‖v₀ μ - v₀ μ'‖ + α * γ * T * W + T ^ 2 * W +
            T ^ 2 * ‖u₀ μ - u₀ μ'‖ +
              α * T ^ 2 * D := by
          field_simp [hα.ne']
          ring
    nlinarith
  have hzPoint (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
      ‖z t‖ ≤ ‖u₀ μ - u₀ μ'‖ + W := by
    have hzEq : z t = (u₀ μ - u₀ μ') + w t := by
      dsimp [z, w, p, p']
      module
    rw [hzEq]
    exact (norm_add_le _ _).trans (by gcongr; exact hw_le t ht)
  have hzSup : pathSupNorm T z ≤ ‖u₀ μ - u₀ μ'‖ + W :=
    pathSupNorm_le_of_forall hT.le hzPoint
  have hdu : 0 ≤ ‖u₀ μ - u₀ μ'‖ := norm_nonneg _
  have hdv : 0 ≤ ‖v₀ μ - v₀ μ'‖ := norm_nonneg _
  have hparamNonneg : 0 ≤ D := hDnn
  have htotalNonneg :
      0 ≤ ‖u₀ μ - u₀ μ'‖ + T * ‖v₀ μ - v₀ μ'‖ +
        T ^ 2 * D := by positivity
  change pathSupNorm T z ≤ _
  apply hzSup.trans
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hdenom).mpr
  have hγTdu : 0 ≤ α * γ * T * ‖u₀ μ - u₀ μ'‖ := by positivity
  calc
    (‖u₀ μ - u₀ μ'‖ + W) * (α - α * γ * T - T ^ 2) =
        (α - α * γ * T - T ^ 2) * ‖u₀ μ - u₀ μ'‖ +
          (α - α * γ * T - T ^ 2) * W := by ring
    _ ≤ (α - α * γ * T - T ^ 2) * ‖u₀ μ - u₀ μ'‖ +
        (α * T * ‖v₀ μ - v₀ μ'‖ + T ^ 2 * ‖u₀ μ - u₀ μ'‖ +
          α * T ^ 2 * D) := by gcongr
    _ ≤ α * (‖u₀ μ - u₀ μ'‖ + T * ‖v₀ μ - v₀ μ'‖ +
        T ^ 2 * D) := by nlinarith


/-- Theorem 7.1 in the form used elsewhere in the paper: the operator discrepancy
  is bounded by the Hölder condition (C₂). -/
theorem thm_8 {H M : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [NormedSpace ℝ H] [NormedAddCommGroup M] (V : Set M) (A : M → H → H)
    (x dx ddx : M → ℝ → H) (u₀ v₀ : M → H) (α γ T : ℝ)
    (hα : 0 < α) (hT : 0 < T)
    (hcoco : ∀ μ ∈ V, CocoerciveOn α Set.univ (fun x : Set.univ => A μ x))
    (hsol : ∀ μ ∈ V,
      ext_def_2 (A μ) γ (u₀ μ) (v₀ μ) (x μ) (dx μ) (ddx μ))
    (θ₁ θ₂ : ℝ) (hC₂ : 0 < θ₁ ∧ 0 < θ₂ ∧ θ₂ ≤ 1 ∧
      ∀ u μ μ', μ ∈ V → μ' ∈ V → ‖A μ u - A μ' u‖ ≤ θ₁ * ‖μ - μ'‖ ^ θ₂)
    (hγT : γ * T + T ^ 2 / α < 1) :
    ∀ μ ∈ V, ∀ μ' ∈ V,
      pathSupNorm T (fun t => x μ t - x μ' t) ≤ α / (α - α * γ * T - T ^ 2) *
        (‖u₀ μ - u₀ μ'‖ + T * ‖v₀ μ - v₀ μ'‖ + T ^ 2 * θ₁ * ‖μ - μ'‖ ^ θ₂) := by
  intro μ hμ μ' hμ'
  simpa only [mul_assoc] using
    thm_8_general V A x dx ddx u₀ v₀ α γ T hα hT hcoco hsol hγT μ hμ μ' hμ'
      (θ₁ * ‖μ - μ'‖ ^ θ₂)
      (by
        intro s hs v hv
        exact hC₂.2.2.2 v μ μ' hμ hμ')

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
