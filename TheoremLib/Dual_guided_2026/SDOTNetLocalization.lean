import TheoremLib.Dual_guided_2026.SDOTConcentration
import TheoremLib.Dual_guided_2026.SDOTPopulationObjective
import TheoremLib.Dual_guided_2026.SDOTFiniteGrid

/-!
# Finite-net localization of empirical semidual maximizers

Concavity supplies a sphere witness for every distant empirical maximum.
The deterministic Lipschitz estimate transfers this witness to a finite
net, and bounded-contrast Hoeffding concentration bounds the violation.
-/

namespace DualGuided2026

open MeasureTheory
open scoped BigOperators

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

theorem populationSemiDualContrast_sub_eq (data : HELLOSDOTData X Ω)
    (gRef g h : Fin data.n → ℝ) :
    populationSemiDualContrast data gRef g - populationSemiDualContrast data gRef h =
      populationSemiDualContrast data h g := by
  have hintegrand : semiDualContrastIntegrand data h g =
      semiDualContrastIntegrand data gRef g - semiDualContrastIntegrand data gRef h := by
    ext x
    simp only [semiDualContrastIntegrand, Pi.sub_apply]
    ring
  have hpotential : g - h = (g - gRef) - (h - gRef) := by
    ext j
    simp only [Pi.sub_apply]
    ring
  unfold populationSemiDualContrast
  rw [hintegrand]
  simp only [Pi.sub_apply]
  rw [integral_sub (integrable_semiDualContrastIntegrand data gRef g)
    (integrable_semiDualContrastIntegrand data gRef h), hpotential, map_sub]
  simp only [map_sub]
  ring

theorem populationSemiDualContrast_abs_le_norm (data : HELLOSDOTData X Ω)
    (g h : Fin data.n → ℝ) (hg : IsBGauge data g) (hh : IsBGauge data h) :
    |populationSemiDualContrast data h g| ≤ ‖g - h‖ := by
  have hgauge : potentialFunctional data data.b (g - h) = 0 := by
    rw [potentialFunctional_apply]
    simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    rw [hg, hh, sub_self]
  unfold populationSemiDualContrast
  rw [hgauge, zero_add]
  have hbound := norm_integral_le_of_norm_le_const (μ := data.sourceMeasure)
    (f := semiDualContrastIntegrand data h g) (C := ‖g - h‖)
    (Filter.Eventually.of_forall (fun x => by
      simpa only [Real.norm_eq_abs] using semiDualContrastIntegrand_abs_le_norm data h g x))
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using hbound

theorem populationSemiDualContrast_sub_abs_le_norm (data : HELLOSDOTData X Ω)
    (gRef g h : Fin data.n → ℝ) (hg : IsBGauge data g) (hh : IsBGauge data h) :
    |populationSemiDualContrast data gRef g - populationSemiDualContrast data gRef h| ≤
      ‖g - h‖ := by
  rw [populationSemiDualContrast_sub_eq]
  exact populationSemiDualContrast_abs_le_norm data g h hg hh

theorem empiricalSemiDualObjective_population_deviation_eq (data : HELLOSDOTData X Ω)
    {m : ℕ} (samples : Fin m → X) (gRef g : Fin data.n → ℝ) :
    empiricalSemiDualObjective data samples g - empiricalSemiDualObjective data samples gRef -
      populationSemiDualContrast data gRef g =
        iidAverage (semiDualContrastIntegrand data gRef g) m samples -
          ∫ x, semiDualContrastIntegrand data gRef g x ∂data.sourceMeasure := by
  rw [empiricalSemiDualObjective_sub_eq]
  unfold populationSemiDualContrast semiDualContrastIntegrand
  rw [potentialFunctional_apply]
  simp only [Pi.sub_apply]
  ring

/-- A local population margin on a sphere forces a positive centered
semidual fluctuation at some point of any sufficiently fine gauge net. -/
theorem empiricalMaximizer_finite_net_witness (data : HELLOSDOTData X Ω)
    {m : ℕ} (hm : 0 < m) (samples : Fin m → X) (g gStar : Fin data.n → ℝ)
    (hg : IsEmpiricalDualMaximizer data samples g) (hstar : IsBGauge data gStar)
    {r ε Δ : ℝ} (hr : 0 < r) (S : Finset (Fin data.n → ℝ))
    (hgauge : ∀ z ∈ S, IsBGauge data z)
    (hnet : ∀ z, IsBGauge data z → ‖z - gStar‖ = r →
      ∃ z' ∈ S, ‖z' - z‖ ≤ ε)
    (hmargin : ∀ z, IsBGauge data z → ‖z - gStar‖ = r →
      populationSemiDualContrast data gStar z ≤ -Δ)
    (hfar : r ≤ ‖g - gStar‖) :
    ∃ z ∈ S, Δ - 2 * ε ≤
      iidAverage (semiDualContrastIntegrand data gStar z) m samples -
        ∫ x, semiDualContrastIntegrand data gStar z x ∂data.sourceMeasure := by
  obtain ⟨z, hzgauge, hzradius, hzemp⟩ :=
    empiricalMaximizer_radial_witness data hm samples g gStar hg hstar hr hfar
  obtain ⟨z', hz'S, hz'close⟩ := hnet z hzgauge hzradius
  have hpop := hmargin z hzgauge hzradius
  have hpopclose := abs_le.mp
    (populationSemiDualContrast_sub_abs_le_norm data gStar z' z (hgauge z' hz'S) hzgauge)
  have hempclose := abs_le.mp
    (empiricalSemiDualObjective_sub_abs_le_norm data hm samples z' z (hgauge z' hz'S) hzgauge)
  refine ⟨z', hz'S, ?_⟩
  rw [← empiricalSemiDualObjective_population_deviation_eq]
  linarith

/-- Probability bound for arbitrary measurable exact empirical solvers,
including independent internal solver randomness. The net and population
margin are deterministic. -/
theorem measure_empiricalPotential_far_le_of_sphere_net (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    (hstar : IsBGauge data gStar) {r ε Δ C : ℝ} (hr : 0 < r) (hC : 0 < C)
    (hδ : 0 ≤ Δ - 2 * ε) (S : Finset (Fin data.n → ℝ))
    (hgauge : ∀ z ∈ S, IsBGauge data z) (hbounded : ∀ z ∈ S, ‖z - gStar‖ ≤ C)
    (hnet : ∀ z, IsBGauge data z → ‖z - gStar‖ = r →
      ∃ z' ∈ S, ‖z' - z‖ ≤ ε)
    (hmargin : ∀ z, IsBGauge data z → ‖z - gStar‖ = r →
      populationSemiDualContrast data gStar z ≤ -Δ)
    {m : ℕ} (hm : 0 < m) :
    (empiricalBatchMeasure data m).real
      {batch | r ≤ ‖empiricalBatchPotential data m batch - gStar‖} ≤
        (S.card : ℝ) * Real.exp (-(m : ℝ) * (Δ - 2 * ε) ^ 2 / (2 * C ^ 2)) := by
  let E : Set (Fin m → X) := {samples | ∃ z ∈ S, Δ - 2 * ε ≤
    iidAverage (semiDualContrastIntegrand data gStar z) m samples -
      ∫ x, semiDualContrastIntegrand data gStar z x ∂data.sourceMeasure}
  have hE : MeasurableSet E := by
    have heq : E = ⋃ z ∈ S, {samples : Fin m → X | Δ - 2 * ε ≤
        iidAverage (semiDualContrastIntegrand data gStar z) m samples -
          ∫ x, semiDualContrastIntegrand data gStar z x ∂data.sourceMeasure} := by
      ext samples
      simp only [E, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    rw [heq]
    apply MeasurableSet.biUnion (Finset.countable_toSet S)
    intro z _
    apply measurableSet_le measurable_const
    have hf := measurable_semiDualContrastIntegrand data gStar z
    unfold iidAverage
    fun_prop
  have hsub : ∀ᵐ batch ∂empiricalBatchMeasure data m,
      batch ∈ {batch | r ≤ ‖empiricalBatchPotential data m batch - gStar‖} →
        batch ∈ Prod.fst ⁻¹' E := by
    filter_upwards [hexact.2.2 hm] with batch hbatch hfar
    exact empiricalMaximizer_finite_net_witness data hm batch.1 _ gStar hbatch hstar
      hr S hgauge hnet hmargin hfar
  have hmeasure := measure_mono_ae hsub
  have hreal := ENNReal.toReal_mono (measure_ne_top (empiricalBatchMeasure data m) _) hmeasure
  have hfst : MeasurePreserving (Prod.fst : (Fin m → X) × Ω → (Fin m → X))
      (empiricalBatchMeasure data m) (sourceBatchMeasure data m) := measurePreserving_fst
  have hpull := congrArg ENNReal.toReal (hfst.measure_preimage hE.nullMeasurableSet)
  change (empiricalBatchMeasure data m).real
      {batch | r ≤ ‖empiricalBatchPotential data m batch - gStar‖} ≤
    (empiricalBatchMeasure data m).real (Prod.fst ⁻¹' E) at hreal
  change (empiricalBatchMeasure data m).real (Prod.fst ⁻¹' E) =
    (sourceBatchMeasure data m).real E at hpull
  rw [hpull] at hreal
  exact hreal.trans
    (measure_finite_semidualContrast_deviation_ge_le data S gStar hC hbounded hm hδ)

theorem centerPotential_eq_of_isBGauge (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (hg : IsBGauge data g) : centerPotential data g = g := by
  change (∑ j, data.b j * g j) = 0 at hg
  ext j
  simp only [centerPotential, hg, sub_zero]

theorem centerPotential_sub (data : HELLOSDOTData X Ω) (g h : Fin data.n → ℝ) :
    centerPotential data g - centerPotential data h = centerPotential data (g - h) := by
  ext j
  simp only [centerPotential, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

theorem weightedPotentialMean_abs_le_norm (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) : |∑ j, data.b j * g j| ≤ ‖g‖ := by
  calc
    _ ≤ ∑ j, |data.b j * g j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, data.b j * ‖g‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_pos (data.b_pos j)]
      exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm g j)
        (data.b_pos j).le
    _ = ‖g‖ := by rw [← Finset.sum_mul, data.b_sum, one_mul]

theorem centerPotential_norm_le (data : HELLOSDOTData X Ω) (g : Fin data.n → ℝ) :
    ‖centerPotential data g‖ ≤ 2 * ‖g‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  simp only [centerPotential, Real.norm_eq_abs]
  have hj : |g j| ≤ ‖g‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm g j
  exact (abs_sub _ _).trans (by linarith [weightedPotentialMean_abs_le_norm data g])

theorem centerPotential_sub_norm_le (data : HELLOSDOTData X Ω) (g h : Fin data.n → ℝ) :
    ‖centerPotential data g - centerPotential data h‖ ≤ 2 * ‖g - h‖ := by
  rw [centerPotential_sub]
  exact centerPotential_norm_le data (g - h)

noncomputable def gaugeCoordinateGrid (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (r δ : ℝ) : Finset (Fin data.n → ℝ) := by
  classical
  exact (coordinateGrid gStar r δ).image (centerPotential data)

theorem gaugeCoordinateGrid_card_real_le (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) :
    ((gaugeCoordinateGrid data gStar r δ).card : ℝ) ≤ (2 * r / δ + 2) ^ data.n := by
  classical
  have hcard : ((gaugeCoordinateGrid data gStar r δ).card : ℝ) ≤
      (coordinateGrid gStar r δ).card := by
    exact_mod_cast (Finset.card_image_le (f := centerPotential data)
      (s := coordinateGrid gStar r δ))
  exact hcard.trans (coordinateGrid_card_real_le gStar hr hδ)

theorem gaugeCoordinateGrid_isBGauge (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (r δ : ℝ) {g : Fin data.n → ℝ}
    (hg : g ∈ gaugeCoordinateGrid data gStar r δ) : IsBGauge data g := by
  classical
  obtain ⟨g, _, rfl⟩ := Finset.mem_image.mp hg
  exact centerPotential_isBGauge data g

theorem gaugeCoordinateGrid_norm_le (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (hstar : IsBGauge data gStar)
    {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) {g : Fin data.n → ℝ}
    (hg : g ∈ gaugeCoordinateGrid data gStar r δ) : ‖g - gStar‖ ≤ 2 * (r + δ) := by
  classical
  change g ∈ (coordinateGrid gStar r δ).image (centerPotential data) at hg
  obtain ⟨g, hgrid, rfl⟩ := Finset.mem_image.mp hg
  rw [← centerPotential_eq_of_isBGauge data gStar hstar]
  exact (centerPotential_sub_norm_le data g gStar).trans
    (mul_le_mul_of_nonneg_left (coordinateGrid_norm_le gStar hr hδ hgrid) (by norm_num))

theorem gaugeCoordinateGrid_covers (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) {r δ : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ)
    (g : Fin data.n → ℝ) (hgauge : IsBGauge data g) (hg : ‖g - gStar‖ ≤ r) :
    ∃ g' ∈ gaugeCoordinateGrid data gStar r δ, ‖g' - g‖ ≤ 2 * δ := by
  classical
  obtain ⟨g', hg', hclose⟩ := coordinateGrid_covers gStar hr hδ g hg
  have hnorm : ‖g' - g‖ ≤ δ := by
    apply (pi_norm_le_iff_of_nonneg hδ.le).mpr
    intro j
    simp only [Pi.sub_apply, Real.norm_eq_abs]
    simpa only [abs_sub_comm] using hclose j
  refine ⟨centerPotential data g', Finset.mem_image.mpr ⟨g', hg', rfl⟩, ?_⟩
  rw [← centerPotential_eq_of_isBGauge data g hgauge]
  exact (centerPotential_sub_norm_le data g' g).trans
    (mul_le_mul_of_nonneg_left hnorm (by norm_num))

/-- A quantitative version of the fixed-radius localization estimate from
Lemma F.10. It also permits radii and grid steps varying with the sample size. -/
theorem measure_empiricalPotential_far_le_of_local_norm_margin
    (data : HELLOSDOTData X Ω) (hexact : HasExactEmpiricalOTSolves data)
    (gStar : Fin data.n → ℝ) (hstar : IsBGauge data gStar)
    {ρ κ r δ : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hδ : 0 < δ)
    (hgap : 0 ≤ κ * r ^ 2 - 4 * δ)
    (hmargin : ∀ u, IsBGaugeDirection data u → ‖u‖ ≤ ρ →
      populationSemiDualContrast data gStar (gStar + u) ≤ -κ * ‖u‖ ^ 2)
    {m : ℕ} (hm : 0 < m) :
    (empiricalBatchMeasure data m).real
      {batch | r ≤ ‖empiricalBatchPotential data m batch - gStar‖} ≤
        (2 * r / δ + 2) ^ data.n *
          Real.exp (-(m : ℝ) * (κ * r ^ 2 - 4 * δ) ^ 2 / (8 * (r + δ) ^ 2)) := by
  let S := gaugeCoordinateGrid data gStar r δ
  have hsphere : ∀ z, IsBGauge data z → ‖z - gStar‖ = r →
      populationSemiDualContrast data gStar z ≤ -(κ * r ^ 2) := by
    intro z hz hzr
    have hu : IsBGaugeDirection data (z - gStar) := by
      simp only [IsBGaugeDirection, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      rw [hz, hstar, sub_self]
    have h := hmargin (z - gStar) hu (hzr.trans_le hrρ)
    rw [add_sub_cancel, hzr] at h
    simpa only [neg_mul] using h
  have htail := measure_empiricalPotential_far_le_of_sphere_net data hexact gStar hstar
    (r := r) (ε := 2 * δ) (Δ := κ * r ^ 2) (C := 2 * (r + δ))
    hr (by positivity) (by linarith) S
    (fun z hz => gaugeCoordinateGrid_isBGauge data gStar r δ hz)
    (fun z hz => gaugeCoordinateGrid_norm_le data gStar hstar hr.le hδ hz)
    (fun z hz hzr => gaugeCoordinateGrid_covers data gStar hr.le hδ z hz hzr.le)
    hsphere hm
  have hcard := gaugeCoordinateGrid_card_real_le data gStar hr.le hδ
  have hexp : -(m : ℝ) * (κ * r ^ 2 - 2 * (2 * δ)) ^ 2 /
      (2 * (2 * (r + δ)) ^ 2) =
        -(m : ℝ) * (κ * r ^ 2 - 4 * δ) ^ 2 / (8 * (r + δ) ^ 2) := by ring
  rw [hexp] at htail
  exact htail.trans (mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _))

/-- Choosing a grid step proportional to the squared radius gives the
polynomial covering factor and Gaussian radius scale needed for shrinking
neighborhoods of the population optimum. -/
theorem measure_empiricalPotential_far_le_polynomial_exp
    (data : HELLOSDOTData X Ω) (hexact : HasExactEmpiricalOTSolves data)
    (gStar : Fin data.n → ℝ) (hstar : IsBGauge data gStar)
    {ρ κ r : ℝ} (hκ : 0 < κ) (hr : 0 < r) (hrρ : r ≤ ρ) (hsmall : κ * r ≤ 8)
    (hmargin : ∀ u, IsBGaugeDirection data u → ‖u‖ ≤ ρ →
      populationSemiDualContrast data gStar (gStar + u) ≤ -κ * ‖u‖ ^ 2)
    {m : ℕ} (hm : 0 < m) :
    (empiricalBatchMeasure data m).real
      {batch | r ≤ ‖empiricalBatchPotential data m batch - gStar‖} ≤
        (16 / (κ * r) + 2) ^ data.n *
          Real.exp (-(m : ℝ) * κ ^ 2 * r ^ 2 / 128) := by
  let δ := κ * r ^ 2 / 8
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδr : δ ≤ r := by
    have h := mul_le_mul_of_nonneg_right hsmall hr.le
    dsimp [δ]
    nlinarith
  have hgap : κ * r ^ 2 - 4 * δ = κ * r ^ 2 / 2 := by dsimp [δ]; ring
  have htail := measure_empiricalPotential_far_le_of_local_norm_margin data hexact gStar hstar
    hr hrρ hδ (by rw [hgap]; positivity) hmargin hm
  have hratio : 2 * r / δ = 16 / (κ * r) := by
    dsimp [δ]
    field_simp [hκ.ne', hr.ne']
    ring
  rw [hratio] at htail
  have hdenom : 0 < 8 * (r + δ) ^ 2 := by positivity
  have hsq : (r + δ) ^ 2 ≤ 4 * r ^ 2 := by
    have h := pow_le_pow_left₀ (by positivity : 0 ≤ r + δ)
      (by linarith : r + δ ≤ 2 * r) 2
    nlinarith
  have hbase : κ ^ 2 * r ^ 2 / 128 ≤
      (κ * r ^ 2 - 4 * δ) ^ 2 / (8 * (r + δ) ^ 2) := by
    apply (le_div_iff₀ hdenom).mpr
    rw [hgap]
    have h := mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ κ ^ 2 * r ^ 2)
    nlinarith
  have hprod := mul_le_mul_of_nonneg_left hbase (show (0 : ℝ) ≤ m by positivity)
  have hexp : Real.exp (-(m : ℝ) * (κ * r ^ 2 - 4 * δ) ^ 2 /
      (8 * (r + δ) ^ 2)) ≤ Real.exp (-(m : ℝ) * κ ^ 2 * r ^ 2 / 128) := by
    apply Real.exp_le_exp.mpr
    convert neg_le_neg hprod using 1 <;> ring
  exact htail.trans (mul_le_mul_of_nonneg_left hexp (by positivity))

/-- The original regularity and exact-solve hypotheses imply a uniform
radius-dependent localization estimate. In particular, fixing the radius
recovers the exponential localization of Lemma F.10. -/
theorem empiricalPotential_localization_of_regularity
    (data : HELLOSDOTData X Ω) (hregular : HasHELLOSDOTRegularity data)
    (hexact : HasExactEmpiricalOTSolves data)
    (gStar : Fin data.n → ℝ) (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (hstar : IsBGauge data gStar) (hbalanced : data.populationMarginal gStar = data.b)
    (hJ : HasFDerivAt data.populationMarginal J gStar)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hcurvature : ∀ u, IsBGaugeDirection data u →
      lambda * (∑ j, (u j) ^ 2) ≤ ∑ j, u j * (J u) j) :
    ∃ ρ κ : ℝ, 0 < ρ ∧ 0 < κ ∧ ∀ {r : ℝ}, 0 < r → r ≤ ρ →
      ∀ {m : ℕ}, 0 < m →
        (empiricalBatchMeasure data m).real
          {batch | r ≤ ‖empiricalBatchPotential data m batch - gStar‖} ≤
            (16 / (κ * r) + 2) ^ data.n *
              Real.exp (-(m : ℝ) * κ ^ 2 * r ^ 2 / 128) := by
  obtain ⟨ρ, hρ, hmargin⟩ := populationSemiDualContrast_local_norm_margin data hregular
    gStar J hbalanced hJ hlambda hcurvature
  let κ := lambda / 4
  have hκ : 0 < κ := by dsimp [κ]; positivity
  let ρ' := min ρ (8 / κ)
  have hρ' : 0 < ρ' := lt_min hρ (by positivity)
  refine ⟨ρ', κ, hρ', hκ, ?_⟩
  intro r hr hrr m hm
  have hrρ : r ≤ ρ := hrr.trans (min_le_left _ _)
  have hrκ : r ≤ 8 / κ := hrr.trans (min_le_right _ _)
  have hsmall : κ * r ≤ 8 := by
    have h := (le_div_iff₀ hκ).mp hrκ
    nlinarith
  exact measure_empiricalPotential_far_le_polynomial_exp data hexact gStar hstar
    hκ hr hrρ hsmall hmargin hm

end DualGuided2026
