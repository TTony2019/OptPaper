import TheoremLib.Dual_guided_2026.SDOTMasterBounds
import TheoremLib.Dual_guided_2026.SDOTMovingAsymptotics

/-!
# Combining localization with the master remainder

A shrinking ball permits a direct partition of the bounded master
remainder. The population contribution has quartic energy, while the
moving-cell and tie contributions are controlled by their actual moments.
-/

namespace DualGuided2026

open MeasureTheory Filter
open scoped BigOperators Topology

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

/-- A shrinking-ball form of Proposition F.4. The localization and
moving-cell inputs concern the actual empirical solver and actual
remainders, and are proved separately from population regularity. -/
theorem linearizationEnergy_isUniformLittleO_of_shrinkingLocalization
    (data : HELLOSDOTData X Ω) (hregular : HasHELLOSDOTRegularity data)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (hbalanced : data.populationMarginal gStar = data.b)
    {C r₀ : ℝ} (hC : 0 ≤ C) (hr₀ : 0 < r₀)
    (hpop : ∀ g, ‖g - gStar‖ ≤ r₀ →
      weightedSquare data (populationLinearizationRemainder data gStar J g) ≤
        C * ‖g - gStar‖ ^ 4)
    (r : ℕ → ℝ) (hrpos : ∀ {m : ℕ}, 0 < m → 0 < r m)
    (hrlimit : Tendsto r atTop (𝓝 0))
    (hquartic : Tendsto (fun m : ℕ => (m : ℝ) * r m ^ 4) atTop (𝓝 0))
    (hmoving : IsUniformLittleOInM data.rmax (fun m _ => batchMovingCellEnergy data gStar m)
      (fun m => 1 / (m : ℝ)))
    (htail : Tendsto (fun m : ℕ => (m : ℝ) * (empiricalBatchMeasure data m).real
      (batchPotentialLocalEvent data gStar m (r m))ᶜ) atTop (𝓝 0)) :
    IsUniformLittleOInM data.rmax (linearizationEnergy data gStar)
      (fun m => 1 / (m : ℝ)) := by
  intro ε hε
  have hτ : 0 < ε / 16 := by positivity
  obtain ⟨M₁, hM₁⟩ := averagedEmpiricalTieEnergy_uniformLittleO data hregular hexact (ε / 16) hτ
  obtain ⟨M₂, hM₂⟩ := hmoving (ε / 16) hτ
  have hpopRate : Tendsto (fun m : ℕ => 8 * C * ((m : ℝ) * r m ^ 4)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hquartic.const_mul (8 * C)
  have htailRate : Tendsto (fun m : ℕ => (4 * inverseWeightSum data * data.rmax) *
      ((m : ℝ) * (empiricalBatchMeasure data m).real
        (batchPotentialLocalEvent data gStar m (r m))ᶜ)) atTop (𝓝 0) := by
    simpa only [mul_zero] using htail.const_mul (4 * inverseWeightSum data * data.rmax)
  have hgood : ∀ᶠ m : ℕ in atTop, 0 < m ∧ r m < r₀ ∧
      8 * C * ((m : ℝ) * r m ^ 4) < ε / 4 ∧
      (4 * inverseWeightSum data * data.rmax) *
        ((m : ℝ) * (empiricalBatchMeasure data m).real
          (batchPotentialLocalEvent data gStar m (r m))ᶜ) < ε / 4 := by
    filter_upwards [eventually_gt_atTop (0 : ℕ), (tendsto_order.1 hrlimit).2 r₀ hr₀,
      (tendsto_order.1 hpopRate).2 (ε / 4) (by positivity),
      (tendsto_order.1 htailRate).2 (ε / 4) (by positivity)] with m hm hr hp ht
    exact ⟨hm, hr, hp, ht⟩
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hgood
  refine ⟨max M₀ (max M₁ M₂), ?_⟩
  intro m hm R hR hRmax
  have hm₀ := (le_max_left M₀ (max M₁ M₂)).trans hm
  obtain ⟨hmpos, hrsmall, hpopSmall, htailSmall⟩ := hM₀ m hm₀
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hRpos : 0 < R := lt_of_lt_of_le Nat.zero_lt_one hR
  have hRreal : (R : ℝ) ≤ data.rmax := by exact_mod_cast hRmax
  have htie := hM₁ m ((le_max_left M₁ M₂).trans ((le_max_right M₀ (max M₁ M₂)).trans hm))
    R hR hRmax
  have hmove := hM₂ m ((le_max_right M₁ M₂).trans ((le_max_right M₀ (max M₁ M₂)).trans hm))
    R hR hRmax
  rw [abs_of_nonneg (averagedEmpiricalTieEnergy_nonneg data m R),
    abs_of_pos (one_div_pos.mpr hmreal)] at htie
  have hMovingNonneg : 0 ≤ batchMovingCellEnergy data gStar m :=
    integral_nonneg fun _ => weightedSquare_nonneg data _
  rw [abs_of_nonneg hMovingNonneg,
    abs_of_pos (one_div_pos.mpr hmreal)] at hmove
  have htieScaled : (m : ℝ) * averagedEmpiricalTieEnergy data m R ≤ ε / 16 := by
    have h := mul_le_mul_of_nonneg_left htie hmreal.le
    field_simp at h
    nlinarith
  have hmoveScaled : (m : ℝ) * batchMovingCellEnergy data gStar m ≤ ε / 16 := by
    have h := mul_le_mul_of_nonneg_left hmove hmreal.le
    field_simp at h
    nlinarith
  have hmaster := linearizationEnergy_localization_bound data hregular hexact gStar J
    hbalanced hC hr₀ hpop hmpos hRpos (hrpos hmpos).le hrsmall.le
  have hB := inverseWeightSum_nonneg data
  have htailR := mul_le_mul_of_nonneg_right hRreal
    (by positivity : 0 ≤ 4 * inverseWeightSum data *
      (empiricalBatchMeasure data m).real (batchPotentialLocalEvent data gStar m (r m))ᶜ)
  have hscaled := mul_le_mul_of_nonneg_left hmaster hmreal.le
  have htailScaled := mul_le_mul_of_nonneg_left htailR hmreal.le
  have hsmall : (m : ℝ) * linearizationEnergy data gStar m R ≤ ε := by
    nlinarith [htieScaled, hmoveScaled, htailScaled]
  rw [abs_of_nonneg (linearizationEnergy_nonneg data gStar m R),
    abs_of_pos (one_div_pos.mpr hmreal)]
  have hdiv := (le_div_iff₀ hmreal).mpr (by simpa only [mul_comm] using hsmall)
  simpa only [div_eq_mul_inv, one_mul] using hdiv

/-- Proposition F.4 (39), deduced from population regularity and exact
empirical solves. Every localization and moving-cell premise of the
shrinking-ball reduction is established from these original assumptions. -/
theorem linearizationEnergy_isUniformLittleO_of_regularity
    (data : HELLOSDOTData X Ω) (hregular : HasHELLOSDOTRegularity data)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (hstar : IsBGauge data gStar) (hbalanced : data.populationMarginal gStar = data.b)
    {U : Set (Fin data.n → ℝ)} (hU : IsOpen U) (hgStar : gStar ∈ U)
    (hC2 : ContDiffOn ℝ 2 data.populationMarginal U)
    (hJ : HasFDerivAt data.populationMarginal J gStar)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hcurvature : ∀ u, IsBGaugeDirection data u →
      lambda * (∑ j, (u j) ^ 2) ≤ ∑ j, u j * (J u) j) :
    IsUniformLittleOInM data.rmax (linearizationEnergy data gStar)
      (fun m => 1 / (m : ℝ)) := by
  obtain ⟨C, hC, r₀, hr₀, hpop⟩ :=
    populationLinearizationRemainder_local_quartic_energy_bound data gStar J hU hgStar hC2 hJ
  obtain ⟨ρ, κ, hρ, hκ, hlocal⟩ := empiricalPotential_localization_of_regularity data hregular
    hexact gStar J hstar hbalanced hJ hlambda hcurvature
  have hα : 0 < localizationExponent data.n := by
    linarith [(localizationExponent_bounds data.n).1]
  have hmovingRate := batchMovingCellEnergy_scaled_tendsto_zero_of_localization
    data hregular hexact gStar hρ hκ hlocal
  have hmoving : IsUniformLittleOInM data.rmax
      (fun m _ => batchMovingCellEnergy data gStar m) (fun m => 1 / (m : ℝ)) := by
    simpa only [pow_one] using uniformLittleO_of_scaled_bound data.rmax 1
      (fun m _ => batchMovingCellEnergy data gStar m)
      (fun m => (m : ℝ) * batchMovingCellEnergy data gStar m)
      (fun m _ => batchMovingCellEnergy_nonneg data gStar m)
      (fun _ _ _ _ => by simp) hmovingRate
  have htail : Tendsto (fun m : ℕ => (m : ℝ) * (empiricalBatchMeasure data m).real
      (batchPotentialLocalEvent data gStar m (powerRadius (localizationExponent data.n) m))ᶜ)
      atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      batchPotentialLocalEvent_compl_scaled_tendsto_zero data gStar hρ hκ hlocal 1
  exact linearizationEnergy_isUniformLittleO_of_shrinkingLocalization data hregular hexact
    gStar J hbalanced hC hr₀ hpop (powerRadius (localizationExponent data.n))
    (fun hm => powerRadius_pos hm _) (powerRadius_tendsto_zero hα)
    (localizationRadius_quartic_rate data.n) hmoving htail

/-- The expectation conclusion of Theorem III.1, including uniformity over
the fixed finite repetition range. -/
theorem theorem_3_1_mean (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (hexact : HasExactEmpiricalOTSolves data) :
    IsUniformLittleOInM data.rmax
      (fun m R => data.meanError m R - helloSDOTMeanLeading data.n m R)
      (fun m => 1 / (m : ℝ)) := by
  have hregular' := hregular
  obtain ⟨_, _, _, _, lambda, _, hlambda, _, gStar, J, U, hstar, hbalanced,
    hU, hgStar, hC2, hJ, hcurvature⟩ := hregular'
  exact mean_asymptotic_of_linearizationEnergy data hexact gStar hbalanced
    (linearizationEnergy_isUniformLittleO_of_regularity data hregular hexact gStar J
      hstar hbalanced hU hgStar hC2 hJ hlambda hcurvature)

end DualGuided2026
