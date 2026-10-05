import TheoremLib.Dual_guided_2026.SDOTMasterFourth
import TheoremLib.Dual_guided_2026.SDOTMovingFourthRates

/-!
# Negligibility of the actual fourth master remainder
-/

namespace DualGuided2026

open MeasureTheory Filter
open scoped BigOperators Topology

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

theorem linearizationFourthEnergy_isUniformLittleO_of_shrinkingLocalization
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
    (hoctic : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * r m ^ 8) atTop (𝓝 0))
    (hmoving : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * batchMovingCellFourthEnergy data gStar m)
      atTop (𝓝 0))
    (htail : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * (empiricalBatchMeasure data m).real
      (batchPotentialLocalEvent data gStar m (r m))ᶜ) atTop (𝓝 0)) :
    IsUniformLittleOInM data.rmax (linearizationFourthEnergy data gStar)
      (fun m => 1 / (m : ℝ) ^ 2) := by
  let K := (2 * (data.n.choose 2 : ℝ)) ^ 4 * (inverseWeightSum data) ^ 2
  let bound := fun m : ℕ =>
    48 * K * powerRadius 2 m +
      48 * ((m : ℝ) ^ 2 * batchMovingCellFourthEnergy data gStar m) +
      192 * C ^ 2 * ((m : ℝ) ^ 2 * r m ^ 8) +
      (16 * (inverseWeightSum data) ^ 2 * data.rmax) *
        ((m : ℝ) ^ 2 * (empiricalBatchMeasure data m).real
          (batchPotentialLocalEvent data gStar m (r m))ᶜ)
  have hboundlim : Tendsto bound atTop (𝓝 0) := by
    have ht := (powerRadius_tendsto_zero (by norm_num : (0 : ℝ) < 2)).const_mul (48 * K)
    have hm := hmoving.const_mul 48
    have hp := hoctic.const_mul (192 * C ^ 2)
    have htail' := htail.const_mul (16 * (inverseWeightSum data) ^ 2 * data.rmax)
    simpa only [bound, mul_zero, add_zero] using ((ht.add hm).add hp).add htail'
  apply uniformLittleO_of_eventually_scaled_bound data.rmax 2
    (linearizationFourthEnergy data gStar) bound
    (fun _ _ => integral_nonneg fun _ => sq_nonneg _) _ hboundlim
  have hrinside : ∀ᶠ m : ℕ in atTop, r m ≤ r₀ :=
    ((tendsto_order.1 hrlimit).2 r₀ hr₀).mono fun _ h => h.le
  filter_upwards [eventually_gt_atTop (0 : ℕ), hrinside] with m hm hrsmall
  intro R hR hRmax
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hRpos : 0 < R := Nat.zero_lt_one.trans_le hR
  have hRreal : (R : ℝ) ≤ data.rmax := by exact_mod_cast hRmax
  have hmaster := linearizationFourthEnergy_localization_bound data hregular hexact gStar J
    hbalanced hC hr₀ hpop hm hRpos (hrpos hm).le hrsmall
  have htie := averagedEmpiricalTieFourthEnergy_le data hregular hexact gStar hbalanced hm hRpos
  have htieScaled : (m : ℝ) ^ 2 * averagedEmpiricalTieFourthEnergy data m R ≤
      K * powerRadius 2 m := by
    have h := mul_le_mul_of_nonneg_left htie (sq_nonneg (m : ℝ))
    have hp : powerRadius 2 m = 1 / (m : ℝ) ^ 2 := by
      unfold powerRadius
      rw [Real.rpow_neg hmreal.le]
      norm_num [Real.rpow_natCast]
    rw [hp]
    calc
      _ ≤ (m : ℝ) ^ 2 * (K / (m : ℝ) ^ 4) := h
      _ = K * (1 / (m : ℝ) ^ 2) := by field_simp
  have htailR := mul_le_mul_of_nonneg_right hRreal
    (by positivity : 0 ≤ 16 * (inverseWeightSum data) ^ 2 *
      (empiricalBatchMeasure data m).real (batchPotentialLocalEvent data gStar m (r m))ᶜ)
  have hscaled := mul_le_mul_of_nonneg_left hmaster (sq_nonneg (m : ℝ))
  have htailScaled := mul_le_mul_of_nonneg_left htailR (sq_nonneg (m : ℝ))
  dsimp only [bound]
  nlinarith only [hscaled, htieScaled, htailScaled]

theorem linearizationFourthEnergy_isUniformLittleO_of_regularity
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
    IsUniformLittleOInM data.rmax (linearizationFourthEnergy data gStar)
      (fun m => 1 / (m : ℝ) ^ 2) := by
  obtain ⟨C, hC, r₀, hr₀, hpop⟩ :=
    populationLinearizationRemainder_local_quartic_energy_bound data gStar J hU hgStar hC2 hJ
  obtain ⟨ρ, κ, hρ, hκ, hlocal⟩ :=
    empiricalPotential_localization_of_regularity data hregular
      hexact gStar J hstar hbalanced hJ hlambda hcurvature
  have hα : 0 < localizationExponent data.n := by
    linarith [(localizationExponent_bounds data.n).1]
  have hmoving := batchMovingCellFourthEnergy_scaled_tendsto_zero_of_localization
    data hregular hexact gStar hρ hκ hlocal
  have htail : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * (empiricalBatchMeasure data m).real
      (batchPotentialLocalEvent data gStar m (powerRadius (localizationExponent data.n) m))ᶜ)
      atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using
      batchPotentialLocalEvent_compl_scaled_tendsto_zero data gStar hρ hκ hlocal 2
  have hoctic : Tendsto (fun m : ℕ => (m : ℝ) ^ 2 *
      powerRadius (localizationExponent data.n) m ^ 8) atTop (𝓝 0) := by
    have h := (localizationRadius_quartic_rate data.n).pow 2
    simpa only [mul_pow, ← pow_mul, Nat.reduceMul, zero_pow (by decide : (2 : ℕ) ≠ 0)] using h
  exact linearizationFourthEnergy_isUniformLittleO_of_shrinkingLocalization data hregular hexact
    gStar J hbalanced hC hr₀ hpop (powerRadius (localizationExponent data.n))
    (fun hm => powerRadius_pos hm _) (powerRadius_tendsto_zero hα) hoctic hmoving htail

theorem theorem_3_1_variance (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (hexact : HasExactEmpiricalOTSolves data) :
    IsUniformLittleOInM data.rmax
      (fun m R => data.varianceError m R - helloSDOTVarianceLeading data.n m R)
      (fun m => 1 / (m : ℝ) ^ 2) := by
  have hregular' := hregular
  obtain ⟨q₀, hq₀, hmoment, Cac, lambda, hCac, hlambda, hac,
    gStar, J, U, hstar, hbalanced, hU, hgStar, hC2, hJ, hcurvature⟩ := hregular'
  exact variance_asymptotic_of_linearizationFourthEnergy data hexact gStar hbalanced
    (linearizationFourthEnergy_isUniformLittleO_of_regularity data hregular hexact gStar J
      hstar hbalanced hU hgStar hC2 hJ hlambda hcurvature)

end DualGuided2026
