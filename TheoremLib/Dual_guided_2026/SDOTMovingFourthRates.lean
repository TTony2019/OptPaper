import TheoremLib.Dual_guided_2026.SDOTMovingFourthAsymptotics

/-!
# Fourth-moment negligibility of the actual moving-cell remainder
-/

namespace DualGuided2026

open MeasureTheory Filter
open scoped BigOperators Topology

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

theorem batchMovingCellFourthEnergy_scaled_tendsto_zero_of_localization
    (data : HELLOSDOTData X Ω) (hregular : HasHELLOSDOTRegularity data)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    {ρ κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ)
    (hlocal : ∀ {r : ℝ}, 0 < r → r ≤ ρ → ∀ {m : ℕ}, 0 < m →
      (empiricalBatchMeasure data m).real
        {batch | r ≤ ‖empiricalBatchPotential data m batch - gStar‖} ≤
          (16 / (κ * r) + 2) ^ data.n *
            Real.exp (-(m : ℝ) * κ ^ 2 * r ^ 2 / 128)) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * batchMovingCellFourthEnergy data gStar m)
      atTop (𝓝 0) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hbound⟩ :=
    batchMovingCellFourthEnergy_coordinateGrid_scaled_bound data hregular hexact
  let r := powerRadius (localizationExponent data.n)
  let δ := powerRadius (gridExponent data.n)
  let G := fun m => (2 * r m / δ m + 4) ^ data.n * r m
  let Q := fun m : ℕ => (m : ℝ) * δ m ^ 2
  let T := fun m : ℕ => (m : ℝ) ^ 2 * (empiricalBatchMeasure data m).real
    (batchPotentialLocalEvent data gStar m (r m))ᶜ
  have hG : Tendsto G atTop (𝓝 0) := localization_grid_radius_rate data.n
  have hQ : Tendsto Q atTop (𝓝 0) := gridRadius_quadratic_rate data.n
  have hT : Tendsto T atTop (𝓝 0) := by
    simpa only [Real.rpow_two] using
      batchPotentialLocalEvent_compl_scaled_tendsto_zero data gStar hρ hκ hlocal 2
  have hlim : Tendsto (fun m => C₁ * G m + C₂ * (Q m) ^ 2 +
      16 * (inverseWeightSum data) ^ 2 * T m) atTop (𝓝 0) := by
    simpa using
      ((hG.const_mul C₁).add ((hQ.pow 2).const_mul C₂)).add
        (hT.const_mul (16 * (inverseWeightSum data) ^ 2))
  have hα : 0 < localizationExponent data.n := by
    linarith [(localizationExponent_bounds data.n).1]
  have hrsmall : ∀ᶠ m : ℕ in atTop, r m ≤ 1 :=
    ((tendsto_order.1 (powerRadius_tendsto_zero hα)).2 1 (by norm_num)).mono
      (fun _ h => h.le)
  apply squeeze_zero' (Eventually.of_forall (fun m =>
    mul_nonneg (sq_nonneg _) (batchMovingCellFourthEnergy_nonneg data gStar m))) ?_ hlim
  filter_upwards [hrsmall, eventually_ge_atTop (1 : ℕ)] with m hrm hm
  have hmpos : 0 < m := by omega
  have hr : 0 < r m := powerRadius_pos hmpos _
  have hδ : 0 < δ m := powerRadius_pos hmpos _
  have hδr : δ m ≤ r m := gridRadius_le_localizationRadius data.n hm
  have h := hbound gStar hmpos hr hrm hδ hδr
  change _ ≤ C₁ * G m + C₂ * (Q m) ^ 2 + 16 * (inverseWeightSum data) ^ 2 * T m
  dsimp only [G, Q, T]
  convert h using 1
  ring

theorem batchMovingCellFourthEnergy_scaled_tendsto_zero
    (data : HELLOSDOTData X Ω) (hregular : HasHELLOSDOTRegularity data)
    (hexact : HasExactEmpiricalOTSolves data)
    (gStar : Fin data.n → ℝ) (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (hstar : IsBGauge data gStar) (hbalanced : data.populationMarginal gStar = data.b)
    (hJ : HasFDerivAt data.populationMarginal J gStar)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hcurvature : ∀ u, IsBGaugeDirection data u →
      lambda * (∑ j, (u j) ^ 2) ≤ ∑ j, u j * (J u) j) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ 2 * batchMovingCellFourthEnergy data gStar m)
      atTop (𝓝 0) := by
  obtain ⟨ρ, κ, hρ, hκ, hlocal⟩ := empiricalPotential_localization_of_regularity data hregular
    hexact gStar J hstar hbalanced hJ hlambda hcurvature
  exact batchMovingCellFourthEnergy_scaled_tendsto_zero_of_localization data hregular hexact
    gStar hρ hκ hlocal

end DualGuided2026
