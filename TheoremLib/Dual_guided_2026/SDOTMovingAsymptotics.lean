import TheoremLib.Dual_guided_2026.SDOTMasterBounds
import TheoremLib.Dual_guided_2026.SDOTNetLocalization
import TheoremLib.Dual_guided_2026.SDOTRates

/-!
# Negligibility of the actual moving-cell remainder

The shrinking-radius finite-grid estimate is applied to the empirical
oracle itself. Localization bounds its complement, while the explicit
radius and grid powers make the local energy negligible after scaling by
the sample size.
-/

namespace DualGuided2026

open MeasureTheory Filter
open scoped BigOperators Topology

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

theorem batchPotentialLocalEvent_compl_scaled_tendsto_zero
    (data : HELLOSDOTData X Ω) (gStar : Fin data.n → ℝ)
    {ρ κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ)
    (hlocal : ∀ {r : ℝ}, 0 < r → r ≤ ρ → ∀ {m : ℕ}, 0 < m →
      (empiricalBatchMeasure data m).real
        {batch | r ≤ ‖empiricalBatchPotential data m batch - gStar‖} ≤
          (16 / (κ * r) + 2) ^ data.n *
            Real.exp (-(m : ℝ) * κ ^ 2 * r ^ 2 / 128))
    (k : ℝ) :
    Tendsto (fun m : ℕ => (m : ℝ) ^ k * (empiricalBatchMeasure data m).real
      (batchPotentialLocalEvent data gStar m
        (powerRadius (localizationExponent data.n) m))ᶜ) atTop (𝓝 0) := by
  let r := powerRadius (localizationExponent data.n)
  have hα : 0 < localizationExponent data.n := by
    linarith [(localizationExponent_bounds data.n).1]
  have hinside : ∀ᶠ m : ℕ in atTop, r m ≤ ρ :=
    ((tendsto_order.1 (powerRadius_tendsto_zero hα)).2 ρ hρ).mono (fun _ h => h.le)
  have hlim := localization_exponential_tail_rate_general data.n k (16 / κ) (κ ^ 2 / 128)
    (by positivity) (by positivity)
  apply squeeze_zero' (Eventually.of_forall (fun m => by positivity)) ?_ hlim
  filter_upwards [hinside, eventually_gt_atTop (0 : ℕ)] with m hmr hm
  have htail := hlocal (powerRadius_pos hm _) hmr hm
  have hsub : (batchPotentialLocalEvent data gStar m (r m))ᶜ ⊆
      {batch | r m ≤ ‖empiricalBatchPotential data m batch - gStar‖} := by
    intro batch hbatch
    change ¬ ‖empiricalBatchPotential data m batch - gStar‖ ≤ r m at hbatch
    exact (not_le.mp hbatch).le
  have hmeasure := (measureReal_mono hsub).trans htail
  have hscaled := mul_le_mul_of_nonneg_left hmeasure
    (Real.rpow_nonneg (Nat.cast_nonneg m) k)
  have hexp : -(m : ℝ) * κ ^ 2 * powerRadius (localizationExponent data.n) m ^ 2 / 128 =
      -(κ ^ 2 / 128) * (m : ℝ) * powerRadius (localizationExponent data.n) m ^ 2 := by ring
  rw [hexp] at hscaled
  simpa only [mul_assoc, div_mul_eq_div_div] using hscaled

theorem batchMovingCellEnergy_nonneg (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (m : ℕ) : 0 ≤ batchMovingCellEnergy data gStar m :=
  integral_nonneg (fun _ => weightedSquare_nonneg data _)

theorem batchMovingCellEnergy_scaled_tendsto_zero_of_localization
    (data : HELLOSDOTData X Ω) (hregular : HasHELLOSDOTRegularity data)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    {ρ κ : ℝ} (hρ : 0 < ρ) (hκ : 0 < κ)
    (hlocal : ∀ {r : ℝ}, 0 < r → r ≤ ρ → ∀ {m : ℕ}, 0 < m →
      (empiricalBatchMeasure data m).real
        {batch | r ≤ ‖empiricalBatchPotential data m batch - gStar‖} ≤
          (16 / (κ * r) + 2) ^ data.n *
            Real.exp (-(m : ℝ) * κ ^ 2 * r ^ 2 / 128)) :
    Tendsto (fun m : ℕ => (m : ℝ) * batchMovingCellEnergy data gStar m) atTop (𝓝 0) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hbound⟩ :=
    batchMovingCellEnergy_coordinateGrid_bound data hregular hexact
  let r := powerRadius (localizationExponent data.n)
  let δ := powerRadius (gridExponent data.n)
  let G := fun m => (2 * r m / δ m + 4) ^ data.n * r m
  let Q := fun m : ℕ => (m : ℝ) * δ m ^ 2
  let T := fun m : ℕ => (m : ℝ) * (empiricalBatchMeasure data m).real
    (batchPotentialLocalEvent data gStar m (r m))ᶜ
  have hG : Tendsto G atTop (𝓝 0) := localization_grid_radius_rate data.n
  have hQ : Tendsto Q atTop (𝓝 0) := gridRadius_quadratic_rate data.n
  have hT : Tendsto T atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using
      batchPotentialLocalEvent_compl_scaled_tendsto_zero data gStar hρ hκ hlocal 1
  have hlim : Tendsto (fun m => 4 * C₁ * G m + C₂ * Q m +
      4 * inverseWeightSum data * T m) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((hG.const_mul (4 * C₁)).add (hQ.const_mul C₂)).add
        (hT.const_mul (4 * inverseWeightSum data))
  apply squeeze_zero' (Eventually.of_forall (fun m =>
    mul_nonneg (Nat.cast_nonneg _) (batchMovingCellEnergy_nonneg data gStar m))) ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmpos : 0 < m := by omega
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hr : 0 < r m := powerRadius_pos hmpos _
  have hδ : 0 < δ m := powerRadius_pos hmpos _
  have hδr : δ m ≤ r m := gridRadius_le_localizationRadius data.n hm
  have h := mul_le_mul_of_nonneg_left (hbound gStar hmpos hr hδ) hmreal.le
  have hgrid : (2 * r m / δ m + 2) ^ data.n * (r m + 3 * δ m) ≤ 4 * G m := by
    dsimp only [G]
    calc
      _ ≤ (2 * r m / δ m + 4) ^ data.n * (4 * r m) := by
        apply mul_le_mul
        · exact pow_le_pow_left₀ (by positivity) (by linarith) _
        · linarith
        · positivity
        · positivity
      _ = _ := by ring
  have hcancel (a : ℝ) : (m : ℝ) * (a / (m : ℝ)) = a := by field_simp
  simp only [mul_add] at h
  rw [hcancel] at h
  have hgridScaled := mul_le_mul_of_nonneg_left hgrid hC₁
  change _ ≤ 4 * C₁ * G m + C₂ * Q m + 4 * inverseWeightSum data * T m
  dsimp only [Q, T]
  nlinarith

/-- Lemma F.7 follows from the original assumptions, with no rate premise
on the empirical oracle or on its chosen exact maximizer. -/
theorem batchMovingCellEnergy_scaled_tendsto_zero
    (data : HELLOSDOTData X Ω) (hregular : HasHELLOSDOTRegularity data)
    (hexact : HasExactEmpiricalOTSolves data)
    (gStar : Fin data.n → ℝ) (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (hstar : IsBGauge data gStar) (hbalanced : data.populationMarginal gStar = data.b)
    (hJ : HasFDerivAt data.populationMarginal J gStar)
    {lambda : ℝ} (hlambda : 0 < lambda)
    (hcurvature : ∀ u, IsBGaugeDirection data u →
      lambda * (∑ j, (u j) ^ 2) ≤ ∑ j, u j * (J u) j) :
    Tendsto (fun m : ℕ => (m : ℝ) * batchMovingCellEnergy data gStar m) atTop (𝓝 0) := by
  obtain ⟨ρ, κ, hρ, hκ, hlocal⟩ := empiricalPotential_localization_of_regularity data hregular
    hexact gStar J hstar hbalanced hJ hlambda hcurvature
  exact batchMovingCellEnergy_scaled_tendsto_zero_of_localization data hregular hexact
    gStar hρ hκ hlocal

end DualGuided2026
