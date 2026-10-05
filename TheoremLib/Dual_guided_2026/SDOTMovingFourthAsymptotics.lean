import TheoremLib.Dual_guided_2026.SDOTMasterFourth
import TheoremLib.Dual_guided_2026.SDOTMovingAsymptotics

/-!
# Fourth-moment negligibility at the empirical optimizer

Finite-grid bracketing controls the actual sample-dependent potential on
the localization event. The remainder is globally bounded on its complement.
-/

namespace DualGuided2026

open MeasureTheory Filter
open scoped BigOperators Topology

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

theorem batchMovingCellFourthEnergy_nonneg (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (m : ℕ) : 0 ≤ batchMovingCellFourthEnergy data gStar m :=
  integral_nonneg fun _ => sq_nonneg _

theorem integrable_gridEndpointFourthEnergy (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) {m : ℕ} (hm : 0 < m)
    (grid : Finset (Fin data.n → ℝ)) (δ : ℝ) :
    Integrable (gridEndpointFourthEnergy data gStar grid δ) (sourceBatchMeasure data m) := by
  have hi (g : Fin data.n → ℝ) (j : Fin data.n) (t : ℝ) :
      Integrable (fun samples => movingCellEmpiricalRemainder data gStar samples
        (shiftPotentialCoordinate g j t) j ^ 4) (sourceBatchMeasure data m) := by
    convert (memLp_fixedMovingCellEmpiricalRemainder_sq data gStar
      (shiftPotentialCoordinate g j t) hm j).integrable_sq using 1
    ext samples
    ring
  exact integrable_finset_sum grid fun g _ => integrable_finset_sum Finset.univ fun j _ =>
    ((hi g j _).add (hi g j _)).div_const _

theorem batchMovingCellFourthEnergy_finiteGrid_bound (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (L : NNReal)
    (hL : LipschitzWith L data.populationMarginal) (gStar : Fin data.n → ℝ)
    {m : ℕ} (hm : 0 < m) (grid : Finset (Fin data.n → ℝ)) (r : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcover : ∀ h : Fin data.n → ℝ, ‖h - gStar‖ ≤ r →
      ∃ g ∈ grid, ∀ k, |h k - g k| ≤ δ) :
    batchMovingCellFourthEnergy data gStar m ≤
      8 * data.n * (∫ samples, gridEndpointFourthEnergy data gStar grid δ samples
        ∂sourceBatchMeasure data m) +
        2048 * data.n * (L : ℝ) ^ 4 * δ ^ 4 * (∑ j, 1 / (data.b j) ^ 2) +
          16 * (inverseWeightSum data) ^ 2 * (empiricalBatchMeasure data m).real
            (batchPotentialLocalEvent data gStar m r)ᶜ := by
  classical
  let A := batchPotentialLocalEvent data gStar m r
  let B := 16 * (inverseWeightSum data) ^ 2
  let K := 2048 * data.n * (L : ℝ) ^ 4 * δ ^ 4 * (∑ j, 1 / (data.b j) ^ 2)
  have hB : 0 ≤ B := by positivity
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : MeasurableSet A := measurableSet_batchPotentialLocalEvent data hexact gStar hm r
  have hF := (memLp_batchMovingCellEnergy data hexact gStar hm).integrable_sq
  have hgrid : Integrable (fun batch : (Fin m → X) × Ω =>
      gridEndpointFourthEnergy data gStar grid δ batch.1) (empiricalBatchMeasure data m) :=
    (integrable_gridEndpointFourthEnergy data gStar hm grid δ).comp_fst (data.solverMeasure m)
  have hInd : Integrable (Aᶜ.indicator (fun _ => B)) (empiricalBatchMeasure data m) :=
    (integrable_const B).indicator hA.compl
  have hpoint (batch : (Fin m → X) × Ω) :
      (weightedSquare data (movingCellEmpiricalRemainder data gStar batch.1
        (empiricalBatchPotential data m batch))) ^ 2 ≤
        8 * data.n * gridEndpointFourthEnergy data gStar grid δ batch.1 + K +
          Aᶜ.indicator (fun _ => B) batch := by
    by_cases hb : batch ∈ A
    · rw [Set.indicator_of_notMem (not_not.mpr hb : batch ∉ Aᶜ)]
      simpa only [add_zero] using movingCellEmpiricalRemainder_finiteGrid_fourth_bound
        data L hL batch.1 gStar _ grid hδ (hcover _ hb)
    · rw [Set.indicator_of_mem (show batch ∈ Aᶜ from hb)]
      have hgridNonneg : 0 ≤ gridEndpointFourthEnergy data gStar grid δ batch.1 :=
        Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun j _ => by positivity
      have hbound := pow_le_pow_left₀ (weightedSquare_nonneg data _)
        (movingCellEmpiricalRemainder_energy_le data hm batch.1 gStar
          (empiricalBatchPotential data m batch)) 2
      change _ ≤ (4 * inverseWeightSum data) ^ 2 at hbound
      change _ ≤ 8 * data.n * gridEndpointFourthEnergy data gStar grid δ batch.1 + K + B
      dsimp [B] at hbound ⊢
      nlinarith only [hbound, hK, mul_nonneg
        (by positivity : (0 : ℝ) ≤ 8 * data.n) hgridNonneg]
  have hbase : Integrable (fun batch : (Fin m → X) × Ω =>
      8 * data.n * gridEndpointFourthEnergy data gStar grid δ batch.1 + K)
      (empiricalBatchMeasure data m) := (hgrid.const_mul _).add (integrable_const K)
  have h := integral_mono hF (hbase.add hInd) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add hbase hInd, integral_add (hgrid.const_mul _) (integrable_const K),
    integral_const_mul, integral_const, probReal_univ, one_smul,
    integral_indicator_const B hA.compl] at h
  have hfst : (∫ batch, gridEndpointFourthEnergy data gStar grid δ batch.1
      ∂empiricalBatchMeasure data m) =
      ∫ samples, gridEndpointFourthEnergy data gStar grid δ samples ∂sourceBatchMeasure data m := by
    simpa only [empiricalBatchMeasure, probReal_univ, one_smul] using
      (integral_fun_fst (μ := sourceBatchMeasure data m) (ν := data.solverMeasure m)
        (gridEndpointFourthEnergy data gStar grid δ))
  rw [hfst] at h
  change batchMovingCellFourthEnergy data gStar m ≤ _ at h
  simpa only [K, B, smul_eq_mul, mul_comm] using h

/-- After scaling by `m²`, the grid contribution is bounded by its
cardinality times the localization radius. This exposes exactly the rates
needed for the variance proof. -/
theorem batchMovingCellFourthEnergy_coordinateGrid_scaled_bound
    (data : HELLOSDOTData X Ω) (hregular : HasHELLOSDOTRegularity data)
    (hexact : HasExactEmpiricalOTSolves data) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ (gStar : Fin data.n → ℝ) {m : ℕ}, 0 < m →
        ∀ {r δ : ℝ}, 0 < r → r ≤ 1 → 0 < δ → δ ≤ r →
          (m : ℝ) ^ 2 * batchMovingCellFourthEnergy data gStar m ≤
            C₁ * (2 * r / δ + 4) ^ data.n * r + C₂ * ((m : ℝ) * δ ^ 2) ^ 2 +
              16 * (inverseWeightSum data) ^ 2 * (m : ℝ) ^ 2 *
                (empiricalBatchMeasure data m).real
                  (batchPotentialLocalEvent data gStar m r)ᶜ := by
  obtain ⟨L, hL⟩ := populationMarginal_lipschitz data hregular
  obtain ⟨C, hC, hgridIntegral⟩ := gridEndpointFourthEnergy_integral_le data hregular
  let W := ∑ j, 1 / (data.b j) ^ 2
  have hW : 0 ≤ W := Finset.sum_nonneg fun j _ => by positivity
  let A := 16 * C + 48 * C ^ 2
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨8 * data.n * (2 * W) * A, 2048 * data.n * (L : ℝ) ^ 4 * W,
    by positivity, by positivity, ?_⟩
  intro gStar m hm r δ hr hrone hδ hδr
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  let grid := coordinateGrid gStar r δ
  let ρ := r + δ + 2 * δ
  have hρ : 0 < ρ := by dsimp [ρ]; positivity
  have hρr : ρ ≤ 4 * r := by dsimp [ρ]; linarith
  have hgrid := hgridIntegral gStar hm grid (by linarith : 0 < r + δ) hδ.le
    (fun g hg => coordinateGrid_norm_le gStar hr.le hδ hg)
  have hscaledGrid := mul_le_mul_of_nonneg_left hgrid (sq_nonneg (m : ℝ))
  have hcancel : (m : ℝ) ^ 2 * ((grid.card : ℝ) * (2 * W) *
      (4 * C * ρ / (m : ℝ) ^ 3 + 3 * C ^ 2 * ρ ^ 2 / (m : ℝ) ^ 2)) =
      (grid.card : ℝ) * (2 * W) * (4 * C * (ρ / (m : ℝ)) + 3 * C ^ 2 * ρ ^ 2) := by
    field_simp
  change (m : ℝ) ^ 2 * (∫ samples, gridEndpointFourthEnergy data gStar grid δ samples
    ∂sourceBatchMeasure data m) ≤ _ at hscaledGrid
  rw [hcancel] at hscaledGrid
  have hρdiv : ρ / (m : ℝ) ≤ 4 * r := (div_le_self hρ.le hmone).trans hρr
  have hρsquare : ρ ^ 2 ≤ 16 * r := by
    have hs := pow_le_pow_left₀ hρ.le hρr 2
    have hr2 : r ^ 2 ≤ r := by nlinarith
    nlinarith
  have hsmall : 4 * C * (ρ / (m : ℝ)) + 3 * C ^ 2 * ρ ^ 2 ≤ A * r := by
    have hfirst := mul_le_mul_of_nonneg_left hρdiv (by positivity : (0 : ℝ) ≤ 4 * C)
    have hsecond := mul_le_mul_of_nonneg_left hρsquare (by positivity : (0 : ℝ) ≤ 3 * C ^ 2)
    dsimp [A]
    nlinarith
  have hcard : (grid.card : ℝ) ≤ (2 * r / δ + 4) ^ data.n :=
    (coordinateGrid_card_real_le gStar hr.le hδ).trans
      (pow_le_pow_left₀ (by positivity) (by linarith) _)
  have hgridRate : (m : ℝ) ^ 2 * (∫ samples,
      gridEndpointFourthEnergy data gStar grid δ samples ∂sourceBatchMeasure data m) ≤
        (2 * r / δ + 4) ^ data.n * (2 * W) * A * r := by
    calc
      _ ≤ (grid.card : ℝ) * (2 * W) * (A * r) :=
        hscaledGrid.trans (mul_le_mul_of_nonneg_left hsmall (by positivity))
      _ ≤ (2 * r / δ + 4) ^ data.n * (2 * W) * (A * r) := by gcongr
      _ = _ := by ring
  have hpoint := batchMovingCellFourthEnergy_finiteGrid_bound data hexact L hL gStar hm
    grid r hδ.le (coordinateGrid_covers gStar hr.le hδ)
  have hscaled := mul_le_mul_of_nonneg_left hpoint (sq_nonneg (m : ℝ))
  have hgridRate' := mul_le_mul_of_nonneg_left hgridRate
    (by positivity : (0 : ℝ) ≤ 8 * data.n)
  calc
    (m : ℝ) ^ 2 * batchMovingCellFourthEnergy data gStar m ≤
        (m : ℝ) ^ 2 * (8 * data.n * (∫ samples,
          gridEndpointFourthEnergy data gStar grid δ samples ∂sourceBatchMeasure data m) +
          2048 * data.n * (L : ℝ) ^ 4 * δ ^ 4 * W +
          16 * (inverseWeightSum data) ^ 2 * (empiricalBatchMeasure data m).real
            (batchPotentialLocalEvent data gStar m r)ᶜ) := hscaled
    _ ≤ 8 * data.n * ((2 * r / δ + 4) ^ data.n * (2 * W) * A * r) +
        (m : ℝ) ^ 2 * (2048 * data.n * (L : ℝ) ^ 4 * δ ^ 4 * W) +
          (m : ℝ) ^ 2 * (16 * (inverseWeightSum data) ^ 2 *
            (empiricalBatchMeasure data m).real (batchPotentialLocalEvent data gStar m r)ᶜ) := by
      simp only [mul_add]
      nlinarith only [hgridRate']
    _ = _ := by ring

end DualGuided2026
