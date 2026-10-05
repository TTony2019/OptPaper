import TheoremLib.Dual_guided_2026.SDOTFiniteGrid
import TheoremLib.Dual_guided_2026.SDOTPopulationRemainder
import TheoremLib.Dual_guided_2026.SDOTVariance
import Mathlib.Algebra.Order.Chebyshev

/-!
# Local bounds for the master marginal remainder

The master remainder is globally bounded by mass-vector bounds. On the
event where every empirical potential lies near the population potential,
its exact decomposition gives a quartic population term and the averaged
tie and moving-cell terms.
-/

namespace DualGuided2026

open MeasureTheory
open scoped BigOperators

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

theorem weightedSquare_nonneg (data : HELLOSDOTData X Ω) (u : Fin data.n → ℝ) :
    0 ≤ weightedSquare data u :=
  Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (data.b_pos j).le

theorem weightedSquare_sub_sub_add_le (data : HELLOSDOTData X Ω)
    (a b c d : Fin data.n → ℝ) :
    weightedSquare data (a - b - c + d) ≤
      4 * (weightedSquare data a + weightedSquare data b +
        weightedSquare data c + weightedSquare data d) := by
  have hscalar (j : Fin data.n) : (a j - b j - c j + d j) ^ 2 ≤
      4 * ((a j) ^ 2 + (b j) ^ 2 + (c j) ^ 2 + (d j) ^ 2) := by
    nlinarith [sq_nonneg (a j + b j), sq_nonneg (a j + c j), sq_nonneg (a j - d j),
      sq_nonneg (b j - c j), sq_nonneg (b j + d j), sq_nonneg (c j + d j)]
  calc
    _ ≤ ∑ j, (4 * ((a j) ^ 2 + (b j) ^ 2 + (c j) ^ 2 + (d j) ^ 2)) / data.b j :=
      Finset.sum_le_sum fun j _ =>
        div_le_div_of_nonneg_right (hscalar j) (data.b_pos j).le
    _ = _ := by
      simp only [weightedSquare, mul_div_assoc, add_div, mul_add, Finset.sum_add_distrib,
        Finset.mul_sum]

theorem weightedSquare_iidAverage_le {A : Type*} (data : HELLOSDOTData X Ω)
    (f : A → Fin data.n → ℝ) (R : ℕ) (samples : Fin R → A) :
    weightedSquare data (fun j => iidAverage (fun a => f a j) R samples) ≤
      iidAverage (fun a => weightedSquare data (f a)) R samples := by
  have hcoord (j : Fin data.n) :
      (iidAverage (fun a => f a j) R samples) ^ 2 / data.b j ≤
        (1 / (R : ℝ)) * ∑ r, (f (samples r) j) ^ 2 / data.b j := by
    have hj := sum_div_card_sq_le_sum_sq_div_card
      (s := Finset.univ) (f := fun r : Fin R => f (samples r) j)
    simp only [Finset.card_univ, Fintype.card_fin] at hj
    convert div_le_div_of_nonneg_right hj (data.b_pos j).le using 1 <;>
      simp only [iidAverage, div_eq_mul_inv, ← Finset.sum_mul] <;> ring
  calc
    _ ≤ ∑ j, (1 / (R : ℝ)) * ∑ r, (f (samples r) j) ^ 2 / data.b j :=
      Finset.sum_le_sum fun j _ => hcoord j
    _ = _ := by
      simp only [iidAverage, weightedSquare, ← Finset.mul_sum]
      rw [Finset.sum_comm]

theorem marginalLinearizationRemainder_abs_le_two (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (hbalanced : data.populationMarginal gStar = data.b)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R)
    (batches : Fin R → ((Fin m → X) × Ω)) (j : Fin data.n) :
    |marginalLinearizationRemainder data gStar m R batches j| ≤ 2 := by
  have hcell (x : X) : ‖centeredCellIndicator data gStar j x‖ ≤ 1 := by
    have hx := cellIndicator_mem_Icc data gStar j x
    have hp0 := populationMarginal_nonneg data gStar j
    have hp1 := populationMarginal_le_one data gStar j
    simp only [centeredCellIndicator, Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hbatch (batch : (Fin m → X) × Ω) :
      ‖batchCategoricalFluctuation data gStar m batch j‖ ≤ 1 :=
    norm_iidAverage_le hcell hm batch.1
  have hz := norm_iidAverage_le hbatch hR batches
  change |averagedCategoricalFluctuation data gStar m R batches j| ≤ 1 at hz
  have hb0 : 0 ≤ data.b j := (data.b_pos j).le
  have hb1 : data.b j ≤ 1 := by rw [← hbalanced]; exact populationMarginal_le_one data gStar j
  have hp0 := populationMarginal_nonneg data (averagedEmpiricalPotential data m R batches) j
  have hp1 := populationMarginal_le_one data (averagedEmpiricalPotential data m R batches) j
  have hdev : |data.populationMarginal (averagedEmpiricalPotential data m R batches) j -
      data.b j| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  exact (abs_add_le _ _).trans (by linarith)

theorem marginalLinearizationRemainder_energy_le (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (hbalanced : data.populationMarginal gStar = data.b)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R)
    (batches : Fin R → ((Fin m → X) × Ω)) :
    weightedSquare data (marginalLinearizationRemainder data gStar m R batches) ≤
      4 * inverseWeightSum data := by
  calc
    _ ≤ ∑ j, 4 / data.b j := by
      apply Finset.sum_le_sum
      intro j _
      apply div_le_div_of_nonneg_right _ (data.b_pos j).le
      have hj := marginalLinearizationRemainder_abs_le_two data gStar hbalanced hm hR batches j
      simpa only [sq_abs, show (2 : ℝ) ^ 2 = 4 by norm_num] using
        (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)).2 hj
    _ = _ := by simp only [inverseWeightSum, Finset.mul_sum]; congr 1; ext j; ring

theorem marginalLinearizationRemainder_local_energy_bound
    (data : HELLOSDOTData X Ω) (gStar : Fin data.n → ℝ)
    (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (hbalanced : data.populationMarginal gStar = data.b)
    {C r₀ : ℝ} (hC : 0 ≤ C) (_hr₀ : 0 < r₀)
    (hpop : ∀ g, ‖g - gStar‖ ≤ r₀ →
      weightedSquare data (populationLinearizationRemainder data gStar J g) ≤
        C * ‖g - gStar‖ ^ 4)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R)
    (batches : Fin R → ((Fin m → X) × Ω)) {r : ℝ} (_hr : 0 ≤ r) (hrr₀ : r ≤ r₀)
    (hnear : ∀ s, ‖empiricalBatchPotential data m (batches s) - gStar‖ ≤ r) :
    weightedSquare data (marginalLinearizationRemainder data gStar m R batches) ≤
      4 * (weightedSquare data (averagedEmpiricalTieResidual data m R batches) +
        iidAverage (fun batch => weightedSquare data
          (movingCellEmpiricalRemainder data gStar batch.1
            (empiricalBatchPotential data m batch))) R batches + 2 * C * r ^ 4) := by
  have hpopBatch (s : Fin R) :
      weightedSquare data (populationLinearizationRemainder data gStar J
        (empiricalBatchPotential data m (batches s))) ≤ C * r ^ 4 := by
    exact (hpop _ ((hnear s).trans hrr₀)).trans (by gcongr; exact hnear s)
  have hpopAvg : weightedSquare data (fun j => iidAverage (fun batch =>
      populationLinearizationRemainder data gStar J (empiricalBatchPotential data m batch) j)
        R batches) ≤ C * r ^ 4 := by
    apply (weightedSquare_iidAverage_le data _ R batches).trans
    unfold iidAverage
    have hRreal : 0 < (R : ℝ) := by exact_mod_cast hR
    calc
      _ ≤ (1 / (R : ℝ)) * ∑ _s : Fin R, C * r ^ 4 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s _ => hpopBatch s) (by positivity)
      _ = _ := by simp; field_simp
  have haverage := averagedEmpiricalPotential_sub_norm_le data gStar hR batches hnear
  have hpopAverage : weightedSquare data (populationLinearizationRemainder data gStar J
      (averagedEmpiricalPotential data m R batches)) ≤ C * r ^ 4 :=
    (hpop _ (haverage.trans hrr₀)).trans (by gcongr)
  rw [marginalLinearizationRemainder_decomposition data gStar J hbalanced hm hR]
  exact (weightedSquare_sub_sub_add_le data _ _ _ _).trans (by
    have hemp := weightedSquare_iidAverage_le data
      (fun batch => movingCellEmpiricalRemainder data gStar batch.1
        (empiricalBatchPotential data m batch)) R batches
    linarith)

def repetitionPotentialLocalEvent (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (m R : ℕ) (r : ℝ) :
    Set (Fin R → ((Fin m → X) × Ω)) :=
  {batches | ∀ s, ‖empiricalBatchPotential data m (batches s) - gStar‖ ≤ r}

theorem measurableSet_repetitionPotentialLocalEvent (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    {m : ℕ} (hm : 0 < m) (R : ℕ) (r : ℝ) :
    MeasurableSet (repetitionPotentialLocalEvent data gStar m R r) := by
  unfold repetitionPotentialLocalEvent
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro s
  exact (measurableSet_batchPotentialLocalEvent data hexact gStar hm r).preimage
    (measurable_pi_apply s)

theorem repetitionPotentialLocalEvent_compl_measure_le (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    {m : ℕ} (hm : 0 < m) (R : ℕ) (r : ℝ) :
    (repetitionMeasure data m R).real (repetitionPotentialLocalEvent data gStar m R r)ᶜ ≤
      (R : ℝ) * (empiricalBatchMeasure data m).real
        (batchPotentialLocalEvent data gStar m r)ᶜ := by
  let A := batchPotentialLocalEvent data gStar m r
  have hA : MeasurableSet A := measurableSet_batchPotentialLocalEvent data hexact gStar hm r
  have hevent : (repetitionPotentialLocalEvent data gStar m R r)ᶜ =
      ⋃ s : Fin R, (fun batches => batches s) ⁻¹' Aᶜ := by
    ext batches
    simp [repetitionPotentialLocalEvent, A, batchPotentialLocalEvent]
  have heval (s : Fin R) :
      (repetitionMeasure data m R).real ((fun batches => batches s) ⁻¹' Aᶜ) =
        (empiricalBatchMeasure data m).real Aᶜ := by
    simp only [measureReal_def, repetitionMeasure]
    congr 1
    exact (measurePreserving_eval
      (fun _ : Fin R => empiricalBatchMeasure data m) s).measure_preimage
      hA.compl.nullMeasurableSet
  rw [hevent]
  calc
    _ ≤ ∑ s : Fin R, (repetitionMeasure data m R).real
        ((fun batches => batches s) ⁻¹' Aᶜ) := measureReal_iUnion_fintype_le _
    _ = _ := by simp only [heval, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, A]

theorem memLp_batchMovingCellEnergy (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    {m : ℕ} (hm : 0 < m) :
    MemLp (fun batch => weightedSquare data (movingCellEmpiricalRemainder data gStar
      batch.1 (empiricalBatchPotential data m batch))) 2 (empiricalBatchMeasure data m) := by
  have hmeas (j : Fin data.n) :=
    measurable_batchMovingCellEmpiricalRemainder data hexact gStar hm j
  have hFmeas : Measurable fun batch => weightedSquare data
      (movingCellEmpiricalRemainder data gStar batch.1 (empiricalBatchPotential data m batch)) := by
    unfold weightedSquare
    fun_prop
  apply MemLp.of_bound hFmeas.aestronglyMeasurable (4 * inverseWeightSum data)
  filter_upwards [] with batch
  rw [Real.norm_eq_abs, abs_of_nonneg (weightedSquare_nonneg data _)]
  exact movingCellEmpiricalRemainder_energy_le data hm batch.1 gStar _

/-- The complete second-moment reduction. All random variables here are the
actual oracle output or actual Laguerre-mass remainders. The only remote
input is the probability that a batch potential leaves the local ball. -/
theorem linearizationEnergy_localization_bound
    (data : HELLOSDOTData X Ω) (hregular : HasHELLOSDOTRegularity data)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (hbalanced : data.populationMarginal gStar = data.b)
    {C r₀ : ℝ} (hC : 0 ≤ C) (hr₀ : 0 < r₀)
    (hpop : ∀ g, ‖g - gStar‖ ≤ r₀ →
      weightedSquare data (populationLinearizationRemainder data gStar J g) ≤
        C * ‖g - gStar‖ ^ 4)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R) {r : ℝ} (hr : 0 ≤ r) (hrr₀ : r ≤ r₀) :
    linearizationEnergy data gStar m R ≤
      4 * averagedEmpiricalTieEnergy data m R + 4 * batchMovingCellEnergy data gStar m +
        8 * C * r ^ 4 + 4 * inverseWeightSum data * (R : ℝ) *
          (empiricalBatchMeasure data m).real (batchPotentialLocalEvent data gStar m r)ᶜ := by
  let A := repetitionPotentialLocalEvent data gStar m R r
  let T := fun batches => weightedSquare data (averagedEmpiricalTieResidual data m R batches)
  let F := fun batch => weightedSquare data (movingCellEmpiricalRemainder data gStar
    batch.1 (empiricalBatchPotential data m batch))
  let K := 8 * C * r ^ 4
  let B := 4 * inverseWeightSum data
  have hB : 0 ≤ B := mul_nonneg (by norm_num) (inverseWeightSum_nonneg data)
  have hK : 0 ≤ K := by positivity
  have hA : MeasurableSet A :=
    measurableSet_repetitionPotentialLocalEvent data hexact gStar hm R r
  have hT : Integrable T (repetitionMeasure data m R) :=
    integrable_finset_sum Finset.univ fun j _ =>
      (memLp_averagedEmpiricalTieResidual data hregular hexact hm R j).integrable_sq.div_const _
  have hF : MemLp F 2 (empiricalBatchMeasure data m) :=
    memLp_batchMovingCellEnergy data hexact gStar hm
  have hAvg : Integrable (iidAverage F R) (repetitionMeasure data m R) :=
    (memLp_iidAverage (empiricalBatchMeasure data m) hF R).integrable (by norm_num)
  have hAvgmean : (∫ batches, iidAverage F R batches ∂repetitionMeasure data m R) =
      batchMovingCellEnergy data gStar m :=
    integral_iidAverage (empiricalBatchMeasure data m) hF hR
  have hsum : Integrable (fun batches => 4 * T batches + 4 * iidAverage F R batches)
      (repetitionMeasure data m R) :=
    (hT.const_mul 4).add (hAvg.const_mul 4)
  have hbase : Integrable (fun batches => 4 * T batches + 4 * iidAverage F R batches + K)
      (repetitionMeasure data m R) :=
    hsum.add (integrable_const K)
  have hInd : Integrable (Aᶜ.indicator (fun _ => B)) (repetitionMeasure data m R) :=
    (integrable_const B).indicator hA.compl
  have hpoint (batches) : weightedSquare data
      (marginalLinearizationRemainder data gStar m R batches) ≤
      4 * T batches + 4 * iidAverage F R batches + K + Aᶜ.indicator (fun _ => B) batches := by
    by_cases hb : batches ∈ A
    · rw [Set.indicator_of_notMem (not_not.mpr hb : batches ∉ Aᶜ)]
      have h := marginalLinearizationRemainder_local_energy_bound data gStar J hbalanced
        hC hr₀ hpop hm hR batches hr hrr₀ hb
      change _ ≤ 4 * T batches + 4 * iidAverage F R batches + K + 0
      dsimp only [T, F, K]
      linarith
    · rw [Set.indicator_of_mem (show batches ∈ Aᶜ from hb)]
      have hTnonneg := weightedSquare_nonneg data (averagedEmpiricalTieResidual data m R batches)
      have hAvgnonneg : 0 ≤ iidAverage F R batches :=
        mul_nonneg (by positivity) (Finset.sum_nonneg fun s _ => weightedSquare_nonneg data _)
      have h := marginalLinearizationRemainder_energy_le data gStar hbalanced hm hR batches
      change _ ≤ 4 * T batches + 4 * iidAverage F R batches + K + B
      change 0 ≤ T batches at hTnonneg
      change _ ≤ B at h
      linarith
  have h := integral_mono (integrable_linearizationSquare data hexact gStar hm R)
    (hbase.add hInd) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add hbase hInd,
    integral_add hsum (integrable_const K),
    integral_add (hT.const_mul 4) (hAvg.const_mul 4),
    integral_const_mul, integral_const_mul, integral_const, probReal_univ, one_smul,
    integral_indicator_const B hA.compl, hAvgmean] at h
  change linearizationEnergy data gStar m R ≤
    4 * averagedEmpiricalTieEnergy data m R + 4 * batchMovingCellEnergy data gStar m +
      K + (repetitionMeasure data m R).real Aᶜ * B at h
  have htail := repetitionPotentialLocalEvent_compl_measure_le data hexact gStar hm R r
  have htailB := mul_le_mul_of_nonneg_right htail hB
  dsimp only [A, B, K] at h htailB
  nlinarith

theorem batchMovingCellEnergy_coordinateGrid_bound (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (hexact : HasExactEmpiricalOTSolves data) :
    ∃ C₁ C₂ : ℝ, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∀ (gStar : Fin data.n → ℝ) {m : ℕ}, 0 < m →
        ∀ {r δ : ℝ}, 0 < r → 0 < δ →
          batchMovingCellEnergy data gStar m ≤
            C₁ * (2 * r / δ + 2) ^ data.n * (r + 3 * δ) / (m : ℝ) + C₂ * δ ^ 2 +
              4 * inverseWeightSum data * (empiricalBatchMeasure data m).real
                (batchPotentialLocalEvent data gStar m r)ᶜ := by
  obtain ⟨L, hL⟩ := populationMarginal_lipschitz data hregular
  obtain ⟨C, hC, hgridIntegral⟩ := gridEndpointEnergy_integral_le data hregular
  refine ⟨2 * C, 32 * (L : ℝ) ^ 2 * inverseWeightSum data, by positivity,
    mul_nonneg (by positivity) (inverseWeightSum_nonneg data), ?_⟩
  intro gStar m hm r δ hr hδ
  let grid := coordinateGrid gStar r δ
  have hgrid := hgridIntegral gStar hm grid (by linarith : 0 < r + δ) hδ.le
    (fun g hg => coordinateGrid_norm_le gStar hr.le hδ hg)
  have hpoint := batchMovingCellEnergy_finiteGrid_bound data hexact L hL gStar hm
    grid r hδ.le (coordinateGrid_covers gStar hr.le hδ)
  have hcard := coordinateGrid_card_real_le gStar hr.le hδ
  have hterm : (grid.card : ℝ) * C * (r + δ + 2 * δ) / (m : ℝ) ≤
      (2 * r / δ + 2) ^ data.n * C * (r + δ + 2 * δ) / (m : ℝ) := by
    gcongr
  have h := hpoint.trans (add_le_add
    (add_le_add (mul_le_mul_of_nonneg_left (hgrid.trans hterm) (by norm_num)) le_rfl) le_rfl)
  change batchMovingCellEnergy data gStar m ≤
    2 * ((2 * r / δ + 2) ^ data.n * C * (r + δ + 2 * δ) / (m : ℝ)) +
      32 * (L : ℝ) ^ 2 * δ ^ 2 * inverseWeightSum data +
        4 * inverseWeightSum data * (empiricalBatchMeasure data m).real
          (batchPotentialLocalEvent data gStar m r)ᶜ at h
  convert h using 1
  ring

end DualGuided2026
