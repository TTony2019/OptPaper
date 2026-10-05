import TheoremLib.Dual_guided_2026.SDOT

/-!
# Categorical fluctuations in Appendix F

This file proves the exact second-moment identity (40) for the actual
independent sampling law. It does not use `theorem_3_1`.
-/

namespace DualGuided2026

open MeasureTheory
open scoped BigOperators

section IID

variable {Y : Type*} [MeasurableSpace Y] (μ : Measure Y) [IsProbabilityMeasure μ]

noncomputable def iidAverage (f : Y → ℝ) (k : ℕ) (samples : Fin k → Y) : ℝ :=
  (1 / (k : ℝ)) * ∑ i, f (samples i)

theorem memLp_iidAverage {f : Y → ℝ} (hf : MemLp f 2 μ) (k : ℕ) :
    MemLp (iidAverage f k) 2 (Measure.pi fun _ : Fin k => μ) := by
  apply MemLp.const_mul
  exact memLp_finset_sum Finset.univ fun i _ =>
    hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin k => μ) i)

theorem integral_iidAverage {f : Y → ℝ} (hf : MemLp f 2 μ) {k : ℕ} (hk : 0 < k) :
    (∫ samples, iidAverage f k samples ∂Measure.pi fun _ : Fin k => μ) = ∫ y, f y ∂μ := by
  have hi (i : Fin k) : Integrable (fun samples : Fin k → Y => f (samples i))
      (Measure.pi fun _ : Fin k => μ) :=
    (hf.comp_measurePreserving (measurePreserving_eval (fun _ : Fin k => μ) i)).integrable
      (by norm_num)
  simp only [iidAverage, integral_const_mul]
  rw [integral_finset_sum Finset.univ (fun i _ => hi i)]
  have hcomp (i : Fin k) :
      (∫ samples : Fin k → Y, f (samples i) ∂Measure.pi fun _ : Fin k => μ) =
        ∫ y, f y ∂μ :=
    integral_comp_eval (μ := fun _ : Fin k => μ) (i := i) hf.aestronglyMeasurable
  simp only [hcomp, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

theorem variance_iidAverage {f : Y → ℝ} (hf : MemLp f 2 μ) {k : ℕ} (hk : 0 < k) :
    ProbabilityTheory.variance (iidAverage f k) (Measure.pi fun _ : Fin k => μ) =
      ProbabilityTheory.variance f μ / k := by
  have hsum := ProbabilityTheory.variance_sum_pi
    (μ := fun _ : Fin k => μ) (X := fun _ : Fin k => f) (fun _ => hf)
  have hfun : (∑ i : Fin k, fun samples : Fin k → Y => f (samples i)) =
      (fun samples => ∑ i, f (samples i)) := by
    funext samples
    simp
  rw [hfun] at hsum
  have hsum' :
      ProbabilityTheory.variance (fun samples : Fin k → Y => ∑ i, f (samples i))
        (Measure.pi fun _ : Fin k => μ) = (k : ℝ) * ProbabilityTheory.variance f μ := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum
  unfold iidAverage
  rw [ProbabilityTheory.variance_const_mul, hsum']
  have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  field_simp

end IID

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

theorem measurableSet_laguerreCell (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j : Fin data.n) : MeasurableSet (laguerreCell data g j) :=
  (measurableSet_jointLaguerreCell data j).preimage (measurable_const.prodMk measurable_id)

noncomputable def cellIndicator (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j : Fin data.n) : X → ℝ :=
  (laguerreCell data g j).indicator (fun _ => 1)

theorem memLp_cellIndicator (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j : Fin data.n) : MemLp (cellIndicator data g j) 2 data.sourceMeasure :=
  (memLp_const (1 : ℝ)).indicator (measurableSet_laguerreCell data g j)

theorem integral_cellIndicator (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j : Fin data.n) :
    (∫ x, cellIndicator data g j x ∂data.sourceMeasure) = data.populationMarginal g j := by
  exact integral_indicator_one (measurableSet_laguerreCell data g j)

theorem cellIndicator_sq (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j : Fin data.n) (x : X) :
    (cellIndicator data g j x) ^ 2 = cellIndicator data g j x := by
  classical
  by_cases h : x ∈ laguerreCell data g j <;> simp [cellIndicator, h]

theorem variance_cellIndicator (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j : Fin data.n) :
    ProbabilityTheory.variance (cellIndicator data g j) data.sourceMeasure =
      data.populationMarginal g j * (1 - data.populationMarginal g j) := by
  rw [ProbabilityTheory.variance_eq_sub (memLp_cellIndicator data g j)]
  simp only [Pi.pow_apply, cellIndicator_sq, integral_cellIndicator]
  ring

noncomputable def centeredCellIndicator (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j : Fin data.n) (x : X) : ℝ :=
  cellIndicator data g j x - data.populationMarginal g j

theorem memLp_centeredCellIndicator (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j : Fin data.n) :
    MemLp (centeredCellIndicator data g j) 2 data.sourceMeasure :=
  (memLp_cellIndicator data g j).sub (memLp_const _)

theorem integral_centeredCellIndicator (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j : Fin data.n) :
    (∫ x, centeredCellIndicator data g j x ∂data.sourceMeasure) = 0 := by
  unfold centeredCellIndicator
  rw [integral_sub ((memLp_cellIndicator data g j).integrable (by norm_num))
    (integrable_const _), integral_cellIndicator]
  simp

theorem variance_centeredCellIndicator (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j : Fin data.n) :
    ProbabilityTheory.variance (centeredCellIndicator data g j) data.sourceMeasure =
      data.populationMarginal g j * (1 - data.populationMarginal g j) := by
  unfold centeredCellIndicator
  rw [ProbabilityTheory.variance_sub_const
    (memLp_cellIndicator data g j).aestronglyMeasurable]
  exact variance_cellIndicator data g j

/-- `ζₘ = (Pₘ - P)a(·; g)` in a single source batch. -/
noncomputable def sourceCategoricalFluctuation (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (m : ℕ) (samples : Fin m → X) (j : Fin data.n) : ℝ :=
  iidAverage (centeredCellIndicator data g j) m samples

noncomputable def batchCategoricalFluctuation (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (m : ℕ) (batch : (Fin m → X) × Ω) (j : Fin data.n) : ℝ :=
  sourceCategoricalFluctuation data g m batch.1 j

theorem memLp_batchCategoricalFluctuation (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (m : ℕ) (j : Fin data.n) :
    MemLp (fun batch => batchCategoricalFluctuation data g m batch j) 2
      (empiricalBatchMeasure data m) :=
  (memLp_iidAverage data.sourceMeasure (memLp_centeredCellIndicator data g j) m).comp_fst
    (data.solverMeasure m)

theorem integral_batchCategoricalFluctuation (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) {m : ℕ} (hm : 0 < m) (j : Fin data.n) :
    (∫ batch, batchCategoricalFluctuation data g m batch j ∂empiricalBatchMeasure data m) =
      0 := by
  unfold batchCategoricalFluctuation empiricalBatchMeasure
  rw [integral_fun_fst (fun samples => sourceCategoricalFluctuation data g m samples j)]
  simp only [sourceCategoricalFluctuation, sourceBatchMeasure,
    integral_iidAverage data.sourceMeasure (memLp_centeredCellIndicator data g j) hm,
    integral_centeredCellIndicator, smul_zero]

theorem variance_batchCategoricalFluctuation (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) {m : ℕ} (hm : 0 < m) (j : Fin data.n) :
    ProbabilityTheory.variance (fun batch => batchCategoricalFluctuation data g m batch j)
      (empiricalBatchMeasure data m) =
      data.populationMarginal g j * (1 - data.populationMarginal g j) / m := by
  change ProbabilityTheory.variance
    (fun batch => iidAverage (centeredCellIndicator data g j) m batch.1)
    ((sourceBatchMeasure data m).prod (data.solverMeasure m)) = _
  rw [sourceBatchMeasure]
  rw [measurePreserving_fst.variance_fun_comp
    (memLp_iidAverage data.sourceMeasure (memLp_centeredCellIndicator data g j) m).aemeasurable]
  rw [variance_iidAverage data.sourceMeasure (memLp_centeredCellIndicator data g j) hm,
    variance_centeredCellIndicator]

/-- `ζ̄ₘ,ᴿ`, the averaged categorical fluctuation in Appendix F (38). -/
noncomputable def averagedCategoricalFluctuation (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (m R : ℕ)
    (batches : Fin R → ((Fin m → X) × Ω)) (j : Fin data.n) : ℝ :=
  iidAverage (fun batch => batchCategoricalFluctuation data g m batch j) R batches

theorem memLp_averagedCategoricalFluctuation (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (m R : ℕ) (j : Fin data.n) :
    MemLp (fun batches => averagedCategoricalFluctuation data g m R batches j) 2
      (repetitionMeasure data m R) :=
  memLp_iidAverage (empiricalBatchMeasure data m)
    (memLp_batchCategoricalFluctuation data g m j) R

theorem integral_averagedCategoricalFluctuation_sq (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) {m R : ℕ} (hm : 0 < m) (hR : 0 < R) (j : Fin data.n) :
    (∫ batches, (averagedCategoricalFluctuation data g m R batches j) ^ 2
      ∂repetitionMeasure data m R) =
      data.populationMarginal g j * (1 - data.populationMarginal g j) / ((m : ℝ) * R) := by
  have hzero : (∫ batches, averagedCategoricalFluctuation data g m R batches j
      ∂repetitionMeasure data m R) = 0 := by
    unfold averagedCategoricalFluctuation repetitionMeasure
    rw [integral_iidAverage (empiricalBatchMeasure data m)
        (memLp_batchCategoricalFluctuation data g m j) hR,
      integral_batchCategoricalFluctuation data g hm]
  have hv := ProbabilityTheory.variance_eq_sub
    (memLp_averagedCategoricalFluctuation data g m R j)
  simp only [Pi.pow_apply, hzero, zero_pow (show (2 : ℕ) ≠ 0 by decide), sub_zero] at hv
  rw [← hv]
  change ProbabilityTheory.variance
    (iidAverage (fun batch => batchCategoricalFluctuation data g m batch j) R)
    (Measure.pi fun _ : Fin R => empiricalBatchMeasure data m) = _
  rw [variance_iidAverage (empiricalBatchMeasure data m)
    (memLp_batchCategoricalFluctuation data g m j) hR,
    variance_batchCategoricalFluctuation data g hm, div_div]

/-- Proposition F.4 (40), under the population balance equation. -/
theorem categorical_second_moment (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (hbalanced : data.populationMarginal gStar = data.b)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    (∫ batches, ∑ j, (averagedCategoricalFluctuation data gStar m R batches j) ^ 2 / data.b j
      ∂repetitionMeasure data m R) = helloSDOTMeanLeading data.n m R := by
  rw [integral_finset_sum Finset.univ (fun j _ =>
    (memLp_averagedCategoricalFluctuation data gStar m R j).integrable_sq.div_const _)]
  simp only [integral_div, integral_averagedCategoricalFluctuation_sq data gStar hm hR,
    hbalanced, helloSDOTMeanLeading]
  have hmR : (m : ℝ) * R ≠ 0 := mul_ne_zero (by exact_mod_cast hm.ne')
    (by exact_mod_cast hR.ne')
  calc
    ∑ j, data.b j * (1 - data.b j) / ((m : ℝ) * R) / data.b j =
        ∑ j, (1 - data.b j) / ((m : ℝ) * R) := by
      apply Finset.sum_congr rfl
      intro j _
      field_simp [(data.b_pos j).ne', hmR]
    _ = ((data.n : ℝ) - 1) / ((m : ℝ) * R) := by
      rw [← Finset.sum_div, Finset.sum_sub_distrib, data.b_sum]
      simp

end DualGuided2026
