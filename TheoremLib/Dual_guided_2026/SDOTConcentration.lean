import TheoremLib.Dual_guided_2026.SDOTSemidualMinimum
import Mathlib.Probability.Moments.SubGaussian

/-!
# Concentration of bounded iid semidual contrasts

Single-source semidual differences are bounded by the distance between
their potentials, so Hoeffding concentration applies without bounded
support for the source measure.
-/

namespace DualGuided2026

open MeasureTheory
open scoped BigOperators ENNReal NNReal

theorem measure_iidAverage_deviation_ge_le {Y : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (f : Y → ℝ) (hf : Measurable f)
    {C : ℝ} (hC : 0 < C) (hbound : ∀ y, |f y| ≤ C)
    {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 ≤ δ) :
    (Measure.pi (fun _ : Fin m => μ)).real
      {samples | δ ≤ iidAverage f m samples - ∫ y, f y ∂μ} ≤
        Real.exp (-(m : ℝ) * δ ^ 2 / (2 * C ^ 2)) := by
  let c : ℝ≥0 := ⟨C ^ 2, sq_nonneg C⟩
  have hproxy : ((‖C - -C‖₊ / 2) ^ 2 : ℝ≥0) = c := by
    apply NNReal.eq
    change (‖C - -C‖ / 2) ^ 2 = C ^ 2
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith : 0 ≤ C - -C)]
    ring
  have hsub : ProbabilityTheory.HasSubgaussianMGF
      (fun y => f y - ∫ z, f z ∂μ) c μ := by
    rw [← hproxy]
    exact ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc hf.aemeasurable
      (Filter.Eventually.of_forall (fun y => abs_le.mp (hbound y)))
  have hind := ProbabilityTheory.iIndepFun_pi (μ := fun _ : Fin m => μ)
    (X := fun _ y => f y - ∫ z, f z ∂μ)
    (fun _ => (hf.sub_const _).aemeasurable)
  have hcoord (k : Fin m) : ProbabilityTheory.HasSubgaussianMGF
      (fun samples : Fin m → Y => f (samples k) - ∫ y, f y ∂μ) c
      (Measure.pi (fun _ : Fin m => μ)) := by
    have hmap : ProbabilityTheory.HasSubgaussianMGF
        (fun y => f y - ∫ z, f z ∂μ) c
        ((Measure.pi (fun _ : Fin m => μ)).map (fun samples => samples k)) := by
      rw [(measurePreserving_eval (fun _ : Fin m => μ) k).map_eq]
      exact hsub
    exact ProbabilityTheory.HasSubgaussianMGF.of_map
      (μ := Measure.pi (fun _ : Fin m => μ))
      (Y := fun samples : Fin m → Y => samples k)
      (X := fun y => f y - ∫ z, f z ∂μ)
      (measurable_pi_apply k).aemeasurable hmap
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have htail := ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := Finset.univ) (c := fun _ => c) (fun k _ => hcoord k)
    (show 0 ≤ (m : ℝ) * δ from mul_nonneg hmreal.le hδ)
  have hevent : {samples : Fin m → Y | δ ≤ iidAverage f m samples - ∫ y, f y ∂μ} =
      {samples | (m : ℝ) * δ ≤ ∑ k, (f (samples k) - ∫ y, f y ∂μ)} := by
    ext samples
    simp only [Set.mem_setOf_eq, iidAverage, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    constructor <;> intro h
    · have h' := mul_le_mul_of_nonneg_left h hmreal.le
      field_simp at h'
      nlinarith
    · apply (mul_le_mul_iff_right₀ hmreal).mp
      field_simp
      nlinarith
  rw [hevent]
  refine htail.trans_eq ?_
  congr 1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    NNReal.coe_mul, NNReal.coe_natCast]
  change -((m : ℝ) * δ) ^ 2 / (2 * ((m : ℝ) * C ^ 2)) =
    -(m : ℝ) * δ ^ 2 / (2 * C ^ 2)
  field_simp [hmreal.ne', hC.ne']

theorem measure_finite_iidAverage_deviation_ge_le {Y ι : Type*} [MeasurableSpace Y]
    (μ : Measure Y) [IsProbabilityMeasure μ] (S : Finset ι) (f : ι → Y → ℝ)
    (hf : ∀ i ∈ S, Measurable (f i)) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ i ∈ S, ∀ y, |f i y| ≤ C)
    {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 ≤ δ) :
    (Measure.pi (fun _ : Fin m => μ)).real
      {samples | ∃ i ∈ S, δ ≤ iidAverage (f i) m samples - ∫ y, f i y ∂μ} ≤
        (S.card : ℝ) * Real.exp (-(m : ℝ) * δ ^ 2 / (2 * C ^ 2)) := by
  let E : ι → Set (Fin m → Y) := fun i =>
    {samples | δ ≤ iidAverage (f i) m samples - ∫ y, f i y ∂μ}
  have hevent : {samples : Fin m → Y |
      ∃ i ∈ S, δ ≤ iidAverage (f i) m samples - ∫ y, f i y ∂μ} = ⋃ i ∈ S, E i := by
    ext samples
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E, exists_prop]
  rw [hevent]
  calc
    _ ≤ ∑ i ∈ S, (Measure.pi (fun _ : Fin m => μ)).real (E i) :=
      measureReal_biUnion_finset_le S E
    _ ≤ ∑ _ ∈ S, Real.exp (-(m : ℝ) * δ ^ 2 / (2 * C ^ 2)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact measure_iidAverage_deviation_ge_le μ (f i) (hf i hi) hC (hbound i hi) hm hδ
    _ = _ := by simp

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

theorem empiricalSemiDualObjective_sub_eq (data : HELLOSDOTData X Ω)
    {m : ℕ} (samples : Fin m → X) (g h : Fin data.n → ℝ) :
    empiricalSemiDualObjective data samples g - empiricalSemiDualObjective data samples h =
      (∑ j, data.b j * (g j - h j)) +
        iidAverage (fun x => sInf (Set.range fun j => sdCost data x j - g j) -
          sInf (Set.range fun j => sdCost data x j - h j)) m samples := by
  simp only [empiricalSemiDualObjective, iidAverage, mul_sub, Finset.sum_sub_distrib]
  ring

/-- Hoeffding's estimate for the fixed-potential contrast entering a finite
net localization proof. -/
theorem measure_semidualContrast_deviation_ge_le (data : HELLOSDOTData X Ω)
    (g h : Fin data.n → ℝ) {C : ℝ} (hC : 0 < C) (hgh : ‖g - h‖ ≤ C)
    {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 ≤ δ) :
    (sourceBatchMeasure data m).real {samples |
      δ ≤ iidAverage (fun x => sInf (Set.range fun j => sdCost data x j - g j) -
        sInf (Set.range fun j => sdCost data x j - h j)) m samples -
          ∫ x, (sInf (Set.range fun j => sdCost data x j - g j) -
            sInf (Set.range fun j => sdCost data x j - h j)) ∂data.sourceMeasure} ≤
              Real.exp (-(m : ℝ) * δ ^ 2 / (2 * C ^ 2)) := by
  apply measure_iidAverage_deviation_ge_le data.sourceMeasure _
    ((measurable_semiDualMinimum data g).sub (measurable_semiDualMinimum data h)) hC _ hm hδ
  intro x
  exact (semiDualMinimum_sub_abs_le_norm data x g h).trans hgh

theorem measure_finite_semidualContrast_deviation_ge_le (data : HELLOSDOTData X Ω)
    (S : Finset (Fin data.n → ℝ)) (h : Fin data.n → ℝ)
    {C : ℝ} (hC : 0 < C) (hbound : ∀ g ∈ S, ‖g - h‖ ≤ C)
    {m : ℕ} (hm : 0 < m) {δ : ℝ} (hδ : 0 ≤ δ) :
    (sourceBatchMeasure data m).real {samples | ∃ g ∈ S,
      δ ≤ iidAverage (fun x => sInf (Set.range fun j => sdCost data x j - g j) -
        sInf (Set.range fun j => sdCost data x j - h j)) m samples -
          ∫ x, (sInf (Set.range fun j => sdCost data x j - g j) -
            sInf (Set.range fun j => sdCost data x j - h j)) ∂data.sourceMeasure} ≤
              (S.card : ℝ) * Real.exp (-(m : ℝ) * δ ^ 2 / (2 * C ^ 2)) := by
  apply measure_finite_iidAverage_deviation_ge_le data.sourceMeasure S _ _ hC _ hm hδ
  · intro g _
    exact (measurable_semiDualMinimum data g).sub (measurable_semiDualMinimum data h)
  · intro g hg x
    exact (semiDualMinimum_sub_abs_le_norm data x g h).trans (hbound g hg)

end DualGuided2026
