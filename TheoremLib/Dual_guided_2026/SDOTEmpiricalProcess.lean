import TheoremLib.Dual_guided_2026.SDOTLinearization

/-!
# Fixed-potential fluctuations and Laguerre brackets

The second-moment bound below is for deterministic potentials. The brackets
are pointwise statements, so they also apply to a potential chosen from the
sample, and reduce a uniform empirical-process bound to a finite grid.
-/

namespace DualGuided2026

open MeasureTheory
open scoped BigOperators

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

theorem movingCellEmpiricalRemainder_eq_centeredAverage (data : HELLOSDOTData X Ω)
    (g h : Fin data.n → ℝ) {m : ℕ} (samples : Fin m → X)
    (j : Fin data.n) :
    movingCellEmpiricalRemainder data g samples h j =
      iidAverage (fun x => cellIndicator data h j x - cellIndicator data g j x) m samples -
        ∫ x, cellIndicator data h j x - cellIndicator data g j x ∂data.sourceMeasure := by
  have hg := (memLp_cellIndicator data g j).integrable (by norm_num)
  have hh := (memLp_cellIndicator data h j).integrable (by norm_num)
  rw [integral_sub hh hg, integral_cellIndicator, integral_cellIndicator]
  simp only [movingCellEmpiricalRemainder, empiricalCellMass, iidAverage,
    Pi.sub_apply, Finset.sum_sub_distrib]
  ring

theorem memLp_fixedMovingCellEmpiricalRemainder (data : HELLOSDOTData X Ω)
    (g h : Fin data.n → ℝ) {m : ℕ} (j : Fin data.n) :
    MemLp (fun samples => movingCellEmpiricalRemainder data g samples h j) 2
      (sourceBatchMeasure data m) := by
  simp_rw [movingCellEmpiricalRemainder_eq_centeredAverage data g h]
  exact (memLp_iidAverage data.sourceMeasure
    ((memLp_cellIndicator data h j).sub (memLp_cellIndicator data g j)) m).sub (memLp_const _)

theorem integral_fixedMovingCellEmpiricalRemainder_sq (data : HELLOSDOTData X Ω)
    (g h : Fin data.n → ℝ) {m : ℕ} (hm : 0 < m) (j : Fin data.n) :
    (∫ samples, (movingCellEmpiricalRemainder data g samples h j) ^ 2
      ∂sourceBatchMeasure data m) =
        ProbabilityTheory.variance
          (fun x => cellIndicator data h j x - cellIndicator data g j x) data.sourceMeasure /
            (m : ℝ) := by
  let f := fun x => cellIndicator data h j x - cellIndicator data g j x
  have hf : MemLp f 2 data.sourceMeasure :=
    (memLp_cellIndicator data h j).sub (memLp_cellIndicator data g j)
  have hmean : (∫ samples, movingCellEmpiricalRemainder data g samples h j
      ∂sourceBatchMeasure data m) = 0 := by
    simp_rw [movingCellEmpiricalRemainder_eq_centeredAverage data g h]
    change (∫ samples, iidAverage f m samples - ∫ x, f x ∂data.sourceMeasure
      ∂Measure.pi (fun _ : Fin m => data.sourceMeasure)) = 0
    rw [integral_sub ((memLp_iidAverage data.sourceMeasure hf m).integrable (by norm_num))
      (integrable_const _), integral_iidAverage data.sourceMeasure hf hm]
    simp
  have hv := ProbabilityTheory.variance_eq_sub
    (memLp_fixedMovingCellEmpiricalRemainder data g h (m := m) j)
  simp only [Pi.pow_apply, hmean, zero_pow (show (2 : ℕ) ≠ 0 by decide), sub_zero] at hv
  rw [← hv]
  simp_rw [movingCellEmpiricalRemainder_eq_centeredAverage data g h]
  change ProbabilityTheory.variance
    (fun samples => iidAverage f m samples - ∫ x, f x ∂data.sourceMeasure)
    (Measure.pi fun _ : Fin m => data.sourceMeasure) = _
  rw [ProbabilityTheory.variance_sub_const
    (memLp_iidAverage data.sourceMeasure hf m).aestronglyMeasurable,
    variance_iidAverage data.sourceMeasure hf hm]

theorem variance_cellIndicator_difference_le_envelope (data : HELLOSDOTData X Ω)
    (g h : Fin data.n → ℝ) (r : ℝ) (hclose : ∀ j, |h j - g j| ≤ r) (j : Fin data.n) :
    ProbabilityTheory.variance (fun x => cellIndicator data h j x - cellIndicator data g j x)
      data.sourceMeasure ≤ (data.sourceMeasure (movingCellEnvelope data g r)).toReal := by
  classical
  have hf := (memLp_cellIndicator data h j).sub (memLp_cellIndicator data g j)
  have hB := measurableSet_movingCellEnvelope data g r
  have hpoint (x : X) : (cellIndicator data h j x - cellIndicator data g j x) ^ 2 ≤
      (movingCellEnvelope data g r).indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ movingCellEnvelope data g r
    · rw [Set.indicator_of_mem hx]
      simp only [cellIndicator, Set.indicator_apply]
      split_ifs <;> norm_num
    · rw [cellIndicator_eq_off_envelope data g h r hclose x hx,
        sub_self, zero_pow (show (2 : ℕ) ≠ 0 by decide), Set.indicator_of_notMem hx]
  have hsq : (∫ x, (cellIndicator data h j x - cellIndicator data g j x) ^ 2
      ∂data.sourceMeasure) ≤ (data.sourceMeasure (movingCellEnvelope data g r)).toReal := by
    calc
      _ ≤ ∫ x, (movingCellEnvelope data g r).indicator (fun _ => (1 : ℝ)) x
          ∂data.sourceMeasure :=
        integral_mono hf.integrable_sq ((integrable_const (1 : ℝ)).indicator hB) hpoint
      _ = _ := integral_indicator_one hB
  change ProbabilityTheory.variance (cellIndicator data h j - cellIndicator data g j)
    data.sourceMeasure ≤ _
  rw [ProbabilityTheory.variance_eq_sub hf]
  simp only [Pi.pow_apply]
  exact (sub_le_self _ (sq_nonneg _)).trans hsq

/-- The local second-moment estimate for any fixed potential in the ball.
The constant is uniform in both deterministic potentials and the batch size.
Passing to a sample-dependent potential additionally needs a supremum bound. -/
theorem fixedMovingCell_second_moment_le (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g h : Fin data.n → ℝ) (r : ℝ), 0 < r →
        (∀ j, |h j - g j| ≤ r) → ∀ {m : ℕ}, 0 < m →
          (∫ samples, weightedSquare data (movingCellEmpiricalRemainder data g samples h)
            ∂sourceBatchMeasure data m) ≤ C * r / (m : ℝ) := by
  obtain ⟨C, hC, hmass⟩ := movingCellEnvelope_measure_le data hregular
  let B := ∑ j, 1 / data.b j
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ => div_nonneg (by norm_num) (data.b_pos j).le
  refine ⟨C * B, mul_nonneg hC hB, ?_⟩
  intro g h r hr hclose m hm
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmassReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmass g r hr)
  rw [ENNReal.toReal_ofReal (mul_nonneg hC hr.le)] at hmassReal
  have hv (j : Fin data.n) := (variance_cellIndicator_difference_le_envelope
    data g h r hclose j).trans hmassReal
  unfold weightedSquare
  rw [integral_finset_sum Finset.univ (fun j _ =>
    (memLp_fixedMovingCellEmpiricalRemainder data g h j).integrable_sq.div_const _)]
  simp only [integral_div, integral_fixedMovingCellEmpiricalRemainder_sq data g h hm]
  calc
    (∑ j, ProbabilityTheory.variance
        (fun x => cellIndicator data h j x - cellIndicator data g j x) data.sourceMeasure /
          (m : ℝ) / data.b j) ≤ ∑ j, (C * r / (m : ℝ)) / data.b j :=
      Finset.sum_le_sum fun j _ => div_le_div_of_nonneg_right
        (div_le_div_of_nonneg_right (hv j) hmreal.le) (data.b_pos j).le
    _ = C * B * r / (m : ℝ) := by
      simp only [B, div_eq_mul_inv, one_mul, ← Finset.mul_sum]
      ring

theorem laguerreCell_mono_comparisons (data : HELLOSDOTData X Ω)
    (g h : Fin data.n → ℝ) (j : Fin data.n)
    (hcomp : ∀ k, g j - g k ≤ h j - h k) :
    laguerreCell data g j ⊆ laguerreCell data h j := by
  intro x hx
  constructor
  · intro k
    have := hx.1 k
    have := hcomp k
    linarith
  · intro k hk
    have := hx.2 k hk
    have := hcomp k
    linarith

theorem cellIndicator_mono_comparisons (data : HELLOSDOTData X Ω)
    (g h : Fin data.n → ℝ) (j : Fin data.n)
    (hcomp : ∀ k, g j - g k ≤ h j - h k) (x : X) :
    cellIndicator data g j x ≤ cellIndicator data h j x := by
  classical
  have hsub := laguerreCell_mono_comparisons data g h j hcomp
  by_cases hx : x ∈ laguerreCell data g j
  · simp [cellIndicator, hx, hsub hx]
  · simp only [cellIndicator, Set.indicator_of_notMem hx, Set.indicator_apply]
    split_ifs <;> norm_num

theorem empiricalCellMass_mono_comparisons (data : HELLOSDOTData X Ω)
    {m : ℕ} (samples : Fin m → X) (g h : Fin data.n → ℝ) (j : Fin data.n)
    (hcomp : ∀ k, g j - g k ≤ h j - h k) :
    empiricalCellMass data samples g j ≤ empiricalCellMass data samples h j := by
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum fun k _ => cellIndicator_mono_comparisons data g h j hcomp (samples k))
    (by positivity)

theorem populationMarginal_mono_comparisons (data : HELLOSDOTData X Ω)
    (g h : Fin data.n → ℝ) (j : Fin data.n)
    (hcomp : ∀ k, g j - g k ≤ h j - h k) :
    data.populationMarginal g j ≤ data.populationMarginal h j :=
  ENNReal.toReal_mono (measure_ne_top data.sourceMeasure _)
    (measure_mono (laguerreCell_mono_comparisons data g h j hcomp))

def shiftPotentialCoordinate {n : ℕ} (g : Fin n → ℝ) (j : Fin n) (t : ℝ) : Fin n → ℝ :=
  Function.update g j (g j + t)

theorem potential_comparison_brackets (data : HELLOSDOTData X Ω)
    (g h : Fin data.n → ℝ) (δ : ℝ) (hclose : ∀ k, |h k - g k| ≤ δ) (j : Fin data.n) :
    (∀ k, shiftPotentialCoordinate g j (-2 * δ) j - shiftPotentialCoordinate g j (-2 * δ) k ≤
      h j - h k) ∧
    (∀ k, h j - h k ≤
      shiftPotentialCoordinate g j (2 * δ) j - shiftPotentialCoordinate g j (2 * δ) k) := by
  classical
  constructor <;> intro k
  all_goals
    by_cases hk : k = j
    · subst k
      simp
    · have hjclose := abs_le.mp (hclose j)
      have hkclose := abs_le.mp (hclose k)
      simp only [shiftPotentialCoordinate, Function.update_self, Function.update_of_ne hk]
      linarith

/-- Pointwise finite-grid bracketing for the empirical process. In particular,
`h` may be the output of the empirical oracle on `samples`. -/
theorem movingCellEmpiricalRemainder_bracket (data : HELLOSDOTData X Ω)
    {m : ℕ} (samples : Fin m → X) (gStar g h : Fin data.n → ℝ) (δ : ℝ)
    (hclose : ∀ k, |h k - g k| ≤ δ) (j : Fin data.n) :
    |movingCellEmpiricalRemainder data gStar samples h j| ≤
      max |movingCellEmpiricalRemainder data gStar samples
          (shiftPotentialCoordinate g j (-2 * δ)) j|
        |movingCellEmpiricalRemainder data gStar samples
          (shiftPotentialCoordinate g j (2 * δ)) j| +
      (data.populationMarginal (shiftPotentialCoordinate g j (2 * δ)) j -
        data.populationMarginal (shiftPotentialCoordinate g j (-2 * δ)) j) := by
  have hc := potential_comparison_brackets data g h δ hclose j
  have hmassLo := empiricalCellMass_mono_comparisons data samples _ h j hc.1
  have hmassHi := empiricalCellMass_mono_comparisons data samples h _ j hc.2
  have hpopLo := populationMarginal_mono_comparisons data _ h j hc.1
  have hpopHi := populationMarginal_mono_comparisons data h _ j hc.2
  have hlo := (neg_abs_le
    (movingCellEmpiricalRemainder data gStar samples (shiftPotentialCoordinate g j (-2 * δ)) j))
  have hhi := (le_abs_self
    (movingCellEmpiricalRemainder data gStar samples (shiftPotentialCoordinate g j (2 * δ)) j))
  have hmaxLo := le_max_left
    |movingCellEmpiricalRemainder data gStar samples (shiftPotentialCoordinate g j (-2 * δ)) j|
    |movingCellEmpiricalRemainder data gStar samples (shiftPotentialCoordinate g j (2 * δ)) j|
  have hmaxHi := le_max_right
    |movingCellEmpiricalRemainder data gStar samples (shiftPotentialCoordinate g j (-2 * δ)) j|
    |movingCellEmpiricalRemainder data gStar samples (shiftPotentialCoordinate g j (2 * δ)) j|
  apply abs_le.mpr
  simp only [movingCellEmpiricalRemainder, Pi.sub_apply] at hlo hhi hmaxLo hmaxHi ⊢
  constructor <;> linarith

theorem populationMarginal_coordinate_bracket_gap (data : HELLOSDOTData X Ω)
    (C : NNReal) (hC : LipschitzWith C data.populationMarginal)
    (g : Fin data.n → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (j : Fin data.n) :
    data.populationMarginal (shiftPotentialCoordinate g j (2 * δ)) j -
      data.populationMarginal (shiftPotentialCoordinate g j (-2 * δ)) j ≤ 4 * C * δ := by
  classical
  have hnorm : ‖shiftPotentialCoordinate g j (2 * δ) -
      shiftPotentialCoordinate g j (-2 * δ)‖ ≤ 4 * δ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro k
    by_cases hk : k = j
    · subst k
      simp only [Pi.sub_apply, shiftPotentialCoordinate, Function.update_self, Real.norm_eq_abs]
      rw [show g j + 2 * δ - (g j + -2 * δ) = 4 * δ by ring, abs_of_nonneg (by positivity)]
    · simp only [Pi.sub_apply, shiftPotentialCoordinate, Function.update_of_ne hk, sub_self,
        norm_zero]
      positivity
  have hdist := hC.dist_le_mul (shiftPotentialCoordinate g j (2 * δ))
    (shiftPotentialCoordinate g j (-2 * δ))
  simp only [dist_eq_norm] at hdist
  have hcoord := norm_le_pi_norm
    (data.populationMarginal (shiftPotentialCoordinate g j (2 * δ)) -
      data.populationMarginal (shiftPotentialCoordinate g j (-2 * δ))) j
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hcoord
  calc
    _ ≤ |data.populationMarginal (shiftPotentialCoordinate g j (2 * δ)) j -
      data.populationMarginal (shiftPotentialCoordinate g j (-2 * δ)) j| := le_abs_self _
    _ ≤ C * ‖shiftPotentialCoordinate g j (2 * δ) -
      shiftPotentialCoordinate g j (-2 * δ)‖ := hcoord.trans hdist
    _ ≤ C * (4 * δ) := mul_le_mul_of_nonneg_left hnorm C.coe_nonneg
    _ = 4 * C * δ := by ring

/-- A sample-dependent potential close to one member of a finite grid is
controlled by the fixed grid endpoints. No independence of `h` is required. -/
theorem movingCellEmpiricalRemainder_finiteGrid_bound (data : HELLOSDOTData X Ω)
    (C : NNReal) (hC : LipschitzWith C data.populationMarginal)
    {m : ℕ} (samples : Fin m → X) (gStar h : Fin data.n → ℝ)
    (grid : Finset (Fin data.n → ℝ)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcover : ∃ g ∈ grid, ∀ k, |h k - g k| ≤ δ) :
    weightedSquare data (movingCellEmpiricalRemainder data gStar samples h) ≤
      2 * (∑ g ∈ grid, ∑ j,
        ((movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (-2 * δ)) j) ^ 2 +
          (movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (2 * δ)) j) ^ 2) /
            data.b j) + 32 * (C : ℝ) ^ 2 * δ ^ 2 * ∑ j, 1 / data.b j := by
  obtain ⟨g, hg, hclose⟩ := hcover
  have hcoord (j : Fin data.n) :
      (movingCellEmpiricalRemainder data gStar samples h j) ^ 2 ≤
        2 * ((movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (-2 * δ)) j) ^ 2 +
          (movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (2 * δ)) j) ^ 2) +
            32 * (C : ℝ) ^ 2 * δ ^ 2 := by
    have hb := movingCellEmpiricalRemainder_bracket data samples gStar g h δ hclose j
    have hgap := populationMarginal_coordinate_bracket_gap data C hC g hδ j
    have habs : |movingCellEmpiricalRemainder data gStar samples h j| ≤
        max |movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (-2 * δ)) j|
          |movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (2 * δ)) j| +
            4 * C * δ := by linarith
    have hs := mul_self_le_mul_self (abs_nonneg _) habs
    rw [← sq, sq_abs, ← sq] at hs
    rcases le_total
      |movingCellEmpiricalRemainder data gStar samples (shiftPotentialCoordinate g j (-2 * δ)) j|
      |movingCellEmpiricalRemainder data gStar samples (shiftPotentialCoordinate g j (2 * δ)) j|
      with hlo | hhi
    · rw [max_eq_right hlo] at hs
      nlinarith [sq_nonneg
        (|movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (2 * δ)) j| -
          4 * C * δ), sq_abs
            (movingCellEmpiricalRemainder data gStar samples
              (shiftPotentialCoordinate g j (2 * δ)) j),
          sq_nonneg (movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (-2 * δ)) j)]
    · rw [max_eq_left hhi] at hs
      nlinarith [sq_nonneg
        (|movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (-2 * δ)) j| -
          4 * C * δ), sq_abs
            (movingCellEmpiricalRemainder data gStar samples
              (shiftPotentialCoordinate g j (-2 * δ)) j),
          sq_nonneg (movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (2 * δ)) j)]
  have hchosen : weightedSquare data (movingCellEmpiricalRemainder data gStar samples h) ≤
      2 * (∑ j,
        ((movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (-2 * δ)) j) ^ 2 +
          (movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (2 * δ)) j) ^ 2) /
            data.b j) + 32 * (C : ℝ) ^ 2 * δ ^ 2 * ∑ j, 1 / data.b j := by
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
      div_le_div_of_nonneg_right (hcoord j) (data.b_pos j).le
    calc
      weightedSquare data (movingCellEmpiricalRemainder data gStar samples h) ≤ _ := hsum
      _ = _ := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
  have hgrid := Finset.single_le_sum
    (f := fun q => ∑ j,
      ((movingCellEmpiricalRemainder data gStar samples
          (shiftPotentialCoordinate q j (-2 * δ)) j) ^ 2 +
        (movingCellEmpiricalRemainder data gStar samples
          (shiftPotentialCoordinate q j (2 * δ)) j) ^ 2) /
          data.b j)
    (fun q _ => Finset.sum_nonneg fun j _ =>
      div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (data.b_pos j).le) hg
  exact hchosen.trans (add_le_add
    (mul_le_mul_of_nonneg_left hgrid (show (0 : ℝ) ≤ 2 by norm_num)) le_rfl)

theorem cellIndicator_mem_Icc (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j : Fin data.n) (x : X) :
    cellIndicator data g j x ∈ Set.Icc 0 1 := by
  classical
  simp only [cellIndicator, Set.indicator_apply, Set.mem_Icc]
  split_ifs <;> norm_num

theorem empiricalCellMass_mem_Icc (data : HELLOSDOTData X Ω)
    {m : ℕ} (hm : 0 < m) (samples : Fin m → X) (g : Fin data.n → ℝ) (j : Fin data.n) :
    empiricalCellMass data samples g j ∈ Set.Icc 0 1 := by
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  constructor
  · exact mul_nonneg (by positivity)
      (Finset.sum_nonneg fun k _ => (cellIndicator_mem_Icc data g j (samples k)).1)
  · calc
      empiricalCellMass data samples g j ≤ (1 / (m : ℝ)) * ∑ _k : Fin m, (1 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum fun k _ => (cellIndicator_mem_Icc data g j (samples k)).2)
          (by positivity)
      _ = 1 := by simp [hmreal.ne']

theorem abs_movingCellEmpiricalRemainder_le_two (data : HELLOSDOTData X Ω)
    {m : ℕ} (hm : 0 < m) (samples : Fin m → X) (g h : Fin data.n → ℝ) (j : Fin data.n) :
    |movingCellEmpiricalRemainder data g samples h j| ≤ 2 := by
  have hg := empiricalCellMass_mem_Icc data hm samples g j
  have hh := empiricalCellMass_mem_Icc data hm samples h j
  have hpg := populationMarginal_nonneg data g j
  have hph := populationMarginal_nonneg data h j
  have hpg' := populationMarginal_le_one data g j
  have hph' := populationMarginal_le_one data h j
  simp only [movingCellEmpiricalRemainder, Pi.sub_apply]
  apply abs_le.mpr
  constructor <;> linarith [hg.1, hg.2, hh.1, hh.2]

theorem movingCellEmpiricalRemainder_energy_le (data : HELLOSDOTData X Ω)
    {m : ℕ} (hm : 0 < m) (samples : Fin m → X) (g h : Fin data.n → ℝ) :
    weightedSquare data (movingCellEmpiricalRemainder data g samples h) ≤
      4 * ∑ j, 1 / data.b j := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hs := mul_self_le_mul_self (abs_nonneg _)
    (abs_movingCellEmpiricalRemainder_le_two data hm samples g h j)
  rw [← sq, sq_abs] at hs
  norm_num only at hs
  simpa only [div_eq_mul_inv, one_mul] using div_le_div_of_nonneg_right hs (data.b_pos j).le

theorem measurable_batchMovingCellEmpiricalRemainder (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    {m : ℕ} (hm : 0 < m) (j : Fin data.n) :
    Measurable fun batch : (Fin m → X) × Ω =>
      movingCellEmpiricalRemainder data gStar batch.1 (empiricalBatchPotential data m batch) j := by
  have hpotential := measurable_empiricalBatchPotential data hexact hm
  have hmass : Measurable fun batch : (Fin m → X) × Ω =>
      empiricalCellMass data batch.1 (empiricalBatchPotential data m batch) j := by
    convert (measurable_batchTieResidual data hexact hm j).add_const (data.b j) using 1
    ext batch
    simp only [empiricalTieResidual, sub_add_cancel]
  have hfixed (k : Fin m) : Measurable fun batch : (Fin m → X) × Ω =>
      cellIndicator data gStar j (batch.1 k) :=
    (measurable_jointCellIndicator data j).comp
      (measurable_const.prodMk ((measurable_pi_apply k).comp measurable_fst))
  have hpopulation := measurable_populationMarginal data
  have hfixedMass : Measurable fun batch : (Fin m → X) × Ω =>
      empiricalCellMass data batch.1 gStar j := by
    unfold empiricalCellMass iidAverage
    fun_prop
  change Measurable fun batch : (Fin m → X) × Ω =>
    (empiricalCellMass data batch.1 (empiricalBatchPotential data m batch) j -
      empiricalCellMass data batch.1 gStar j) -
    (data.populationMarginal (empiricalBatchPotential data m batch) j -
      data.populationMarginal gStar j)
  exact (hmass.sub hfixedMass).sub
    (((measurable_pi_apply j).comp (hpopulation.comp hpotential)).sub_const _)

theorem memLp_batchMovingCellEmpiricalRemainder (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    {m : ℕ} (hm : 0 < m) (j : Fin data.n) :
    MemLp (fun batch =>
      movingCellEmpiricalRemainder data gStar batch.1 (empiricalBatchPotential data m batch) j)
      2 (empiricalBatchMeasure data m) := by
  apply MemLp.of_bound
    (measurable_batchMovingCellEmpiricalRemainder data hexact gStar hm j).aestronglyMeasurable 2
  filter_upwards [] with batch
  simpa only [Real.norm_eq_abs] using
    abs_movingCellEmpiricalRemainder_le_two data hm batch.1 gStar _ j

noncomputable def batchMovingCellEnergy (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (m : ℕ) : ℝ :=
  ∫ batch, weightedSquare data
    (movingCellEmpiricalRemainder data gStar batch.1 (empiricalBatchPotential data m batch))
      ∂empiricalBatchMeasure data m

def batchPotentialLocalEvent (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (m : ℕ) (r : ℝ) : Set ((Fin m → X) × Ω) :=
  {batch | ‖empiricalBatchPotential data m batch - gStar‖ ≤ r}

theorem measurableSet_batchPotentialLocalEvent (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    {m : ℕ} (hm : 0 < m) (r : ℝ) : MeasurableSet (batchPotentialLocalEvent data gStar m r) := by
  have hpotential := measurable_empiricalBatchPotential data hexact hm
  unfold batchPotentialLocalEvent
  apply measurableSet_le _ measurable_const
  fun_prop

noncomputable def gridEndpointEnergy (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) {m : ℕ} (grid : Finset (Fin data.n → ℝ)) (δ : ℝ)
    (samples : Fin m → X) : ℝ :=
  ∑ g ∈ grid, ∑ j,
    ((movingCellEmpiricalRemainder data gStar samples
        (shiftPotentialCoordinate g j (-2 * δ)) j) ^ 2 +
      (movingCellEmpiricalRemainder data gStar samples
        (shiftPotentialCoordinate g j (2 * δ)) j) ^ 2) /
        data.b j

theorem integrable_gridEndpointEnergy (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (m : ℕ) (grid : Finset (Fin data.n → ℝ)) (δ : ℝ) :
    Integrable (gridEndpointEnergy data gStar (m := m) grid δ) (sourceBatchMeasure data m) :=
  integrable_finset_sum grid fun g _ => integrable_finset_sum Finset.univ fun j _ =>
    (((memLp_fixedMovingCellEmpiricalRemainder data gStar
      (shiftPotentialCoordinate g j (-2 * δ)) j).integrable_sq).add
        ((memLp_fixedMovingCellEmpiricalRemainder data gStar
          (shiftPotentialCoordinate g j (2 * δ)) j).integrable_sq)).div_const _

/-- The integral form of finite-grid bracketing for the actual empirical
oracle. The remaining stochastic inputs are the grid fluctuation sum and
the probability of the potential leaving the covered ball. -/
theorem batchMovingCellEnergy_finiteGrid_bound (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (C : NNReal)
    (hC : LipschitzWith C data.populationMarginal) (gStar : Fin data.n → ℝ)
    {m : ℕ} (hm : 0 < m) (grid : Finset (Fin data.n → ℝ)) (r : ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hcover : ∀ h : Fin data.n → ℝ, ‖h - gStar‖ ≤ r →
      ∃ g ∈ grid, ∀ k, |h k - g k| ≤ δ) :
    batchMovingCellEnergy data gStar m ≤
      2 * (∫ samples, gridEndpointEnergy data gStar grid δ samples
        ∂sourceBatchMeasure data m) +
        32 * (C : ℝ) ^ 2 * δ ^ 2 * (∑ j, 1 / data.b j) +
        (4 * ∑ j, 1 / data.b j) *
          (empiricalBatchMeasure data m (batchPotentialLocalEvent data gStar m r)ᶜ).toReal := by
  classical
  let A := batchPotentialLocalEvent data gStar m r
  let B := ∑ j, 1 / data.b j
  let K := 32 * (C : ℝ) ^ 2 * δ ^ 2 * B
  have hB : 0 ≤ B := Finset.sum_nonneg fun j _ => div_nonneg (by norm_num) (data.b_pos j).le
  have hK : 0 ≤ K := by positivity
  have hA : MeasurableSet A := measurableSet_batchPotentialLocalEvent data hexact gStar hm r
  have hF := integrable_finset_sum Finset.univ fun j _ =>
    (memLp_batchMovingCellEmpiricalRemainder data hexact gStar hm j).integrable_sq.div_const
      (data.b j)
  have hgrid : Integrable (fun batch : (Fin m → X) × Ω =>
      gridEndpointEnergy data gStar grid δ batch.1)
      (empiricalBatchMeasure data m) :=
    (integrable_gridEndpointEnergy data gStar m grid δ).comp_fst (data.solverMeasure m)
  have hindicator : Integrable (Aᶜ.indicator (fun _ => 4 * B)) (empiricalBatchMeasure data m) :=
    (integrable_const _).indicator hA.compl
  have hpoint (batch : (Fin m → X) × Ω) :
      weightedSquare data
        (movingCellEmpiricalRemainder data gStar batch.1 (empiricalBatchPotential data m batch)) ≤
      2 * gridEndpointEnergy data gStar grid δ batch.1 + K +
        Aᶜ.indicator (fun _ => 4 * B) batch := by
    by_cases hb : batch ∈ A
    · rw [Set.indicator_of_notMem (not_not.mpr hb : batch ∉ Aᶜ)]
      simpa only [add_zero] using movingCellEmpiricalRemainder_finiteGrid_bound
        data C hC batch.1 gStar _ grid hδ (hcover _ hb)
    · rw [Set.indicator_of_mem (show batch ∈ Aᶜ from hb)]
      have hgridNonneg : 0 ≤ gridEndpointEnergy data gStar grid δ batch.1 :=
        Finset.sum_nonneg fun g _ => Finset.sum_nonneg fun j _ =>
          div_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (data.b_pos j).le
      have hbound := movingCellEmpiricalRemainder_energy_le data hm batch.1 gStar
        (empiricalBatchPotential data m batch)
      change _ ≤ 2 * gridEndpointEnergy data gStar grid δ batch.1 + K + 4 * B
      linarith
  have hbase : Integrable (fun batch : (Fin m → X) × Ω =>
      2 * gridEndpointEnergy data gStar grid δ batch.1 + K) (empiricalBatchMeasure data m) :=
    (hgrid.const_mul 2).add (integrable_const K)
  have h := integral_mono hF (hbase.add hindicator) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add hbase hindicator,
    integral_add (hgrid.const_mul 2) (integrable_const K), integral_const_mul,
    integral_const, probReal_univ, one_smul] at h
  have hfst : (∫ batch, gridEndpointEnergy data gStar grid δ batch.1
      ∂empiricalBatchMeasure data m) =
      ∫ samples, gridEndpointEnergy data gStar grid δ samples ∂sourceBatchMeasure data m := by
    simpa only [empiricalBatchMeasure, probReal_univ, one_smul] using
      (integral_fun_fst (μ := sourceBatchMeasure data m) (ν := data.solverMeasure m)
        (gridEndpointEnergy data gStar grid δ))
  have hIndicator : (∫ batch, Aᶜ.indicator (fun _ => 4 * B) batch
      ∂empiricalBatchMeasure data m) =
      (4 * B) * (empiricalBatchMeasure data m Aᶜ).toReal := by
    rw [integral_indicator_const (4 * B) hA.compl]
    simp only [smul_eq_mul, measureReal_def]
    ring
  rw [hfst, hIndicator] at h
  exact h

end DualGuided2026
