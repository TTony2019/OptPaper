import TheoremLib.Dual_guided_2026.SDOTTies

/-!
# The moving-cell envelope

A change of Laguerre assignment under a potential perturbation of radius `r`
is confined to finitely many pairwise strips of width proportional to `r`.
Anti-concentration gives the envelope mass estimate (55) in Lemma F.7.
-/

namespace DualGuided2026

open MeasureTheory
open scoped BigOperators

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

theorem target_separation_pos (data : HELLOSDOTData X Ω) {i j : Fin data.n}
    (hij : i ≠ j) : 0 < ‖data.targetSites j - data.targetSites i‖ := by
  apply norm_pos_iff.mpr
  intro h
  exact hij.symm (data.targetSites_injective (sub_eq_zero.mp h))

def pairwiseBoundaryStrip (data : HELLOSDOTData X Ω) (g : Fin data.n → ℝ)
    (r : ℝ) (i j : Fin data.n) : Set X :=
  {x | |sdCost data x i - g i - (sdCost data x j - g j)| ≤ 2 * r}

theorem measurableSet_pairwiseBoundaryStrip (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (r : ℝ) (i j : Fin data.n) :
    MeasurableSet (pairwiseBoundaryStrip data g r i j) := by
  unfold pairwiseBoundaryStrip
  apply measurableSet_le _ measurable_const
  unfold sdCost
  fun_prop

theorem pairwiseBoundaryStrip_subset_projection (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (r : ℝ) {i j : Fin data.n} (hij : i ≠ j) :
    pairwiseBoundaryStrip data g r i j ⊆
      {x | |inner ℝ (targetUnitDirection data i j) x -
        (g i - g j - ‖data.targetSites i‖ ^ 2 + ‖data.targetSites j‖ ^ 2) /
          (2 * ‖data.targetSites j - data.targetSites i‖)| ≤
            r / ‖data.targetSites j - data.targetSites i‖} := by
  intro x hx
  have hd := target_separation_pos data hij
  have hidentity : sdCost data x i - g i - (sdCost data x j - g j) =
      (2 * ‖data.targetSites j - data.targetSites i‖) *
        (inner ℝ (targetUnitDirection data i j) x -
          (g i - g j - ‖data.targetSites i‖ ^ 2 + ‖data.targetSites j‖ ^ 2) /
            (2 * ‖data.targetSites j - data.targetSites i‖)) := by
    rw [show sdCost data x i - g i - (sdCost data x j - g j) =
      (sdCost data x i - sdCost data x j) - g i + g j by ring, sdCost_sub_sdCost]
    simp only [targetUnitDirection, real_inner_smul_left]
    field_simp
    ring
  change |sdCost data x i - g i - (sdCost data x j - g j)| ≤ 2 * r at hx
  rw [hidentity, abs_mul, abs_of_pos (mul_pos (by norm_num) hd)] at hx
  simp only [Set.mem_setOf_eq]
  apply (le_div_iff₀ hd).mpr
  nlinarith

/-- An explicit measurable envelope for all cell changes in a coordinatewise
potential ball. -/
def movingCellEnvelope (data : HELLOSDOTData X Ω) (g : Fin data.n → ℝ) (r : ℝ) : Set X :=
  ⋃ p : {p : Fin data.n × Fin data.n // p.1 ≠ p.2},
    pairwiseBoundaryStrip data g r p.1.1 p.1.2

theorem measurableSet_movingCellEnvelope (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (r : ℝ) : MeasurableSet (movingCellEnvelope data g r) :=
  MeasurableSet.iUnion fun p => measurableSet_pairwiseBoundaryStrip data g r p.1.1 p.1.2

theorem assignment_change_mem_envelope (data : HELLOSDOTData X Ω)
    (g h : Fin data.n → ℝ) (r : ℝ) (hclose : ∀ j, |h j - g j| ≤ r) (x : X)
    (hchange : laguerreAssignment data h x ≠ laguerreAssignment data g x) :
    x ∈ movingCellEnvelope data g r := by
  let i := laguerreAssignment data h x
  let j := laguerreAssignment data g x
  apply Set.mem_iUnion.mpr
  refine ⟨⟨(i, j), hchange⟩, ?_⟩
  change |sdCost data x i - g i - (sdCost data x j - g j)| ≤ 2 * r
  have hi := (laguerreAssignment_mem data h x).1 j
  have hj := (laguerreAssignment_mem data g x).1 i
  have hci := abs_le.mp (hclose i)
  have hcj := abs_le.mp (hclose j)
  rw [abs_of_nonneg (by linarith)]
  dsimp only [i, j] at hci hcj ⊢
  linarith

theorem cellIndicator_eq_off_envelope (data : HELLOSDOTData X Ω)
    (g h : Fin data.n → ℝ) (r : ℝ) (hclose : ∀ j, |h j - g j| ≤ r)
    (x : X) (hx : x ∉ movingCellEnvelope data g r) (j : Fin data.n) :
    cellIndicator data h j x = cellIndicator data g j x := by
  have heq : laguerreAssignment data h x = laguerreAssignment data g x := by
    by_contra hne
    exact hx (assignment_change_mem_envelope data g h r hclose x hne)
  simp only [cellIndicator_eq_assignment, heq]

/-- Lemma F.7 (55). The constant depends only on the source and fixed sites,
and the estimate is uniform in the center potential. -/
theorem movingCellEnvelope_measure_le (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g : Fin data.n → ℝ) (r : ℝ), 0 < r →
        data.sourceMeasure (movingCellEnvelope data g r) ≤ ENNReal.ofReal (C * r) := by
  classical
  obtain ⟨q, hq, hmoment, Cac, lambda, hCac, hlambda, hac, hrest⟩ := hregular
  let P := {p : Fin data.n × Fin data.n // p.1 ≠ p.2}
  let c : P → ℝ := fun p => Cac / ‖data.targetSites p.1.2 - data.targetSites p.1.1‖
  have hc (p : P) : 0 ≤ c p := div_nonneg hCac (norm_nonneg _)
  refine ⟨∑ p, c p, Finset.sum_nonneg (fun p _ => hc p), ?_⟩
  intro g r hr
  have hstrip (p : P) : data.sourceMeasure (pairwiseBoundaryStrip data g r p.1.1 p.1.2) ≤
      ENNReal.ofReal (c p * r) := by
    have hd := target_separation_pos data p.2
    have h := (measure_mono (pairwiseBoundaryStrip_subset_projection data g r p.2)).trans
      (hac p.1.1 p.1.2 p.2
        ((g p.1.1 - g p.1.2 - ‖data.targetSites p.1.1‖ ^ 2 + ‖data.targetSites p.1.2‖ ^ 2) /
          (2 * ‖data.targetSites p.1.2 - data.targetSites p.1.1‖))
        (r / ‖data.targetSites p.1.2 - data.targetSites p.1.1‖) (div_pos hr hd))
    convert h using 1
    congr 1
    dsimp only [c]
    ring
  calc
    data.sourceMeasure (movingCellEnvelope data g r) ≤
        ∑' p : P, data.sourceMeasure (pairwiseBoundaryStrip data g r p.1.1 p.1.2) :=
      measure_iUnion_le _
    _ ≤ ∑' p : P, ENNReal.ofReal (c p * r) := ENNReal.tsum_le_tsum hstrip
    _ = ENNReal.ofReal ((∑ p : P, c p) * r) := by
      rw [tsum_fintype, ← ENNReal.ofReal_sum_of_nonneg (fun p _ => mul_nonneg (hc p) hr.le),
        Finset.sum_mul]

theorem integral_cellIndicator_difference_le_envelope (data : HELLOSDOTData X Ω)
    (g h : Fin data.n → ℝ) (r : ℝ) (hclose : ∀ j, |h j - g j| ≤ r) (j : Fin data.n) :
    |data.populationMarginal h j - data.populationMarginal g j| ≤
      (data.sourceMeasure (movingCellEnvelope data g r)).toReal := by
  classical
  have hg := (memLp_cellIndicator data g j).integrable (by norm_num)
  have hh := (memLp_cellIndicator data h j).integrable (by norm_num)
  have hB := measurableSet_movingCellEnvelope data g r
  have hbound (x : X) : |cellIndicator data h j x - cellIndicator data g j x| ≤
      (movingCellEnvelope data g r).indicator (fun _ => (1 : ℝ)) x := by
    by_cases hx : x ∈ movingCellEnvelope data g r
    · rw [Set.indicator_of_mem hx]
      simp only [cellIndicator, Set.indicator_apply]
      split_ifs <;> norm_num
    · rw [cellIndicator_eq_off_envelope data g h r hclose x hx,
        sub_self, abs_zero, Set.indicator_of_notMem hx]
  calc
    |data.populationMarginal h j - data.populationMarginal g j| =
        |∫ x, cellIndicator data h j x - cellIndicator data g j x ∂data.sourceMeasure| := by
      rw [integral_sub hh hg, integral_cellIndicator, integral_cellIndicator]
    _ ≤ ∫ x, |cellIndicator data h j x - cellIndicator data g j x| ∂data.sourceMeasure :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, (movingCellEnvelope data g r).indicator (fun _ => (1 : ℝ)) x
        ∂data.sourceMeasure :=
      integral_mono (hh.sub hg).abs ((integrable_const (1 : ℝ)).indicator hB) hbound
    _ = (data.sourceMeasure (movingCellEnvelope data g r)).toReal := integral_indicator_one hB

/-- Anti-concentration implies a global Lipschitz bound for the population
mass map, in the same supremum norm used to define the moving-cell ball. -/
theorem populationMarginal_lipschitz (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) :
    ∃ C : NNReal, LipschitzWith C data.populationMarginal := by
  obtain ⟨C, hC, hmass⟩ := movingCellEnvelope_measure_le data hregular
  refine ⟨⟨C, hC⟩, LipschitzWith.of_dist_le_mul ?_⟩
  intro h g
  by_cases heq : h = g
  · simp [heq]
  have hr : 0 < ‖h - g‖ := norm_pos_iff.mpr (sub_ne_zero.mpr heq)
  have hclose (j : Fin data.n) : |h j - g j| ≤ ‖h - g‖ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (h - g) j
  have hmassReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmass g ‖h - g‖ hr)
  rw [ENNReal.toReal_ofReal (mul_nonneg hC hr.le)] at hmassReal
  simp only [dist_eq_norm]
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC hr.le)).mpr
  intro j
  simp only [Pi.sub_apply, Real.norm_eq_abs]
  exact (integral_cellIndicator_difference_le_envelope data g h ‖h - g‖ hclose j).trans hmassReal

end DualGuided2026
