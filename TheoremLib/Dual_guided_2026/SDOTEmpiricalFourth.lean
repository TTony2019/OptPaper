import TheoremLib.Dual_guided_2026.SDOTFiniteGrid
import TheoremLib.Dual_guided_2026.SDOTVariance

/-!
# Fourth moments of fixed moving-cell fluctuations

These bounds retain the small probability of the moving boundary envelope.
They are intended for finite-grid control of a sample-dependent potential.
-/

namespace DualGuided2026

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

theorem norm_cellIndicator_difference_le (data : HELLOSDOTData X Ω)
    (g h : Fin data.n → ℝ) (j : Fin data.n) (x : X) :
    ‖cellIndicator data h j x - cellIndicator data g j x‖ ≤ 1 := by
  classical
  simp only [cellIndicator, Set.indicator_apply]
  split_ifs <;> norm_num

theorem fixedMovingCell_fourth_moment_le_envelope (data : HELLOSDOTData X Ω)
    (g h : Fin data.n → ℝ) (r : ℝ) (hclose : ∀ j, |h j - g j| ≤ r)
    {m : ℕ} (hm : 0 < m) (j : Fin data.n) :
    (∫ samples, (movingCellEmpiricalRemainder data g samples h j) ^ 4
      ∂sourceBatchMeasure data m) ≤
        4 * (data.sourceMeasure (movingCellEnvelope data g r)).toReal / (m : ℝ) ^ 3 +
          3 * ((data.sourceMeasure (movingCellEnvelope data g r)).toReal) ^ 2 / (m : ℝ) ^ 2 := by
  let f : X → ℝ := fun x => cellIndicator data h j x - cellIndicator data g j x
  let F : X → ℝ := fun x => f x - ∫ y, f y ∂data.sourceMeasure
  let α := (data.sourceMeasure (movingCellEnvelope data g r)).toReal
  have hfmeas : Measurable f :=
    (measurable_const.indicator (measurableSet_laguerreCell data h j)).sub
      (measurable_const.indicator (measurableSet_laguerreCell data g j))
  have hfmem : MemLp f 2 data.sourceMeasure :=
    (memLp_cellIndicator data h j).sub (memLp_cellIndicator data g j)
  have hmeanBound : ‖∫ y, f y ∂data.sourceMeasure‖ ≤ 1 := by
    simpa using norm_integral_le_of_norm_le_const (μ := data.sourceMeasure)
      (Filter.Eventually.of_forall (norm_cellIndicator_difference_le data g h j))
  have hFmeas : Measurable F := hfmeas.sub measurable_const
  have hFbound (x : X) : ‖F x‖ ≤ 2 :=
    (norm_sub_le _ _).trans (by
      have hb := norm_cellIndicator_difference_le data g h j x
      change ‖f x‖ + ‖∫ y, f y ∂data.sourceMeasure‖ ≤ 2
      linarith)
  have hFzero : (∫ x, F x ∂data.sourceMeasure) = 0 := by
    dsimp [F]
    rw [integral_sub (hfmem.integrable (by norm_num)) (integrable_const _)]
    simp
  have hFsecond : (∫ x, F x ^ 2 ∂data.sourceMeasure) = variance f data.sourceMeasure :=
    (variance_eq_integral hfmeas.aemeasurable).symm
  have hvarle : variance f data.sourceMeasure ≤ α :=
    variance_cellIndicator_difference_le_envelope data g h r hclose j
  have hfour : (∫ x, F x ^ 4 ∂data.sourceMeasure) ≤ 4 * variance f data.sourceMeasure := by
    have hmem4 := memLp_pow_of_bound (μ := data.sourceMeasure) hFmeas (by norm_num) hFbound 4
    have hmem2 := memLp_pow_of_bound (μ := data.sourceMeasure) hFmeas (by norm_num) hFbound 2
    have hi4 := hmem4.integrable (by norm_num)
    have hi2 := hmem2.integrable (by norm_num)
    calc
      _ ≤ ∫ x, 4 * F x ^ 2 ∂data.sourceMeasure :=
        integral_mono hi4 (hi2.const_mul 4) (fun x => by
        have hb := hFbound x
        rw [Real.norm_eq_abs] at hb
        have hs : F x ^ 2 ≤ 4 := by nlinarith only [abs_le.mp hb, sq_nonneg (F x)]
        nlinarith only [mul_nonneg (sq_nonneg (F x)) (sub_nonneg.mpr hs)])
      _ = _ := by rw [integral_const_mul, hFsecond]
  have hFun (samples : Fin m → X) : movingCellEmpiricalRemainder data g samples h j =
      iidAverage F m samples := by
    rw [movingCellEmpiricalRemainder_eq_centeredAverage data g h]
    change (1 / (m : ℝ)) * ∑ k, f (samples k) - (∫ y, f y ∂data.sourceMeasure) =
      (1 / (m : ℝ)) * ∑ k, (f (samples k) - (∫ y, f y ∂data.sourceMeasure))
    conv_rhs => rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
    field_simp
  simp only [hFun]
  unfold sourceBatchMeasure
  rw [integral_iidAverage_fourth hFmeas (by norm_num) hFbound hFzero hm, hFsecond]
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hα : 0 ≤ α := ENNReal.toReal_nonneg
  have hvar : 0 ≤ variance f data.sourceMeasure := variance_nonneg _ _
  have hsquare : (variance f data.sourceMeasure) ^ 2 ≤ α ^ 2 :=
    pow_le_pow_left₀ hvar hvarle 2
  calc
    ((∫ x, F x ^ 4 ∂data.sourceMeasure) +
        3 * ((m : ℝ) - 1) * (variance f data.sourceMeasure) ^ 2) /
        (m : ℝ) ^ 3 ≤ (4 * α + 3 * (m : ℝ) * α ^ 2) / (m : ℝ) ^ 3 := by
      apply div_le_div_of_nonneg_right _ (pow_pos hmreal _).le
      have hsmall := mul_le_mul_of_nonneg_left hsquare
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 3) (sub_nonneg.mpr hmone))
      nlinarith only [hfour, hvarle, hsmall, sq_nonneg α]
    _ = 4 * α / (m : ℝ) ^ 3 + 3 * α ^ 2 / (m : ℝ) ^ 2 := by field_simp

theorem fixedMovingCell_fourth_moment_le (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g h : Fin data.n → ℝ) (r : ℝ), 0 < r →
        (∀ j, |h j - g j| ≤ r) → ∀ {m : ℕ}, 0 < m → ∀ j : Fin data.n,
          (∫ samples, (movingCellEmpiricalRemainder data g samples h j) ^ 4
            ∂sourceBatchMeasure data m) ≤
              4 * C * r / (m : ℝ) ^ 3 + 3 * C ^ 2 * r ^ 2 / (m : ℝ) ^ 2 := by
  obtain ⟨C, hC, hmass⟩ := movingCellEnvelope_measure_le data hregular
  refine ⟨C, hC, ?_⟩
  intro g h r hr hclose m hm j
  have hmassReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hmass g r hr)
  rw [ENNReal.toReal_ofReal (mul_nonneg hC hr.le)] at hmassReal
  have hsquare := pow_le_pow_left₀ ENNReal.toReal_nonneg hmassReal 2
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  refine (fixedMovingCell_fourth_moment_le_envelope data g h r hclose hm j).trans ?_
  have hterm1 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hmassReal (by norm_num : (0 : ℝ) ≤ 4))
    (pow_pos hmreal 3).le
  have hterm2 := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hsquare (by norm_num : (0 : ℝ) ≤ 3))
    (sq_pos_of_pos hmreal).le
  convert add_le_add hterm1 hterm2 using 1
  ring

theorem memLp_fixedMovingCellEmpiricalRemainder_sq (data : HELLOSDOTData X Ω)
    (g h : Fin data.n → ℝ) {m : ℕ} (hm : 0 < m) (j : Fin data.n) :
    MemLp (fun samples => (movingCellEmpiricalRemainder data g samples h j) ^ 2) 2
      (sourceBatchMeasure data m) := by
  have hbound (samples : Fin m → X) :
      ‖movingCellEmpiricalRemainder data g samples h j‖ ≤ 2 := by
    rw [movingCellEmpiricalRemainder_eq_centeredAverage data g h]
    have hmeanBound : ‖∫ x, cellIndicator data h j x - cellIndicator data g j x
        ∂data.sourceMeasure‖ ≤ 1 := by
      simpa using norm_integral_le_of_norm_le_const (μ := data.sourceMeasure)
        (Filter.Eventually.of_forall (norm_cellIndicator_difference_le data g h j))
    have havgBound := norm_iidAverage_le (norm_cellIndicator_difference_le data g h j) hm samples
    exact (norm_sub_le _ _).trans (by linarith)
  have hmeas := (memLp_fixedMovingCellEmpiricalRemainder data g h (m := m) j).aestronglyMeasurable
  apply MemLp.of_bound (hmeas.pow 2)
    (4 : ℝ)
  exact Filter.Eventually.of_forall fun samples => by
    simp only [Pi.pow_apply]
    rw [norm_pow]
    have h := pow_le_pow_left₀ (norm_nonneg _) (hbound samples) 2
    norm_num at h ⊢
    exact h

theorem fixedMovingCell_fourth_energy_le (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g h : Fin data.n → ℝ) (r : ℝ), 0 < r →
        (∀ j, |h j - g j| ≤ r) → ∀ {m : ℕ}, 0 < m →
          (∫ samples, (weightedSquare data (movingCellEmpiricalRemainder data g samples h)) ^ 2
            ∂sourceBatchMeasure data m) ≤
              (∑ j, 1 / data.b j) ^ 2 *
                (4 * C * r / (m : ℝ) ^ 3 + 3 * C ^ 2 * r ^ 2 / (m : ℝ) ^ 2) := by
  obtain ⟨C, hC, hfour⟩ := fixedMovingCell_fourth_moment_le data hregular
  refine ⟨C, hC, ?_⟩
  intro g h r hr hclose m hm
  let M := 4 * C * r / (m : ℝ) ^ 3 + 3 * C ^ 2 * r ^ 2 / (m : ℝ) ^ 2
  have hmem (j : Fin data.n) := memLp_fixedMovingCellEmpiricalRemainder_sq data g h hm j
  have hifour (j : Fin data.n) : Integrable (fun samples =>
      (movingCellEmpiricalRemainder data g samples h j) ^ 4) (sourceBatchMeasure data m) := by
    convert (hmem j).integrable_sq using 1
    ext samples
    ring
  have hpair (j k : Fin data.n) :
      (∫ samples, (movingCellEmpiricalRemainder data g samples h j) ^ 2 *
        (movingCellEmpiricalRemainder data g samples h k) ^ 2
          ∂sourceBatchMeasure data m) ≤ M := by
    have hi : Integrable (fun samples =>
        ((movingCellEmpiricalRemainder data g samples h j) ^ 4 +
          (movingCellEmpiricalRemainder data g samples h k) ^ 4) / 2) (sourceBatchMeasure data m) :=
      ((hifour j).add (hifour k)).div_const 2
    calc
      _ ≤ ∫ samples,
          ((movingCellEmpiricalRemainder data g samples h j) ^ 4 +
            (movingCellEmpiricalRemainder data g samples h k) ^ 4) / 2
              ∂sourceBatchMeasure data m :=
        integral_mono ((hmem j).integrable_mul (hmem k)) hi (fun samples => by
          simp only [Pi.mul_apply]
          nlinarith only [sq_nonneg ((movingCellEmpiricalRemainder data g samples h j) ^ 2 -
            (movingCellEmpiricalRemainder data g samples h k) ^ 2)])
      _ = ((∫ samples, (movingCellEmpiricalRemainder data g samples h j) ^ 4
            ∂sourceBatchMeasure data m) +
          (∫ samples, (movingCellEmpiricalRemainder data g samples h k) ^ 4
            ∂sourceBatchMeasure data m)) / 2 := by
        rw [integral_div, integral_add (hifour j) (hifour k)]
      _ ≤ M := by
        have hj := hfour g h r hr hclose hm j
        have hk := hfour g h r hr hclose hm k
        linarith
  rw [integral_weightedSquare_sq (sourceBatchMeasure data m) data
    (fun samples => movingCellEmpiricalRemainder data g samples h) hmem]
  calc
    (∑ j, ∑ k, (∫ samples, (movingCellEmpiricalRemainder data g samples h j) ^ 2 *
        (movingCellEmpiricalRemainder data g samples h k) ^ 2 ∂sourceBatchMeasure data m) /
          (data.b j * data.b k)) ≤ ∑ j, ∑ k, M / (data.b j * data.b k) :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
        div_le_div_of_nonneg_right (hpair j k) (mul_pos (data.b_pos j) (data.b_pos k)).le
    _ = (∑ j, 1 / data.b j) ^ 2 * M := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring

noncomputable def gridEndpointFourthEnergy (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (grid : Finset (Fin data.n → ℝ)) (δ : ℝ)
    {m : ℕ} (samples : Fin m → X) : ℝ :=
  ∑ g ∈ grid, ∑ j,
    ((movingCellEmpiricalRemainder data gStar samples
        (shiftPotentialCoordinate g j (-2 * δ)) j) ^ 4 +
      (movingCellEmpiricalRemainder data gStar samples
        (shiftPotentialCoordinate g j (2 * δ)) j) ^ 4) / (data.b j) ^ 2

theorem movingCellEmpiricalRemainder_finiteGrid_fourth_bound (data : HELLOSDOTData X Ω)
    (C : NNReal) (hC : LipschitzWith C data.populationMarginal)
    {m : ℕ} (samples : Fin m → X) (gStar h : Fin data.n → ℝ)
    (grid : Finset (Fin data.n → ℝ)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hcover : ∃ g ∈ grid, ∀ k, |h k - g k| ≤ δ) :
    (weightedSquare data (movingCellEmpiricalRemainder data gStar samples h)) ^ 2 ≤
      8 * data.n * gridEndpointFourthEnergy data gStar grid δ samples +
        2048 * data.n * (C : ℝ) ^ 4 * δ ^ 4 * ∑ j, 1 / (data.b j) ^ 2 := by
  obtain ⟨g, hg, hclose⟩ := hcover
  have hcoord (j : Fin data.n) :
      (movingCellEmpiricalRemainder data gStar samples h j) ^ 4 ≤
        8 * ((movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (-2 * δ)) j) ^ 4 +
          (movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (2 * δ)) j) ^ 4) + 2048 * (C : ℝ) ^ 4 * δ ^ 4 := by
    let a := |movingCellEmpiricalRemainder data gStar samples
      (shiftPotentialCoordinate g j (-2 * δ)) j|
    let b := |movingCellEmpiricalRemainder data gStar samples
      (shiftPotentialCoordinate g j (2 * δ)) j|
    have ha : 0 ≤ a := abs_nonneg _
    have hb : 0 ≤ b := abs_nonneg _
    have habs : |movingCellEmpiricalRemainder data gStar samples h j| ≤ max a b + 4 * C * δ := by
      have hbracket := movingCellEmpiricalRemainder_bracket data samples gStar g h δ hclose j
      have hgap := populationMarginal_coordinate_bracket_gap data C hC g hδ j
      linarith
    have hpow := pow_le_pow_left₀ (abs_nonneg _) habs 4
    have hmax : 0 ≤ max a b := ha.trans (le_max_left _ _)
    have hsum := add_pow_le hmax (by positivity : (0 : ℝ) ≤ 4 * C * δ) 4
    have hsummax : (max a b) ^ 4 ≤ a ^ 4 + b ^ 4 := by
      rcases le_total a b with hab | hba
      · rw [max_eq_right hab]
        linarith [pow_nonneg ha 4]
      · rw [max_eq_left hba]
        linarith [pow_nonneg hb 4]
    have habspow (x : ℝ) : |x| ^ 4 = x ^ 4 := (by norm_num : Even (4 : ℕ)).pow_abs x
    simp only [Nat.reduceSub, habspow] at hpow hsum
    have hcombined := hpow.trans hsum
    dsimp [a, b] at hsummax hcombined
    simp only [habspow] at hsummax
    nlinarith only [hcombined, hsummax]
  have hcauchy := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ)
    (f := fun j => (movingCellEmpiricalRemainder data gStar samples h j) ^ 2 / data.b j)
  simp only [Finset.card_univ, Fintype.card_fin] at hcauchy
  have hchosen : (weightedSquare data (movingCellEmpiricalRemainder data gStar samples h)) ^ 2 ≤
      8 * data.n * (∑ j,
        ((movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (-2 * δ)) j) ^ 4 +
          (movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (2 * δ)) j) ^ 4) / (data.b j) ^ 2) +
        2048 * data.n * (C : ℝ) ^ 4 * δ ^ 4 * ∑ j, 1 / (data.b j) ^ 2 := by
    have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) =>
      div_le_div_of_nonneg_right (hcoord j) (sq_nonneg (data.b j))
    have hsumscaled := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg data.n)
    have hscalar (j : Fin data.n) :
        ((movingCellEmpiricalRemainder data gStar samples h j) ^ 2 / data.b j) ^ 2 =
          (movingCellEmpiricalRemainder data gStar samples h j) ^ 4 / (data.b j) ^ 2 := by ring
    simp only [hscalar] at hcauchy
    refine hcauchy.trans (hsumscaled.trans_eq ?_)
    simp only [div_eq_mul_inv, add_mul, mul_add, mul_assoc, Finset.sum_add_distrib,
      ← Finset.mul_sum, one_mul]
    ring
  have hgrid := Finset.single_le_sum
    (f := fun q => ∑ j,
      ((movingCellEmpiricalRemainder data gStar samples
          (shiftPotentialCoordinate q j (-2 * δ)) j) ^ 4 +
        (movingCellEmpiricalRemainder data gStar samples
          (shiftPotentialCoordinate q j (2 * δ)) j) ^ 4) / (data.b j) ^ 2)
    (fun q _ => Finset.sum_nonneg fun j _ =>
      div_nonneg (add_nonneg (by positivity) (by positivity)) (sq_nonneg _)) hg
  exact hchosen.trans (add_le_add
    (mul_le_mul_of_nonneg_left hgrid (by positivity : (0 : ℝ) ≤ 8 * data.n)) le_rfl)

theorem gridEndpointFourthEnergy_integral_le (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (gStar : Fin data.n → ℝ) {m : ℕ}, 0 < m →
        ∀ (grid : Finset (Fin data.n → ℝ)) {r δ : ℝ}, 0 < r → 0 ≤ δ →
          (∀ g ∈ grid, ‖g - gStar‖ ≤ r) →
          (∫ samples, gridEndpointFourthEnergy data gStar grid δ samples
            ∂sourceBatchMeasure data m) ≤
            (grid.card : ℝ) * (2 * ∑ j, 1 / (data.b j) ^ 2) *
              (4 * C * (r + 2 * δ) / (m : ℝ) ^ 3 +
                3 * C ^ 2 * (r + 2 * δ) ^ 2 / (m : ℝ) ^ 2) := by
  classical
  obtain ⟨C, hC, hfour⟩ := fixedMovingCell_fourth_moment_le data hregular
  refine ⟨C, hC, ?_⟩
  intro gStar m hm grid r δ hr hδ hgrid
  let M := 4 * C * (r + 2 * δ) / (m : ℝ) ^ 3 +
    3 * C ^ 2 * (r + 2 * δ) ^ 2 / (m : ℝ) ^ 2
  have hρ : 0 < r + 2 * δ := by linarith
  have hfixed (g : Fin data.n → ℝ) (hg : g ∈ grid) (j : Fin data.n)
      (t : ℝ) (ht : |t| ≤ 2 * δ) :
      (∫ samples, movingCellEmpiricalRemainder data gStar samples
        (shiftPotentialCoordinate g j t) j ^ 4 ∂sourceBatchMeasure data m) ≤ M :=
    hfour _ _ _ hρ (shiftPotentialCoordinate_close data gStar g hδ (hgrid g hg) j ht) hm j
  have hneg : |-2 * δ| ≤ 2 * δ := by rw [abs_of_nonpos (by linarith)]; linarith
  have hpos : |2 * δ| ≤ 2 * δ := by rw [abs_of_nonneg (by positivity)]
  have hi (g : Fin data.n → ℝ) (j : Fin data.n) (t : ℝ) :
      Integrable (fun samples => movingCellEmpiricalRemainder data gStar samples
        (shiftPotentialCoordinate g j t) j ^ 4) (sourceBatchMeasure data m) := by
    convert (memLp_fixedMovingCellEmpiricalRemainder_sq data gStar
      (shiftPotentialCoordinate g j t) hm j).integrable_sq using 1
    ext samples
    ring
  have hterm (g : Fin data.n → ℝ) (j : Fin data.n) :
      Integrable (fun samples =>
        (movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (-2 * δ)) j ^ 4 +
          movingCellEmpiricalRemainder data gStar samples
            (shiftPotentialCoordinate g j (2 * δ)) j ^ 4) / (data.b j) ^ 2)
        (sourceBatchMeasure data m) := ((hi g j _).add (hi g j _)).div_const _
  unfold gridEndpointFourthEnergy
  rw [integral_finset_sum grid
    (fun g _ => integrable_finset_sum Finset.univ fun j _ => hterm g j)]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hterm _ j), integral_div,
    integral_add (hi _ _ _) (hi _ _ _)]
  calc
    _ ≤ ∑ g ∈ grid, ∑ j, (M + M) / (data.b j) ^ 2 := by
      apply Finset.sum_le_sum
      intro g hg
      apply Finset.sum_le_sum
      intro j _
      exact div_le_div_of_nonneg_right
        (add_le_add (hfixed g hg j _ hneg) (hfixed g hg j _ hpos)) (sq_nonneg _)
    _ = (grid.card : ℝ) * (2 * ∑ j, 1 / (data.b j) ^ 2) * M := by
      simp only [div_eq_mul_inv, one_mul, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
      ring

end DualGuided2026
