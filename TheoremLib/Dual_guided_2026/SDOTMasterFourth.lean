import TheoremLib.Dual_guided_2026.SDOTMasterBounds
import TheoremLib.Dual_guided_2026.SDOTEmpiricalFourth

/-!
# Fourth-moment bounds for the actual master remainder
-/

namespace DualGuided2026

open MeasureTheory ProbabilityTheory
open scoped BigOperators

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

noncomputable def linearizationFourthEnergy (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (m R : ℕ) : ℝ :=
  ∫ batches, (weightedSquare data
    (marginalLinearizationRemainder data gStar m R batches)) ^ 2 ∂repetitionMeasure data m R

noncomputable def averagedEmpiricalTieFourthEnergy (data : HELLOSDOTData X Ω)
    (m R : ℕ) : ℝ :=
  ∫ batches, (weightedSquare data (averagedEmpiricalTieResidual data m R batches)) ^ 2
    ∂repetitionMeasure data m R

noncomputable def batchMovingCellFourthEnergy (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (m : ℕ) : ℝ :=
  ∫ batch, (weightedSquare data (movingCellEmpiricalRemainder data gStar batch.1
    (empiricalBatchPotential data m batch))) ^ 2 ∂empiricalBatchMeasure data m

theorem iidAverage_sq_le_average_sq {A : Type*} (f : A → ℝ) (R : ℕ)
    (samples : Fin R → A) :
    (iidAverage f R samples) ^ 2 ≤ iidAverage (fun a => (f a) ^ 2) R samples := by
  have h := sum_div_card_sq_le_sum_sq_div_card
    (s := Finset.univ) (f := fun r : Fin R => f (samples r))
  simp only [Finset.card_univ, Fintype.card_fin] at h
  convert h using 1 <;> simp only [iidAverage, div_eq_mul_inv] <;> ring

theorem memLp_linearizationSquare (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    (hbalanced : data.populationMarginal gStar = data.b)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    MemLp (fun batches => weightedSquare data
      (marginalLinearizationRemainder data gStar m R batches)) 2
      (repetitionMeasure data m R) := by
  apply MemLp.of_bound
    (integrable_linearizationSquare data hexact gStar hm R).aestronglyMeasurable
    (4 * inverseWeightSum data)
  exact Filter.Eventually.of_forall fun batches => by
    rw [Real.norm_eq_abs, abs_of_nonneg (weightedSquare_nonneg data _)]
    exact marginalLinearizationRemainder_energy_le data gStar hbalanced hm hR batches

theorem memLp_averagedTieSquare (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (hexact : HasExactEmpiricalOTSolves data)
    (gStar : Fin data.n → ℝ) (hbalanced : data.populationMarginal gStar = data.b)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    MemLp (fun batches => weightedSquare data (averagedEmpiricalTieResidual data m R batches))
      2 (repetitionMeasure data m R) := by
  have hi : Integrable (fun batches => weightedSquare data
      (averagedEmpiricalTieResidual data m R batches)) (repetitionMeasure data m R) :=
    integrable_finset_sum Finset.univ fun j _ =>
      (memLp_averagedEmpiricalTieResidual data hregular hexact hm R j).integrable_sq.div_const _
  have hbound (batch : (Fin m → X) × Ω) (j : Fin data.n) :
      ‖empiricalTieResidual data batch.1 (empiricalBatchPotential data m batch) j‖ ≤ 1 := by
    have hmass := empiricalCellMass_mem_Icc data hm batch.1 (empiricalBatchPotential data m batch) j
    have hb0 := (data.b_pos j).le
    have hb1 : data.b j ≤ 1 := by rw [← hbalanced]; exact populationMarginal_le_one data gStar j
    rw [Real.norm_eq_abs]
    unfold empiricalTieResidual
    exact abs_le.mpr ⟨by linarith [hmass.1], by linarith [hmass.2]⟩
  apply MemLp.of_bound hi.aestronglyMeasurable (inverseWeightSum data)
  exact Filter.Eventually.of_forall fun batches => by
    rw [Real.norm_eq_abs, abs_of_nonneg (weightedSquare_nonneg data _)]
    unfold weightedSquare inverseWeightSum
    apply Finset.sum_le_sum
    intro j _
    apply div_le_div_of_nonneg_right _ (data.b_pos j).le
    have havg := norm_iidAverage_le (fun batch => hbound batch j) hR batches
    change |averagedEmpiricalTieResidual data m R batches j| ≤ 1 at havg
    have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr havg
    simpa only [sq_abs, one_pow] using hs

theorem averagedEmpiricalTieFourthEnergy_le (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (hexact : HasExactEmpiricalOTSolves data)
    (gStar : Fin data.n → ℝ) (hbalanced : data.populationMarginal gStar = data.b)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R) :
    averagedEmpiricalTieFourthEnergy data m R ≤
      (2 * (data.n.choose 2 : ℝ)) ^ 4 * (inverseWeightSum data) ^ 2 / (m : ℝ) ^ 4 := by
  let K := 2 * (data.n.choose 2 : ℝ) / (m : ℝ)
  have hall : ∀ᵐ batches ∂repetitionMeasure data m R, ∀ r : Fin R, ∀ j : Fin data.n,
      |empiricalTieResidual data (batches r).1
        (empiricalBatchPotential data m (batches r)) j| ≤ K := by
    apply ae_all_iff.mpr
    intro r
    have hbatch : ∀ᵐ batch ∂empiricalBatchMeasure data m, ∀ j : Fin data.n,
        |empiricalTieResidual data batch.1 (empiricalBatchPotential data m batch) j| ≤ K :=
      ae_all_iff.mpr (abs_batchTieResidual_le data hregular hexact hm)
    have heval := measurePreserving_eval (fun _ : Fin R => empiricalBatchMeasure data m) r
    exact heval.quasiMeasurePreserving.ae hbatch
  have hpoint : ∀ᵐ batches ∂repetitionMeasure data m R,
      (weightedSquare data (averagedEmpiricalTieResidual data m R batches)) ^ 2 ≤
        (K ^ 2 * inverseWeightSum data) ^ 2 := by
    filter_upwards [hall] with batches hbatches
    have hcoord (j : Fin data.n) : |averagedEmpiricalTieResidual data m R batches j| ≤ K := by
      have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
      change |(1 / (R : ℝ)) * ∑ r, empiricalTieResidual data (batches r).1
        (empiricalBatchPotential data m (batches r)) j| ≤ K
      rw [abs_mul, abs_of_pos (one_div_pos.mpr hRreal)]
      calc
        _ ≤ (1 / (R : ℝ)) * ∑ r, |empiricalTieResidual data (batches r).1
            (empiricalBatchPotential data m (batches r)) j| :=
          mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
        _ ≤ (1 / (R : ℝ)) * ∑ _r : Fin R, K :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => hbatches r j) (by positivity)
        _ = K := by simp; field_simp
    have henergy : weightedSquare data (averagedEmpiricalTieResidual data m R batches) ≤
        K ^ 2 * inverseWeightSum data := by
      unfold weightedSquare inverseWeightSum
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro j _
      have hs := mul_self_le_mul_self (abs_nonneg _) (hcoord j)
      rw [← sq, sq_abs, ← sq] at hs
      simpa only [div_eq_mul_inv, one_mul] using
        div_le_div_of_nonneg_right hs (data.b_pos j).le
    exact pow_le_pow_left₀ (weightedSquare_nonneg data _) henergy 2
  have h := integral_mono_ae
    (memLp_averagedTieSquare data hregular hexact gStar hbalanced hm hR).integrable_sq
    (integrable_const _) hpoint
  simp only [integral_const, probReal_univ, one_smul] at h
  change averagedEmpiricalTieFourthEnergy data m R ≤ _ at h
  refine h.trans_eq ?_
  dsimp [K]
  ring

theorem marginalLinearizationRemainder_local_fourth_bound
    (data : HELLOSDOTData X Ω) (gStar : Fin data.n → ℝ)
    (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (hbalanced : data.populationMarginal gStar = data.b)
    {C r₀ : ℝ} (hC : 0 ≤ C) (hr₀ : 0 < r₀)
    (hpop : ∀ g, ‖g - gStar‖ ≤ r₀ →
      weightedSquare data (populationLinearizationRemainder data gStar J g) ≤
        C * ‖g - gStar‖ ^ 4)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R)
    (batches : Fin R → ((Fin m → X) × Ω)) {r : ℝ} (hr : 0 ≤ r) (hrr₀ : r ≤ r₀)
    (hnear : ∀ s, ‖empiricalBatchPotential data m (batches s) - gStar‖ ≤ r) :
    (weightedSquare data (marginalLinearizationRemainder data gStar m R batches)) ^ 2 ≤
      48 * (weightedSquare data (averagedEmpiricalTieResidual data m R batches)) ^ 2 +
        48 * iidAverage (fun batch => (weightedSquare data
          (movingCellEmpiricalRemainder data gStar batch.1
            (empiricalBatchPotential data m batch))) ^ 2)
            R batches + 192 * C ^ 2 * r ^ 8 := by
  let T := weightedSquare data (averagedEmpiricalTieResidual data m R batches)
  let F := fun batch => weightedSquare data
    (movingCellEmpiricalRemainder data gStar batch.1 (empiricalBatchPotential data m batch))
  have hlocal := marginalLinearizationRemainder_local_energy_bound data gStar J hbalanced
    hC hr₀ hpop hm hR batches hr hrr₀ hnear
  change _ ≤ 4 * (T + iidAverage F R batches + 2 * C * r ^ 4) at hlocal
  have hsq := pow_le_pow_left₀ (weightedSquare_nonneg data _) hlocal 2
  have havg := iidAverage_sq_le_average_sq F R batches
  have hthree (a b c : ℝ) : (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
    nlinarith only [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]
  have htri := hthree T (iidAverage F R batches) (2 * C * r ^ 4)
  change _ ≤ 48 * T ^ 2 + 48 * iidAverage (fun batch => F batch ^ 2) R batches + _
  nlinarith only [hsq, htri, havg]

theorem linearizationFourthEnergy_localization_bound
    (data : HELLOSDOTData X Ω) (hregular : HasHELLOSDOTRegularity data)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (hbalanced : data.populationMarginal gStar = data.b)
    {C r₀ : ℝ} (hC : 0 ≤ C) (hr₀ : 0 < r₀)
    (hpop : ∀ g, ‖g - gStar‖ ≤ r₀ →
      weightedSquare data (populationLinearizationRemainder data gStar J g) ≤
        C * ‖g - gStar‖ ^ 4)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R) {r : ℝ} (hr : 0 ≤ r) (hrr₀ : r ≤ r₀) :
    linearizationFourthEnergy data gStar m R ≤
      48 * averagedEmpiricalTieFourthEnergy data m R +
        48 * batchMovingCellFourthEnergy data gStar m + 192 * C ^ 2 * r ^ 8 +
          16 * (inverseWeightSum data) ^ 2 * (R : ℝ) *
            (empiricalBatchMeasure data m).real (batchPotentialLocalEvent data gStar m r)ᶜ := by
  let A := repetitionPotentialLocalEvent data gStar m R r
  let T := fun batches => weightedSquare data (averagedEmpiricalTieResidual data m R batches)
  let F := fun batch => weightedSquare data (movingCellEmpiricalRemainder data gStar
    batch.1 (empiricalBatchPotential data m batch))
  let K := 192 * C ^ 2 * r ^ 8
  let B := 16 * (inverseWeightSum data) ^ 2
  have hB : 0 ≤ B := by positivity
  have hK : 0 ≤ K := by positivity
  have hA : MeasurableSet A :=
    measurableSet_repetitionPotentialLocalEvent data hexact gStar hm R r
  have hT : Integrable (fun batches => T batches ^ 2) (repetitionMeasure data m R) :=
    (memLp_averagedTieSquare data hregular hexact gStar hbalanced hm hR).integrable_sq
  have hF : MemLp F 2 (empiricalBatchMeasure data m) :=
    memLp_batchMovingCellEnergy data hexact gStar hm
  have hFsq : MemLp (fun batch => F batch ^ 2) 2 (empiricalBatchMeasure data m) := by
    apply MemLp.of_bound (hF.aestronglyMeasurable.pow 2) ((4 * inverseWeightSum data) ^ 2)
    exact Filter.Eventually.of_forall fun batch => by
      simp only [Pi.pow_apply, norm_pow]
      rw [Real.norm_eq_abs, abs_of_nonneg (weightedSquare_nonneg data _)]
      exact pow_le_pow_left₀ (weightedSquare_nonneg data _)
        (movingCellEmpiricalRemainder_energy_le data hm batch.1 gStar _) 2
  have hAvg : Integrable (iidAverage (fun batch => F batch ^ 2) R)
      (repetitionMeasure data m R) :=
    (memLp_iidAverage (empiricalBatchMeasure data m) hFsq R).integrable (by norm_num)
  have hsum : Integrable (fun batches => 48 * T batches ^ 2 +
      48 * iidAverage (fun batch => F batch ^ 2) R batches) (repetitionMeasure data m R) :=
    (hT.const_mul 48).add (hAvg.const_mul 48)
  have hbase : Integrable (fun batches => 48 * T batches ^ 2 +
      48 * iidAverage (fun batch => F batch ^ 2) R batches + K) (repetitionMeasure data m R) :=
    hsum.add (integrable_const K)
  have hInd : Integrable (Aᶜ.indicator (fun _ => B)) (repetitionMeasure data m R) :=
    (integrable_const B).indicator hA.compl
  have hpoint (batches) : (weightedSquare data
      (marginalLinearizationRemainder data gStar m R batches)) ^ 2 ≤
      48 * T batches ^ 2 + 48 * iidAverage (fun batch => F batch ^ 2) R batches + K +
        Aᶜ.indicator (fun _ => B) batches := by
    by_cases hb : batches ∈ A
    · rw [Set.indicator_of_notMem (not_not.mpr hb : batches ∉ Aᶜ)]
      have h := marginalLinearizationRemainder_local_fourth_bound data gStar J hbalanced
        hC hr₀ hpop hm hR batches hr hrr₀ hb
      change _ ≤ 48 * T batches ^ 2 +
        48 * iidAverage (fun batch => F batch ^ 2) R batches + K + 0
      dsimp only [T, F, K]
      linarith
    · rw [Set.indicator_of_mem (show batches ∈ Aᶜ from hb)]
      have h := pow_le_pow_left₀ (weightedSquare_nonneg data _)
        (marginalLinearizationRemainder_energy_le data gStar hbalanced hm hR batches) 2
      have hAvgNonneg : 0 ≤ iidAverage (fun batch => F batch ^ 2) R batches :=
        mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      change _ ≤ 48 * T batches ^ 2 +
        48 * iidAverage (fun batch => F batch ^ 2) R batches + K + B
      dsimp only [B]
      nlinarith only [h, hAvgNonneg, hK, sq_nonneg (T batches)]
  have hIntegrable := (memLp_linearizationSquare data hexact gStar hbalanced hm hR).integrable_sq
  have h := integral_mono hIntegrable
    (hbase.add hInd) hpoint
  have hAvgInt : (∫ batches, iidAverage (fun batch => F batch ^ 2) R batches
      ∂repetitionMeasure data m R) = ∫ batch, F batch ^ 2 ∂empiricalBatchMeasure data m :=
    integral_iidAverage (empiricalBatchMeasure data m) hFsq hR
  simp only [Pi.add_apply] at h
  rw [integral_add hbase hInd, integral_add hsum (integrable_const K),
    integral_add (hT.const_mul 48) (hAvg.const_mul 48),
    integral_const_mul, integral_const_mul, integral_const, probReal_univ, one_smul,
    integral_indicator_const B hA.compl, hAvgInt] at h
  change linearizationFourthEnergy data gStar m R ≤
    48 * averagedEmpiricalTieFourthEnergy data m R +
      48 * batchMovingCellFourthEnergy data gStar m + K +
        (repetitionMeasure data m R).real Aᶜ * B at h
  have htail := repetitionPotentialLocalEvent_compl_measure_le data hexact gStar hm R r
  have htailB := mul_le_mul_of_nonneg_right htail hB
  dsimp only [A, B, K] at h htailB
  nlinarith

theorem categorical_fourth_moment_uniform_bound (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (hbalanced : data.populationMarginal gStar = data.b) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {m R : ℕ}, 0 < m → 1 ≤ R →
      (∫ batches, (categoricalQuadraticError data gStar m R batches) ^ 2
        ∂repetitionMeasure data m R) ≤ A * |1 / (m : ℝ) ^ 2| := by
  let S := (∑ j, 1 / data.b j) - 2 * data.n + 1
  let B := ((data.n : ℝ) - 1) ^ 2 + 2 * ((data.n : ℝ) - 1)
  refine ⟨|B| + |S - B|, add_nonneg (abs_nonneg _) (abs_nonneg _), ?_⟩
  intro m R hm hR
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hRpos : 0 < R := Nat.zero_lt_one.trans_le hR
  let N := (m : ℝ) * R
  have hNpos : 0 < N := by dsimp [N]; positivity
  have hmN : (m : ℝ) ≤ N := by dsimp [N]; nlinarith
  have hNone : 1 ≤ N := hmone.trans hmN
  have hN2 : (m : ℝ) ^ 2 ≤ N ^ 2 := pow_le_pow_left₀ hmreal.le hmN 2
  have hN3 : (m : ℝ) ^ 2 ≤ N ^ 3 := by
    have h := mul_le_mul_of_nonneg_left hNone (sq_nonneg N)
    nlinarith
  have heq : (S + (N - 1) * B) / N ^ 3 = B / N ^ 2 + (S - B) / N ^ 3 := by
    field_simp
    ring
  change (∫ batches, (weightedSquare data
    (averagedCategoricalFluctuation data gStar m R batches)) ^ 2
      ∂repetitionMeasure data m R) ≤ _
  rw [categorical_fourth_moment data gStar hbalanced hm hRpos]
  change (S + (N - 1) * B) / N ^ 3 ≤ _
  rw [heq, abs_of_pos (one_div_pos.mpr (sq_pos_of_pos hmreal))]
  calc
    B / N ^ 2 + (S - B) / N ^ 3 ≤ |B| / N ^ 2 + |S - B| / N ^ 3 :=
      add_le_add (div_le_div_of_nonneg_right (le_abs_self _) (sq_nonneg _))
        (div_le_div_of_nonneg_right (le_abs_self _) (pow_pos hNpos _).le)
    _ ≤ |B| / (m : ℝ) ^ 2 + |S - B| / (m : ℝ) ^ 2 :=
      add_le_add (div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hmreal) hN2)
        (div_le_div_of_nonneg_left (abs_nonneg _) (sq_pos_of_pos hmreal) hN3)
    _ = (|B| + |S - B|) * (1 / (m : ℝ) ^ 2) := by ring

theorem quadraticErrorDifferenceEnergy_le (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    (hbalanced : data.populationMarginal gStar = data.b)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R) {ε : ℝ} (hε : 0 < ε) :
    quadraticErrorDifferenceEnergy data gStar m R ≤
      2 * ε ^ 2 * (∫ batches, (categoricalQuadraticError data gStar m R batches) ^ 2
        ∂repetitionMeasure data m R) +
          2 * (((1 + ε) / ε) ^ 2) * linearizationFourthEnergy data gStar m R := by
  let Q := categoricalQuadraticError data gStar m R
  let E := fun batches => weightedSquare data
    (marginalLinearizationRemainder data gStar m R batches)
  let c := (1 + ε) / ε
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpoint (batches) : (empiricalMarginalError data m R batches - Q batches) ^ 2 ≤
      2 * ε ^ 2 * Q batches ^ 2 + 2 * c ^ 2 * E batches ^ 2 := by
    have h := weightedSquare_difference_bounds data
      (fun j => data.populationMarginal (averagedEmpiricalPotential data m R batches) j - data.b j)
      (averagedCategoricalFluctuation data gStar m R batches) ε hε
    have habs : |empiricalMarginalError data m R batches - Q batches| ≤
        ε * Q batches + c * E batches :=
      abs_le.mpr h
    have hs := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at hs
    nlinarith only [hs, sq_nonneg (ε * Q batches - c * E batches)]
  have hQ : MemLp Q 2 (repetitionMeasure data m R) :=
    memLp_categoricalQuadraticError data gStar hm hR
  have hE : MemLp E 2 (repetitionMeasure data m R) :=
    memLp_linearizationSquare data hexact gStar hbalanced hm hR
  have hDiff := ((memLp_empiricalMarginalError data hexact hm R).sub hQ).integrable_sq
  have h := integral_mono hDiff
    ((hQ.integrable_sq.const_mul (2 * ε ^ 2)).add (hE.integrable_sq.const_mul (2 * c ^ 2))) hpoint
  simp only [Pi.add_apply] at h
  rw [integral_add (hQ.integrable_sq.const_mul _) (hE.integrable_sq.const_mul _),
    integral_const_mul, integral_const_mul] at h
  exact h

private theorem uniformLittleO_of_twoTermBound (rmax : ℕ) {A : ℝ} (hA : 0 ≤ A)
    (f e : ℕ → ℕ → ℝ) (scale : ℕ → ℝ)
    (he : IsUniformLittleOInM rmax e scale)
    (hbound : ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧
      ∀ m : ℕ, 0 < m → ∀ R : ℕ, 1 ≤ R → R ≤ rmax →
        |f m R| ≤ ε * A * |scale m| + c * |e m R|) :
    IsUniformLittleOInM rmax f scale := by
  intro δ hδ
  let ε := δ / (2 * (A + 1))
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hεeq : ε * (2 * (A + 1)) = δ := div_mul_cancel₀ _ (by positivity)
  have hεA : ε * A ≤ δ / 2 := by nlinarith
  obtain ⟨c, hc, hfc⟩ := hbound ε hε
  obtain ⟨M, hM⟩ := he (δ / (2 * c)) (by positivity)
  refine ⟨max M 1, ?_⟩
  intro m hm R hR hRmax
  have hmpos : 0 < m := Nat.zero_lt_one.trans_le ((le_max_right M 1).trans hm)
  have hsmall := hM m ((le_max_left M 1).trans hm) R hR hRmax
  have hceq : c * (δ / (2 * c)) = δ / 2 := by field_simp
  calc
    |f m R| ≤ ε * A * |scale m| + c * |e m R| := hfc m hmpos R hR hRmax
    _ ≤ ε * A * |scale m| + c * ((δ / (2 * c)) * |scale m|) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsmall hc.le)
    _ = ε * A * |scale m| + (δ / 2) * |scale m| := by rw [← mul_assoc, hceq]
    _ ≤ (δ / 2) * |scale m| + (δ / 2) * |scale m| :=
      add_le_add (mul_le_mul_of_nonneg_right hεA (abs_nonneg _)) le_rfl
    _ = δ * |scale m| := by ring

theorem quadraticErrorDifferenceEnergy_uniformLittleO_of_fourth (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    (hbalanced : data.populationMarginal gStar = data.b)
    (hfourth : IsUniformLittleOInM data.rmax (linearizationFourthEnergy data gStar)
      (fun m => 1 / (m : ℝ) ^ 2)) :
    IsUniformLittleOInM data.rmax (quadraticErrorDifferenceEnergy data gStar)
      (fun m => 1 / (m : ℝ) ^ 2) := by
  obtain ⟨A, hA, hproxy⟩ := categorical_fourth_moment_uniform_bound data gStar hbalanced
  apply uniformLittleO_of_twoTermBound data.rmax hA
    (quadraticErrorDifferenceEnergy data gStar) (linearizationFourthEnergy data gStar)
    (fun m => 1 / (m : ℝ) ^ 2) hfourth
  intro ε hε
  let t := min 1 (ε / 2)
  have ht : 0 < t := lt_min (by norm_num) (by positivity)
  have htone : t ≤ 1 := min_le_left _ _
  have hteps : t ≤ ε / 2 := min_le_right _ _
  have hcoeff : 2 * t ^ 2 ≤ ε := by nlinarith
  let c := 2 * (((1 + t) / t) ^ 2)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro m hm R hR _
  have hRpos : 0 < R := Nat.zero_lt_one.trans_le hR
  have hbound := quadraticErrorDifferenceEnergy_le data hexact gStar hbalanced hm hRpos ht
  have hsmall := hproxy hm hR
  have hnonneg : 0 ≤ quadraticErrorDifferenceEnergy data gStar m R :=
    integral_nonneg fun _ => sq_nonneg _
  rw [abs_of_nonneg hnonneg]
  calc
    quadraticErrorDifferenceEnergy data gStar m R ≤
        2 * t ^ 2 * (∫ batches, (categoricalQuadraticError data gStar m R batches) ^ 2
          ∂repetitionMeasure data m R) + c * linearizationFourthEnergy data gStar m R := hbound
    _ ≤ 2 * t ^ 2 * (A * |1 / (m : ℝ) ^ 2|) +
        c * |linearizationFourthEnergy data gStar m R| :=
      add_le_add (mul_le_mul_of_nonneg_left hsmall (by positivity))
        (mul_le_mul_of_nonneg_left (le_abs_self _) hc.le)
    _ ≤ ε * A * |1 / (m : ℝ) ^ 2| +
        c * |linearizationFourthEnergy data gStar m R| := by
      apply add_le_add _ le_rfl
      have h := mul_le_mul_of_nonneg_right hcoeff
        (mul_nonneg hA (abs_nonneg (1 / (m : ℝ) ^ 2)))
      convert h using 1
      ring

theorem variance_asymptotic_of_quadraticErrorDifferenceEnergy (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    (hbalanced : data.populationMarginal gStar = data.b)
    (hdifference : IsUniformLittleOInM data.rmax (quadraticErrorDifferenceEnergy data gStar)
      (fun m => 1 / (m : ℝ) ^ 2)) :
    IsUniformLittleOInM data.rmax
      (fun m R => data.varianceError m R - helloSDOTVarianceLeading data.n m R)
      (fun m => 1 / (m : ℝ) ^ 2) := by
  obtain ⟨A, hA, hproxy⟩ := categorical_fourth_moment_uniform_bound data gStar hbalanced
  have htransfer : IsUniformLittleOInM data.rmax
      (fun m R => data.varianceError m R -
        variance (categoricalQuadraticError data gStar m R) (repetitionMeasure data m R))
      (fun m => 1 / (m : ℝ) ^ 2) := by
    apply uniformLittleO_of_twoTermBound data.rmax hA _
      (quadraticErrorDifferenceEnergy data gStar) (fun m => 1 / (m : ℝ) ^ 2) hdifference
    intro ε hε
    let c := (1 + ε) / ε
    have hc : 0 < c := by dsimp [c]; positivity
    refine ⟨c, hc, ?_⟩
    intro m hm R hR _
    have hRpos : 0 < R := Nat.zero_lt_one.trans_le hR
    have hQmem := memLp_categoricalQuadraticError data gStar hm hRpos
    have hvarproxy : variance (categoricalQuadraticError data gStar m R)
        (repetitionMeasure data m R) ≤ A * |1 / (m : ℝ) ^ 2| :=
      (variance_le_expectation_sq hQmem.aestronglyMeasurable).trans (hproxy hm hR)
    have hscaled : ε * variance (categoricalQuadraticError data gStar m R)
        (repetitionMeasure data m R) ≤ ε * A * |1 / (m : ℝ) ^ 2| := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hvarproxy hε.le
    exact (varianceError_comparison data hexact gStar hm hRpos hε).trans
      (add_le_add hscaled
        (mul_le_mul_of_nonneg_left (le_abs_self _) hc.le))
  have hcategory := categorical_variance_asymptotic data gStar hbalanced
  intro δ hδ
  obtain ⟨M₁, hM₁⟩ := htransfer (δ / 2) (by positivity)
  obtain ⟨M₂, hM₂⟩ := hcategory (δ / 2) (by positivity)
  refine ⟨max M₁ M₂, ?_⟩
  intro m hm R hR hRmax
  have h₁ := hM₁ m ((le_max_left _ _).trans hm) R hR hRmax
  have h₂ := hM₂ m ((le_max_right _ _).trans hm) R hR hRmax
  have htri := abs_add_le
    (data.varianceError m R - variance (categoricalQuadraticError data gStar m R)
      (repetitionMeasure data m R))
    (variance (categoricalQuadraticError data gStar m R) (repetitionMeasure data m R) -
      helloSDOTVarianceLeading data.n m R)
  dsimp only at h₁ h₂ ⊢
  simp only [sub_add_sub_cancel] at htri
  linarith

theorem variance_asymptotic_of_linearizationFourthEnergy (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    (hbalanced : data.populationMarginal gStar = data.b)
    (hfourth : IsUniformLittleOInM data.rmax (linearizationFourthEnergy data gStar)
      (fun m => 1 / (m : ℝ) ^ 2)) :
    IsUniformLittleOInM data.rmax
      (fun m R => data.varianceError m R - helloSDOTVarianceLeading data.n m R)
      (fun m => 1 / (m : ℝ) ^ 2) :=
  variance_asymptotic_of_quadraticErrorDifferenceEnergy data hexact gStar hbalanced
    (quadraticErrorDifferenceEnergy_uniformLittleO_of_fourth data hexact gStar hbalanced hfourth)

end DualGuided2026
