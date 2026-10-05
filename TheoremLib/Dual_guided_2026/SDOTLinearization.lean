import TheoremLib.Dual_guided_2026.SDOTMovingCells

/-!
# The expectation reduction in Appendix F

The remainder below is defined from the actual population marginal and
categorical fluctuations. Its smallness is not assumed in `theorem_3_1`.
The comparison inequality isolates the estimate required by Proposition F.4.
-/

namespace DualGuided2026

open MeasureTheory
open scoped BigOperators

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

noncomputable def weightedSquare (data : HELLOSDOTData X Ω) (u : Fin data.n → ℝ) : ℝ :=
  ∑ j, (u j) ^ 2 / data.b j

theorem batchCategoricalFluctuation_eq_empiricalCellMass (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) {m : ℕ} (hm : 0 < m) (batch : (Fin m → X) × Ω)
    (j : Fin data.n) :
    batchCategoricalFluctuation data g m batch j =
      empiricalCellMass data batch.1 g j - data.populationMarginal g j := by
  unfold batchCategoricalFluctuation sourceCategoricalFluctuation
    empiricalCellMass iidAverage centeredCellIndicator
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

/-- The actual population Taylor remainder `Δpop,m` from Appendix F (35). -/
noncomputable def populationLinearizationRemainder (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (g : Fin data.n → ℝ) : Fin data.n → ℝ :=
  data.populationMarginal g - data.populationMarginal gStar - J (g - gStar)

/-- The actual empirical-process remainder `Δemp,m`, evaluated at the
sample-dependent potential. -/
noncomputable def movingCellEmpiricalRemainder (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) {m : ℕ} (samples : Fin m → X)
    (g : Fin data.n → ℝ) : Fin data.n → ℝ :=
  empiricalCellMass data samples g - empiricalCellMass data samples gStar -
    (data.populationMarginal g - data.populationMarginal gStar)

/-- Appendix F (41): the exact single-batch balance decomposition. -/
theorem empirical_balance_decomposition (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (hbalanced : data.populationMarginal gStar = data.b)
    {m : ℕ} (hm : 0 < m) (batch : (Fin m → X) × Ω) (g : Fin data.n → ℝ) :
    J (g - gStar) + batchCategoricalFluctuation data gStar m batch =
      empiricalTieResidual data batch.1 g - populationLinearizationRemainder data gStar J g -
        movingCellEmpiricalRemainder data gStar batch.1 g := by
  ext j
  simp only [Pi.add_apply, Pi.sub_apply, empiricalTieResidual,
    populationLinearizationRemainder, movingCellEmpiricalRemainder,
    batchCategoricalFluctuation_eq_empiricalCellMass data gStar hm, hbalanced]
  ring

/-- The unique remainder making Appendix F (38) hold. -/
noncomputable def marginalLinearizationRemainder (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (m R : ℕ)
    (batches : Fin R → ((Fin m → X) × Ω)) (j : Fin data.n) : ℝ :=
  data.populationMarginal (averagedEmpiricalPotential data m R batches) j - data.b j +
    averagedCategoricalFluctuation data gStar m R batches j

noncomputable def linearizationEnergy (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (m R : ℕ) : ℝ :=
  ∫ batches, weightedSquare data (marginalLinearizationRemainder data gStar m R batches)
    ∂repetitionMeasure data m R

/-- The actual remainder in (38) equals the average of the three single-batch
remainders plus the population Taylor remainder of the averaged potential.
Thus the tie term proved in `SDOTTies` is a term of the master remainder. -/
theorem marginalLinearizationRemainder_decomposition (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (hbalanced : data.populationMarginal gStar = data.b)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R)
    (batches : Fin R → ((Fin m → X) × Ω)) :
    marginalLinearizationRemainder data gStar m R batches =
      averagedEmpiricalTieResidual data m R batches -
        (fun j => iidAverage (fun batch => populationLinearizationRemainder data gStar J
          (empiricalBatchPotential data m batch) j) R batches) -
        (fun j => iidAverage (fun batch => movingCellEmpiricalRemainder data gStar batch.1
          (empiricalBatchPotential data m batch) j) R batches) +
        populationLinearizationRemainder data gStar J
          (averagedEmpiricalPotential data m R batches) := by
  have hJ : J (averagedEmpiricalPotential data m R batches - gStar) =
      (R : ℝ)⁻¹ • ∑ r, J (empiricalBatchPotential data m (batches r) - gStar) := by
    rw [← map_sum, ← map_smul]
    congr 1
    ext j
    simp only [averagedEmpiricalPotential, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, one_div]
    have hRreal : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
    field_simp
  have hbalance (r : Fin R) := empirical_balance_decomposition data gStar J hbalanced hm
    (batches r) (empiricalBatchPotential data m (batches r))
  ext j
  have hJj := congrFun hJ j
  simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at hJj
  have hsum := congrArg (fun u : Fin R → ℝ => ∑ r, u r)
    (funext fun r => congrFun (hbalance r) j)
  simp only [Pi.add_apply, Pi.sub_apply, Finset.sum_add_distrib,
    Finset.sum_sub_distrib] at hsum
  simp only [populationLinearizationRemainder, Pi.sub_apply, hbalanced] at hsum
  have hscaled := congrArg (fun x : ℝ => (R : ℝ)⁻¹ * x) hsum
  simp only [marginalLinearizationRemainder, averagedEmpiricalTieResidual,
    averagedCategoricalFluctuation, iidAverage, Pi.add_apply, Pi.sub_apply,
    populationLinearizationRemainder, hbalanced, one_div]
  nlinarith only [hJj, hscaled]

theorem memLp_marginalDeviation (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) {m : ℕ} (hm : 0 < m) (R : ℕ)
    (j : Fin data.n) :
    MemLp (fun batches => data.populationMarginal
      (averagedEmpiricalPotential data m R batches) j - data.b j) 2
      (repetitionMeasure data m R) := by
  have hp := measurable_populationMarginal data
  have hg := measurable_averagedEmpiricalPotential data hexact hm R
  have hmeas : Measurable fun batches => data.populationMarginal
      (averagedEmpiricalPotential data m R batches) j - data.b j := by fun_prop
  apply MemLp.of_bound hmeas.aestronglyMeasurable (1 + data.b j)
  filter_upwards [] with batches
  rw [Real.norm_eq_abs]
  calc
    |data.populationMarginal (averagedEmpiricalPotential data m R batches) j - data.b j| ≤
        |data.populationMarginal (averagedEmpiricalPotential data m R batches) j| +
          |data.b j| := abs_sub _ _
    _ ≤ 1 + data.b j := by
      rw [abs_of_nonneg (populationMarginal_nonneg data _ j), abs_of_pos (data.b_pos j)]
      linarith [populationMarginal_le_one data (averagedEmpiricalPotential data m R batches) j]

theorem memLp_marginalLinearizationRemainder (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    {m : ℕ} (hm : 0 < m) (R : ℕ) (j : Fin data.n) :
    MemLp (fun batches => marginalLinearizationRemainder data gStar m R batches j) 2
      (repetitionMeasure data m R) :=
  (memLp_marginalDeviation data hexact hm R j).add
    (memLp_averagedCategoricalFluctuation data gStar m R j)

theorem integrable_linearizationSquare (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    {m : ℕ} (hm : 0 < m) (R : ℕ) :
    Integrable (fun batches => weightedSquare data
      (marginalLinearizationRemainder data gStar m R batches)) (repetitionMeasure data m R) :=
  integrable_finset_sum Finset.univ fun j _ =>
    (memLp_marginalLinearizationRemainder data hexact gStar hm R j).integrable_sq.div_const _

theorem linearizationEnergy_nonneg (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (m R : ℕ) : 0 ≤ linearizationEnergy data gStar m R :=
  integral_nonneg fun _ => Finset.sum_nonneg fun j _ =>
    div_nonneg (sq_nonneg _) (data.b_pos j).le

private theorem sq_difference_bounds (z η ε : ℝ) (hε : 0 < ε) :
    -(ε * z ^ 2 + ((1 + ε) / ε) * η ^ 2) ≤ (η - z) ^ 2 - z ^ 2 ∧
      (η - z) ^ 2 - z ^ 2 ≤ ε * z ^ 2 + ((1 + ε) / ε) * η ^ 2 := by
  have hconvert : (ε ^ 2 * z ^ 2 + (1 + ε) * η ^ 2) / ε =
      ε * z ^ 2 + ((1 + ε) / ε) * η ^ 2 := by
    field_simp
  have hupper : (η - z) ^ 2 - z ^ 2 ≤ (ε ^ 2 * z ^ 2 + (1 + ε) * η ^ 2) / ε := by
    apply (le_div_iff₀ hε).mpr
    nlinarith [sq_nonneg (ε * z + η)]
  have hlower : -((ε ^ 2 * z ^ 2 + (1 + ε) * η ^ 2) / ε) ≤ (η - z) ^ 2 - z ^ 2 := by
    rw [← neg_div]
    apply (div_le_iff₀ hε).mpr
    nlinarith [sq_nonneg (ε * z - η), mul_nonneg hε.le (sq_nonneg η)]
  rw [hconvert] at hupper hlower
  exact ⟨hlower, hupper⟩

theorem weightedSquare_difference_bounds (data : HELLOSDOTData X Ω)
    (x z : Fin data.n → ℝ) (ε : ℝ) (hε : 0 < ε) :
    -(ε * weightedSquare data z + ((1 + ε) / ε) *
      weightedSquare data (fun j => x j + z j)) ≤ weightedSquare data x - weightedSquare data z ∧
    weightedSquare data x - weightedSquare data z ≤ ε * weightedSquare data z +
      ((1 + ε) / ε) * weightedSquare data (fun j => x j + z j) := by
  have hscalar (j : Fin data.n) := sq_difference_bounds (z j) (x j + z j) ε hε
  simp only [add_sub_cancel_right] at hscalar
  have hlower (j : Fin data.n) :
      -(ε * ((z j) ^ 2 / data.b j) + ((1 + ε) / ε) * ((x j + z j) ^ 2 / data.b j)) ≤
        (x j) ^ 2 / data.b j - (z j) ^ 2 / data.b j := by
    convert div_le_div_of_nonneg_right (hscalar j).1 (data.b_pos j).le using 1 <;> ring
  have hupper (j : Fin data.n) :
      (x j) ^ 2 / data.b j - (z j) ^ 2 / data.b j ≤
        ε * ((z j) ^ 2 / data.b j) + ((1 + ε) / ε) * ((x j + z j) ^ 2 / data.b j) := by
    convert div_le_div_of_nonneg_right (hscalar j).2 (data.b_pos j).le using 1 <;> ring
  constructor
  · simpa only [weightedSquare, Finset.sum_sub_distrib, Finset.sum_neg_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum] using
      Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hlower j)
  · simpa only [weightedSquare, Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum] using Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hupper j)

/-- A Young-inequality version of the Cauchy--Schwarz comparison in the
proof of Theorem F.2. -/
theorem meanError_comparison (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    (hbalanced : data.populationMarginal gStar = data.b)
    {m R : ℕ} (hm : 0 < m) (hR : 0 < R) (ε : ℝ) (hε : 0 < ε) :
    |data.meanError m R - helloSDOTMeanLeading data.n m R| ≤
      ε * helloSDOTMeanLeading data.n m R + ((1 + ε) / ε) *
        linearizationEnergy data gStar m R := by
  let Z := fun batches =>
    weightedSquare data (averagedCategoricalFluctuation data gStar m R batches)
  let E := fun batches =>
    weightedSquare data (marginalLinearizationRemainder data gStar m R batches)
  have hZ : Integrable Z (repetitionMeasure data m R) :=
    integrable_finset_sum Finset.univ fun j _ =>
      (memLp_averagedCategoricalFluctuation data gStar m R j).integrable_sq.div_const _
  have hE : Integrable E (repetitionMeasure data m R) :=
    integrable_linearizationSquare data hexact gStar hm R
  have hΦ := (memLp_empiricalMarginalError data hexact hm R).integrable (by norm_num)
  have hsecond : (∫ batches, Z batches ∂repetitionMeasure data m R) =
      helloSDOTMeanLeading data.n m R := categorical_second_moment data gStar hbalanced hm hR
  have hdiff : (∫ batches, empiricalMarginalError data m R batches - Z batches
      ∂repetitionMeasure data m R) = data.meanError m R - helloSDOTMeanLeading data.n m R := by
    rw [integral_sub hΦ hZ, hsecond]
    rfl
  have hbound : (∫ batches, ε * Z batches + ((1 + ε) / ε) * E batches
      ∂repetitionMeasure data m R) = ε * helloSDOTMeanLeading data.n m R +
        ((1 + ε) / ε) * linearizationEnergy data gStar m R := by
    rw [integral_add (hZ.const_mul _) (hE.const_mul _), integral_const_mul,
      integral_const_mul, hsecond]
    rfl
  have hpoint (batches) := weightedSquare_difference_bounds data
    (fun j => data.populationMarginal (averagedEmpiricalPotential data m R batches) j - data.b j)
    (averagedCategoricalFluctuation data gStar m R batches) ε hε
  apply abs_le.mpr
  constructor
  · have hmono := integral_mono ((hZ.const_mul ε).add (hE.const_mul ((1 + ε) / ε))).neg
      (hΦ.sub hZ) (fun batches => (hpoint batches).1)
    simp only [Pi.neg_apply, Pi.add_apply, Pi.sub_apply] at hmono
    rw [integral_neg, hdiff, hbound] at hmono
    exact hmono
  · have hmono := integral_mono (hΦ.sub hZ)
      ((hZ.const_mul ε).add (hE.const_mul ((1 + ε) / ε))) (fun batches => (hpoint batches).2)
    simp only [Pi.add_apply, Pi.sub_apply] at hmono
    rw [hdiff, hbound] at hmono
    exact hmono

private theorem uniformLittleO_of_youngBound (rmax : ℕ) (A : ℝ) (hA : 0 ≤ A)
    (f e : ℕ → ℕ → ℝ)
    (he : IsUniformLittleOInM rmax e (fun m => 1 / (m : ℝ)))
    (hbound : ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, 0 < m → ∀ R : ℕ,
      1 ≤ R → R ≤ rmax →
      |f m R| ≤ ε * A * |1 / (m : ℝ)| + ((1 + ε) / ε) * |e m R|) :
    IsUniformLittleOInM rmax f (fun m => 1 / (m : ℝ)) := by
  intro δ hδ
  let ε := δ / (2 * (A + 1))
  have hε : 0 < ε := div_pos hδ (by positivity)
  let C := (1 + ε) / ε
  have hC : 0 < C := div_pos (by linarith) hε
  have hεeq : ε * (2 * (A + 1)) = δ := div_mul_cancel₀ _ (by positivity)
  have hεA : ε * A ≤ δ / 2 := by nlinarith
  have hτ : 0 < δ / (2 * C) := div_pos hδ (by positivity)
  obtain ⟨M, hM⟩ := he (δ / (2 * C)) hτ
  have hCτ : C * (δ / (2 * C)) = δ / 2 := by
    field_simp
  refine ⟨max M 1, ?_⟩
  intro m hm R hR hRmax
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right M 1).trans hm)
  have hsmall := hM m ((le_max_left M 1).trans hm) R hR hRmax
  calc
    |f m R| ≤ ε * A * |1 / (m : ℝ)| + C * |e m R| := hbound ε hε m hmpos R hR hRmax
    _ ≤ ε * A * |1 / (m : ℝ)| + C * ((δ / (2 * C)) * |1 / (m : ℝ)|) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hsmall hC.le)
    _ = ε * A * |1 / (m : ℝ)| + (δ / 2) * |1 / (m : ℝ)| := by rw [← mul_assoc, hCτ]
    _ ≤ (δ / 2) * |1 / (m : ℝ)| + (δ / 2) * |1 / (m : ℝ)| :=
      add_le_add (mul_le_mul_of_nonneg_right hεA (abs_nonneg _)) le_rfl
    _ = δ * |1 / (m : ℝ)| := by ring

theorem helloSDOTMeanLeading_le (n : ℕ) {m R : ℕ} (hm : 0 < m) (hR : 1 ≤ R) :
    helloSDOTMeanLeading n m R ≤ |(n : ℝ) - 1| * |1 / (m : ℝ)| := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hRreal : (1 : ℝ) ≤ R := by exact_mod_cast hR
  have hden : (m : ℝ) ≤ (m : ℝ) * R := by nlinarith
  have hdenpos : (0 : ℝ) < (m : ℝ) * R := hmreal.trans_le hden
  have hrecip := one_div_le_one_div_of_le hmreal hden
  calc
    helloSDOTMeanLeading n m R ≤ |(n : ℝ) - 1| / ((m : ℝ) * R) :=
      div_le_div_of_nonneg_right (le_abs_self _) hdenpos.le
    _ ≤ |(n : ℝ) - 1| / (m : ℝ) := by
      simpa only [div_eq_mul_inv, one_mul] using
        mul_le_mul_of_nonneg_left hrecip (abs_nonneg ((n : ℝ) - 1))
    _ = |(n : ℝ) - 1| * |1 / (m : ℝ)| := by
      rw [abs_of_pos (one_div_pos.mpr hmreal)]
      ring

/-- The expectation conclusion follows once the actual remainder energy
satisfies Proposition F.4 (39). The original theorem still has to establish
that estimate from its regularity and exact-solve hypotheses. -/
theorem mean_asymptotic_of_linearizationEnergy (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    (hbalanced : data.populationMarginal gStar = data.b)
    (henergy : IsUniformLittleOInM data.rmax (linearizationEnergy data gStar)
      (fun m => 1 / (m : ℝ))) :
    IsUniformLittleOInM data.rmax
      (fun m R => data.meanError m R - helloSDOTMeanLeading data.n m R)
      (fun m => 1 / (m : ℝ)) := by
  apply uniformLittleO_of_youngBound data.rmax |(data.n : ℝ) - 1| (abs_nonneg _)
    _ _ henergy
  intro ε hε m hm R hR hRmax
  have hC : 0 ≤ (1 + ε) / ε := le_of_lt (div_pos (by linarith) hε)
  calc
    |data.meanError m R - helloSDOTMeanLeading data.n m R| ≤
        ε * helloSDOTMeanLeading data.n m R + ((1 + ε) / ε) *
          linearizationEnergy data gStar m R :=
      meanError_comparison data hexact gStar hbalanced hm (lt_of_lt_of_le Nat.zero_lt_one hR) ε hε
    _ ≤ ε * (|(data.n : ℝ) - 1| * |1 / (m : ℝ)|) + ((1 + ε) / ε) *
        |linearizationEnergy data gStar m R| :=
      add_le_add (mul_le_mul_of_nonneg_left (helloSDOTMeanLeading_le data.n hm hR) hε.le)
        (mul_le_mul_of_nonneg_left (le_abs_self _) hC)
    _ = ε * |(data.n : ℝ) - 1| * |1 / (m : ℝ)| + ((1 + ε) / ε) *
        |linearizationEnergy data gStar m R| := by ring

end DualGuided2026
