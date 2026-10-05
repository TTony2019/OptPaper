import TheoremLib.Dual_guided_2026.HELLO

/-!
# The empirical semi-discrete OT experiment of Appendix F

The population marginal is the mass of the Laguerre partition with the
smallest-index tie rule. Each empirical solve uses an iid source batch and
an independent solver seed; repetitions have the finite product law.
The mean and variance are computed from the population marginal error of
the gauge-aligned averaged potential, as in equation (5) and Appendix F.

Finite-dimensional real inner-product spaces with their Borel structure
represent the Euclidean ambient space of the paper. The oracle remains
unspecified, but its output must be a measurable exact empirical maximizer
almost surely. Taking the seed space to be `Unit` covers deterministic solves.
-/

namespace DualGuided2026

open MeasureTheory
open scoped BigOperators

/-- Fixed population data and an empirical OT oracle. The seed space `Ω`
allows internal solver randomness independent of the source samples. -/
structure HELLOSDOTData (X Ω : Type*) [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [FiniteDimensional ℝ X]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω] where
  n : ℕ
  rmax : ℕ
  targetSites : Fin n → X
  targetSites_injective : Function.Injective targetSites
  b : Fin n → ℝ
  b_pos : ∀ j, 0 < b j
  b_sum : ∑ j, b j = 1
  sourceMeasure : Measure X
  sourceProbability : IsProbabilityMeasure sourceMeasure
  solverMeasure : ℕ → Measure Ω
  solverProbability : ∀ m, IsProbabilityMeasure (solverMeasure m)
  empiricalPotential : (m : ℕ) → (Fin m → X) → Ω → Fin n → ℝ
  epsilon : ℝ
  rmax_pos : 0 < rmax

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

instance (data : HELLOSDOTData X Ω) : IsProbabilityMeasure data.sourceMeasure :=
  data.sourceProbability

instance (data : HELLOSDOTData X Ω) (m : ℕ) :
    IsProbabilityMeasure (data.solverMeasure m) :=
  data.solverProbability m

/-- The gauge used for target dual potentials. -/
def IsBGauge (data : HELLOSDOTData X Ω) (g : Fin data.n → ℝ) : Prop :=
  ∑ j, data.b j * g j = 0

/-- The tangent space of the centered gauge. -/
def IsBGaugeDirection (data : HELLOSDOTData X Ω) (u : Fin data.n → ℝ) : Prop :=
  ∑ j, data.b j * u j = 0

/-- The squared-Euclidean cost to a fixed target site. -/
def sdCost (data : HELLOSDOTData X Ω) (x : X) (j : Fin data.n) : ℝ :=
  ‖x - data.targetSites j‖ ^ 2

/-- A Laguerre cell. Strict comparisons with smaller indices assign every
tie to the smallest index among the minimizers. -/
def laguerreCell (data : HELLOSDOTData X Ω) (g : Fin data.n → ℝ)
    (j : Fin data.n) : Set X :=
  {x | (∀ k, sdCost data x j - g j ≤ sdCost data x k - g k) ∧
    ∀ k, k < j → sdCost data x j - g j < sdCost data x k - g k}

/-- The population mass vector `p(g) = (μ(Lⱼ(g)))ⱼ`. -/
noncomputable def HELLOSDOTData.populationMarginal (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j : Fin data.n) : ℝ :=
  (data.sourceMeasure (laguerreCell data g j)).toReal

/-- Equation (5): the chi-square population marginal error. -/
noncomputable def populationMarginalError (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) : ℝ :=
  ∑ j, (data.populationMarginal g j - data.b j) ^ 2 / data.b j

/-- The empirical semi-discrete dual objective in Appendix F. -/
noncomputable def empiricalSemiDualObjective (data : HELLOSDOTData X Ω)
    {m : ℕ} (samples : Fin m → X)
    (g : Fin data.n → ℝ) : ℝ :=
  ∑ j, data.b j * g j + (1 / (m : ℝ)) *
    ∑ i, sInf (Set.range fun j => sdCost data (samples i) j - g j)

/-- An exact maximizer of the empirical semi-discrete dual objective. -/
def IsEmpiricalDualMaximizer (data : HELLOSDOTData X Ω)
    {m : ℕ} (samples : Fin m → X)
    (g : Fin data.n → ℝ) : Prop :=
  IsBGauge data g ∧
    ∀ g', IsBGauge data g' →
      empiricalSemiDualObjective data samples g' ≤
        empiricalSemiDualObjective data samples g

/-- The gauge alignment in Algorithm 7, line 6. -/
def centerPotential (data : HELLOSDOTData X Ω) (g : Fin data.n → ℝ) :
    Fin data.n → ℝ :=
  fun j => g j - ∑ k, data.b k * g k

theorem centerPotential_isBGauge (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) : IsBGauge data (centerPotential data g) := by
  simp only [IsBGauge, centerPotential, mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, data.b_sum, one_mul, sub_self]

/-- `μ^m`, the law of the iid source samples in one batch. -/
noncomputable def sourceBatchMeasure (data : HELLOSDOTData X Ω) (m : ℕ) :
    Measure (Fin m → X) :=
  Measure.pi fun _ => data.sourceMeasure

/-- One batch together with independent internal solver randomness. -/
noncomputable def empiricalBatchMeasure (data : HELLOSDOTData X Ω) (m : ℕ) :
    Measure ((Fin m → X) × Ω) :=
  (sourceBatchMeasure data m).prod (data.solverMeasure m)

instance (data : HELLOSDOTData X Ω) (m : ℕ) :
    IsProbabilityMeasure (sourceBatchMeasure data m) := by
  unfold sourceBatchMeasure
  infer_instance

instance (data : HELLOSDOTData X Ω) (m : ℕ) :
    IsProbabilityMeasure (empiricalBatchMeasure data m) := by
  unfold empiricalBatchMeasure
  infer_instance

/-- The normalized single-batch estimator `Gₘ` in Appendix F. -/
def empiricalBatchPotential (data : HELLOSDOTData X Ω) (m : ℕ)
    (batch : (Fin m → X) × Ω) : Fin data.n → ℝ :=
  centerPotential data (data.empiricalPotential m batch.1 batch.2)

/-- The law of `R` independent copies of the complete batch experiment. -/
noncomputable def repetitionMeasure (data : HELLOSDOTData X Ω) (m R : ℕ) :
    Measure (Fin R → ((Fin m → X) × Ω)) :=
  Measure.pi fun _ => empiricalBatchMeasure data m

instance (data : HELLOSDOTData X Ω) (m R : ℕ) :
    IsProbabilityMeasure (repetitionMeasure data m R) := by
  unfold repetitionMeasure
  infer_instance

/-- Algorithm 7, line 8: `Gₘ,ᴿ = R⁻¹ ∑ᵣ Gₘ⁽ʳ⁾`. -/
noncomputable def averagedEmpiricalPotential (data : HELLOSDOTData X Ω) (m R : ℕ)
    (batches : Fin R → ((Fin m → X) × Ω)) : Fin data.n → ℝ :=
  fun j => (1 / (R : ℝ)) * ∑ r, empiricalBatchPotential data m (batches r) j

/-- The random variable `Φ(Gₘ,ᴿ)` on the independent repetition space. -/
noncomputable def empiricalMarginalError (data : HELLOSDOTData X Ω) (m R : ℕ)
    (batches : Fin R → ((Fin m → X) × Ω)) : ℝ :=
  populationMarginalError data (averagedEmpiricalPotential data m R batches)

/-- The actual expectation of `Φ(Gₘ,ᴿ)`, rather than an unconstrained field. -/
noncomputable def HELLOSDOTData.meanError (data : HELLOSDOTData X Ω) (m R : ℕ) : ℝ :=
  ∫ batches, empiricalMarginalError data m R batches ∂repetitionMeasure data m R

/-- The actual variance of `Φ(Gₘ,ᴿ)` under the same independent sampling law. -/
noncomputable def HELLOSDOTData.varianceError (data : HELLOSDOTData X Ω)
    (m R : ℕ) : ℝ :=
  ProbabilityTheory.variance (empiricalMarginalError data m R) (repetitionMeasure data m R)

/-- The normalized direction between two target sites. -/
noncomputable def targetUnitDirection (data : HELLOSDOTData X Ω) (i j : Fin data.n) : X :=
  (‖data.targetSites j - data.targetSites i‖)⁻¹ •
    (data.targetSites j - data.targetSites i)

/-- Assumption F.1, together with the local `C²` condition of Theorem F.2:
a moment of real order
`q₀ > 2`, the pairwise boundary anti-concentration estimate, a balanced
population potential, and positive curvature on the gauge subspace.
The explicit sum of squares is the Euclidean squared norm in (31). -/
def HasHELLOSDOTRegularity (data : HELLOSDOTData X Ω) : Prop :=
  ∃ q₀ : ℝ, 2 < q₀ ∧
    (∫⁻ x, ENNReal.ofReal (Real.rpow ‖x‖ q₀) ∂data.sourceMeasure) < ⊤ ∧
    ∃ Cac : ℝ, ∃ lambda : ℝ, 0 ≤ Cac ∧ 0 < lambda ∧
      (∀ i j, i ≠ j → ∀ t : ℝ, ∀ s : ℝ, 0 < s →
        data.sourceMeasure
            {x | |inner ℝ (targetUnitDirection data i j) x - t| ≤ s} ≤
          ENNReal.ofReal (Cac * s)) ∧
      ∃ gStar : Fin data.n → ℝ,
        ∃ J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ),
          ∃ U : Set (Fin data.n → ℝ),
            IsBGauge data gStar ∧ data.populationMarginal gStar = data.b ∧
              IsOpen U ∧ gStar ∈ U ∧
              ContDiffOn ℝ 2 data.populationMarginal U ∧
              HasFDerivAt data.populationMarginal J gStar ∧
              (∀ u, IsBGaugeDirection data u →
                lambda * (∑ i, (u i) ^ 2) ≤ ∑ i, u i * (J u) i)

/-- The strengthened Appendix F moment condition used for the variance
asymptotic. -/
def HasStrengthenedMoment (data : HELLOSDOTData X Ω) : Prop :=
  ∃ q₀ : ℝ, 4 < q₀ ∧
    (∫⁻ x, ENNReal.ofReal (Real.rpow ‖x‖ q₀) ∂data.sourceMeasure) < ⊤

/-- Zero tolerance and a measurable oracle whose gauge-aligned output is
an exact empirical maximizer almost surely under the batch-and-seed law,
for every positive batch size, as in Appendix F (29). -/
def HasExactEmpiricalOTSolves (data : HELLOSDOTData X Ω) : Prop :=
  data.epsilon = 0 ∧
    (∀ {m : ℕ}, 0 < m → Measurable fun batch : (Fin m → X) × Ω =>
      data.empiricalPotential m batch.1 batch.2) ∧
    (∀ {m : ℕ}, 0 < m → ∀ᵐ batch ∂empiricalBatchMeasure data m,
      IsEmpiricalDualMaximizer data batch.1 (empiricalBatchPotential data m batch))

theorem measurableSet_jointLaguerreCell (data : HELLOSDOTData X Ω)
    (j : Fin data.n) :
    MeasurableSet {z : (Fin data.n → ℝ) × X | z.2 ∈ laguerreCell data z.1 j} := by
  have hscore (k : Fin data.n) :
      Measurable fun z : (Fin data.n → ℝ) × X => sdCost data z.2 k - z.1 k := by
    unfold sdCost
    fun_prop
  change MeasurableSet {z : (Fin data.n → ℝ) × X |
    (∀ k, sdCost data z.2 j - z.1 j ≤ sdCost data z.2 k - z.1 k) ∧
      ∀ k, k < j → sdCost data z.2 j - z.1 j < sdCost data z.2 k - z.1 k}
  simp only [Set.setOf_and, Set.setOf_forall]
  exact (MeasurableSet.iInter fun k => measurableSet_le (hscore j) (hscore k)).inter
    (MeasurableSet.iInter fun k => MeasurableSet.iInter fun (_hk : k < j) =>
      measurableSet_lt (hscore j) (hscore k))

theorem measurable_populationMarginal (data : HELLOSDOTData X Ω) :
    Measurable data.populationMarginal := by
  apply measurable_pi_iff.mpr
  intro j
  exact (measurable_measure_prodMk_left (ν := data.sourceMeasure)
    (measurableSet_jointLaguerreCell data j)).ennreal_toReal

theorem measurable_populationMarginalError (data : HELLOSDOTData X Ω) :
    Measurable (populationMarginalError data) := by
  have hp := measurable_populationMarginal data
  unfold populationMarginalError
  fun_prop

theorem populationMarginal_nonneg (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j : Fin data.n) : 0 ≤ data.populationMarginal g j :=
  ENNReal.toReal_nonneg

theorem populationMarginal_le_one (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (j : Fin data.n) : data.populationMarginal g j ≤ 1 := by
  have h := ENNReal.toReal_mono (measure_ne_top data.sourceMeasure Set.univ)
    (measure_mono (Set.subset_univ (laguerreCell data g j)))
  simpa [HELLOSDOTData.populationMarginal] using h

theorem populationMarginalError_nonneg (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) : 0 ≤ populationMarginalError data g := by
  exact Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (data.b_pos j).le

/-- A fixed bound, independent of the potential or batch size. -/
theorem populationMarginalError_le (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) :
    populationMarginalError data g ≤ ∑ j, (1 + data.b j) ^ 2 / data.b j := by
  apply Finset.sum_le_sum
  intro j _
  have habs : |data.populationMarginal g j - data.b j| ≤ 1 + data.b j := by
    calc
      |data.populationMarginal g j - data.b j| ≤
          |data.populationMarginal g j| + |data.b j| := abs_sub _ _
      _ ≤ 1 + data.b j := by
        rw [abs_of_nonneg (populationMarginal_nonneg data g j), abs_of_pos (data.b_pos j)]
        linarith [populationMarginal_le_one data g j]
  have hsq : (data.populationMarginal g j - data.b j) ^ 2 ≤ (1 + data.b j) ^ 2 := by
    simpa only [← sq, sq_abs] using mul_self_le_mul_self (abs_nonneg _) habs
  exact div_le_div_of_nonneg_right hsq (data.b_pos j).le

theorem measurable_empiricalBatchPotential (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) {m : ℕ} (hm : 0 < m) :
    Measurable (empiricalBatchPotential data m) := by
  have hg := hexact.2.1 hm
  unfold empiricalBatchPotential centerPotential
  fun_prop

theorem measurable_averagedEmpiricalPotential (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) {m : ℕ} (hm : 0 < m) (R : ℕ) :
    Measurable (averagedEmpiricalPotential data m R) := by
  have hg := measurable_empiricalBatchPotential data hexact hm
  unfold averagedEmpiricalPotential
  fun_prop

theorem measurable_empiricalMarginalError (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) {m : ℕ} (hm : 0 < m) (R : ℕ) :
    Measurable (empiricalMarginalError data m R) :=
  (measurable_populationMarginalError data).comp
    (measurable_averagedEmpiricalPotential data hexact hm R)

/-- The random marginal error has finite second moment, so its expectation
and variance are the usual probabilistic quantities. -/
theorem memLp_empiricalMarginalError (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) {m : ℕ} (hm : 0 < m) (R : ℕ) :
    MemLp (empiricalMarginalError data m R) 2 (repetitionMeasure data m R) := by
  apply MemLp.of_bound (measurable_empiricalMarginalError data hexact hm R).aestronglyMeasurable
    (∑ j, (1 + data.b j) ^ 2 / data.b j)
  filter_upwards [] with batches
  unfold empiricalMarginalError
  rw [Real.norm_eq_abs, abs_of_nonneg (populationMarginalError_nonneg data _)]
  exact populationMarginalError_le data _

/-- The normalized batch estimators are independent, including their
internal solver randomness, under the repetition law. -/
theorem independent_empiricalBatchPotentials (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) {m : ℕ} (hm : 0 < m) (R : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun r : Fin R => fun batches => empiricalBatchPotential data m (batches r))
      (repetitionMeasure data m R) := by
  exact ProbabilityTheory.iIndepFun_pi
    (fun _ => (measurable_empiricalBatchPotential data hexact hm).aemeasurable)

/-- Uniform little-o in the batch size, with the repetition count restricted
to the fixed finite range `1 ≤ R ≤ rmax`. -/
def IsUniformLittleOInM (rmax : ℕ) (f : ℕ → ℕ → ℝ)
    (scale : ℕ → ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
    ∀ R : ℕ, 1 ≤ R → R ≤ rmax → |f m R| ≤ δ * |scale m|

/-- The leading term in the expectation from Theorem III.1. -/
noncomputable def helloSDOTMeanLeading (n m R : ℕ) : ℝ :=
  ((n : ℝ) - 1) / ((m : ℝ) * (R : ℝ))

/-- The leading term in the variance from Theorem III.1. -/
noncomputable def helloSDOTVarianceLeading (n m R : ℕ) : ℝ :=
  2 * ((n : ℝ) - 1) / ((m : ℝ) ^ 2 * (R : ℝ) ^ 2)

theorem laguerreCell_eq_univ_of_one_target (data : HELLOSDOTData X Ω)
    (hn : data.n = 1) (g : Fin data.n → ℝ) (j : Fin data.n) :
    laguerreCell data g j = Set.univ := by
  have hsub : Subsingleton (Fin data.n) := by rw [hn]; infer_instance
  letI := hsub
  ext x
  simp only [laguerreCell, Set.mem_setOf_eq, Set.mem_univ, iff_true]
  constructor
  · intro k
    have hk : k = j := Subsingleton.elim _ _
    simp [hk]
  · intro k hk
    have heq : k = j := Subsingleton.elim _ _
    subst k
    exact (lt_irrefl j hk).elim

theorem b_eq_one_of_one_target (data : HELLOSDOTData X Ω)
    (hn : data.n = 1) (j : Fin data.n) : data.b j = 1 := by
  have hsub : Subsingleton (Fin data.n) := by rw [hn]; infer_instance
  letI := hsub
  have hsum : (∑ k, data.b k) = data.b j := by
    apply Finset.sum_eq_single j
    · intro k _ hkj
      exact (hkj (Subsingleton.elim _ _)).elim
    · simp
  exact hsum.symm.trans data.b_sum

theorem populationMarginalError_zero_of_one_target (data : HELLOSDOTData X Ω)
    (hn : data.n = 1) (g : Fin data.n → ℝ) : populationMarginalError data g = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  simp [HELLOSDOTData.populationMarginal, laguerreCell_eq_univ_of_one_target data hn,
    b_eq_one_of_one_target data hn]

theorem meanError_zero_of_one_target (data : HELLOSDOTData X Ω)
    (hn : data.n = 1) (m R : ℕ) : data.meanError m R = 0 := by
  simp [HELLOSDOTData.meanError, empiricalMarginalError,
    populationMarginalError_zero_of_one_target data hn]

theorem varianceError_zero_of_one_target (data : HELLOSDOTData X Ω)
    (hn : data.n = 1) (m R : ℕ) : data.varianceError m R = 0 := by
  have herr : empiricalMarginalError data m R = 0 := by
    funext batches
    exact populationMarginalError_zero_of_one_target data hn _
  simp [HELLOSDOTData.varianceError, herr, ProbabilityTheory.variance_zero]

/-- The degenerate one-target case requires no asymptotic remainder estimates. -/
theorem theorem_3_1_single_target (data : HELLOSDOTData X Ω) (hn : data.n = 1) :
    IsUniformLittleOInM data.rmax
      (fun m R => data.meanError m R - helloSDOTMeanLeading data.n m R)
      (fun m => 1 / (m : ℝ)) ∧
    IsUniformLittleOInM data.rmax
      (fun m R => data.varianceError m R - helloSDOTVarianceLeading data.n m R)
      (fun m => 1 / (m : ℝ) ^ 2) := by
  constructor
  · intro δ hδ
    refine ⟨0, ?_⟩
    intro m hm R hR hRmax
    simp only [meanError_zero_of_one_target data hn, helloSDOTMeanLeading, hn,
      Nat.cast_one, sub_self, zero_div, abs_zero]
    exact mul_nonneg hδ.le (abs_nonneg _)
  · intro δ hδ
    refine ⟨0, ?_⟩
    intro m hm R hR hRmax
    simp only [varianceError_zero_of_one_target data hn, helloSDOTVarianceLeading, hn,
      Nat.cast_one, sub_self, mul_zero, zero_div, abs_zero]
    exact mul_nonneg hδ.le (abs_nonneg _)

end DualGuided2026
