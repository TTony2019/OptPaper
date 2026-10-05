import TheoremLib.Dual_guided_2026.SDOTLinearization

/-!
# Population linearization remainder

The local/remote partition used in Lemma F.6 only needs differentiability:
the local remainder is smaller than any prescribed multiple of the potential
error, and the remote contribution is controlled by its second-moment tail.
-/

namespace DualGuided2026

open MeasureTheory
open scoped BigOperators

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

noncomputable def inverseWeightSum (data : HELLOSDOTData X Ω) : ℝ :=
  ∑ j, 1 / data.b j

theorem inverseWeightSum_nonneg (data : HELLOSDOTData X Ω) :
    0 ≤ inverseWeightSum data :=
  Finset.sum_nonneg fun j _ => div_nonneg zero_le_one (data.b_pos j).le

theorem weightedSquare_le_norm_sq (data : HELLOSDOTData X Ω) (u : Fin data.n → ℝ) :
    weightedSquare data u ≤ inverseWeightSum data * ‖u‖ ^ 2 := by
  have hcoord (j : Fin data.n) : (u j) ^ 2 ≤ ‖u‖ ^ 2 := by
    have hj := norm_le_pi_norm u j
    rw [Real.norm_eq_abs] at hj
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (u j)) (norm_nonneg u)).2 hj
  calc
    weightedSquare data u ≤ ∑ j, ‖u‖ ^ 2 / data.b j :=
      Finset.sum_le_sum fun j _ => div_le_div_of_nonneg_right (hcoord j) (data.b_pos j).le
    _ = inverseWeightSum data * ‖u‖ ^ 2 := by
      simp only [inverseWeightSum, Finset.sum_mul]
      congr 1
      ext j
      ring

theorem populationMarginal_norm_le_one (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) : ‖data.populationMarginal g‖ ≤ 1 := by
  exact pi_norm_le_iff_of_nonneg zero_le_one |>.mpr fun j => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (populationMarginal_nonneg data g j)] using
      populationMarginal_le_one data g j

theorem populationLinearizationRemainder_norm_le (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (g : Fin data.n → ℝ) :
    ‖populationLinearizationRemainder data gStar J g‖ ≤ 2 + ‖J‖ * ‖g - gStar‖ := by
  unfold populationLinearizationRemainder
  calc
    ‖data.populationMarginal g - data.populationMarginal gStar - J (g - gStar)‖ ≤
        ‖data.populationMarginal g - data.populationMarginal gStar‖ + ‖J (g - gStar)‖ :=
      norm_sub_le _ _
    _ ≤ (‖data.populationMarginal g‖ + ‖data.populationMarginal gStar‖) +
        ‖J‖ * ‖g - gStar‖ := add_le_add (norm_sub_le _ _) (J.le_opNorm _)
    _ ≤ 2 + ‖J‖ * ‖g - gStar‖ := by
      linarith [populationMarginal_norm_le_one data g,
        populationMarginal_norm_le_one data gStar]

/-- Differentiability gives the arbitrarily small local squared-remainder bound.
The radius depends on the prescribed coefficient but not on a sample size. -/
theorem populationLinearizationRemainder_local_bound (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (hJ : HasFDerivAt data.populationMarginal J gStar) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ g, ‖g - gStar‖ < r →
      weightedSquare data (populationLinearizationRemainder data gStar J g) ≤
        ε * ‖g - gStar‖ ^ 2 := by
  let W := inverseWeightSum data
  have hW : 0 ≤ W := inverseWeightSum_nonneg data
  let η := Real.sqrt (ε / (W + 1))
  have hη : 0 < η := Real.sqrt_pos.2 (div_pos hε (by positivity))
  have hηsq : η ^ 2 = ε / (W + 1) := Real.sq_sqrt (by positivity)
  have hcoefficient : W * η ^ 2 ≤ ε := by
    rw [hηsq]
    apply (mul_div_assoc W ε (W + 1)).symm ▸ (div_le_iff₀ (by positivity : 0 < W + 1)).mpr
    nlinarith
  have hevent := hJ.isLittleO.bound hη
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hevent
  refine ⟨r, hr, fun g hg => ?_⟩
  have hsmall : ‖populationLinearizationRemainder data gStar J g‖ ≤ η * ‖g - gStar‖ := by
    exact hball (by simpa only [dist_eq_norm] using hg)
  calc
    weightedSquare data (populationLinearizationRemainder data gStar J g) ≤
        W * ‖populationLinearizationRemainder data gStar J g‖ ^ 2 :=
      weightedSquare_le_norm_sq data _
    _ ≤ W * (η * ‖g - gStar‖) ^ 2 := by
      gcongr
    _ = (W * η ^ 2) * ‖g - gStar‖ ^ 2 := by ring
    _ ≤ ε * ‖g - gStar‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcoefficient (sq_nonneg _)

/-- Away from a fixed ball the global boundedness of the mass vector absorbs
the constant term into the potential error. -/
theorem populationLinearizationRemainder_remote_bound (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    {r : ℝ} (hr : 0 < r) (g : Fin data.n → ℝ) (hg : r ≤ ‖g - gStar‖) :
    weightedSquare data (populationLinearizationRemainder data gStar J g) ≤
      (inverseWeightSum data * (2 / r + ‖J‖) ^ 2) * ‖g - gStar‖ ^ 2 := by
  have hlinear : 2 + ‖J‖ * ‖g - gStar‖ ≤ (2 / r + ‖J‖) * ‖g - gStar‖ := by
    have htwo : 2 ≤ (2 / r) * ‖g - gStar‖ := by
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hr).mpr
      nlinarith
    nlinarith
  have hnorm := (populationLinearizationRemainder_norm_le data gStar J g).trans hlinear
  calc
    weightedSquare data (populationLinearizationRemainder data gStar J g) ≤
        inverseWeightSum data * ‖populationLinearizationRemainder data gStar J g‖ ^ 2 :=
      weightedSquare_le_norm_sq data _
    _ ≤ inverseWeightSum data * ((2 / r + ‖J‖) * ‖g - gStar‖) ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (by positivity)).2 hnorm)
        (inverseWeightSum_nonneg data)
    _ = _ := by ring

/-- The `C²` hypothesis of Theorem F.2 gives a fixed quadratic Taylor bound.
It follows by applying the mean-value inequality to the locally Lipschitz
derivative on the ball with radius `‖g - gStar‖`. -/
theorem populationLinearizationRemainder_local_quadratic_bound
    (data : HELLOSDOTData X Ω) (gStar : Fin data.n → ℝ)
    (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    {U : Set (Fin data.n → ℝ)} (hU : IsOpen U) (hgStar : gStar ∈ U)
    (hC2 : ContDiffOn ℝ 2 data.populationMarginal U)
    (hJ : HasFDerivAt data.populationMarginal J gStar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ ∀ g, ‖g - gStar‖ ≤ r →
      ‖populationLinearizationRemainder data gStar J g‖ ≤ C * ‖g - gStar‖ ^ 2 := by
  have hD : ContDiffAt ℝ 1 (fderiv ℝ data.populationMarginal) gStar :=
    (hC2.contDiffAt (hU.mem_nhds hgStar)).fderiv_right (by norm_num)
  obtain ⟨K, T, hT, hLip⟩ := hD.exists_lipschitzOnWith
  obtain ⟨s, hs, hball⟩ := Metric.mem_nhds_iff.1
    (Filter.inter_mem (hU.mem_nhds hgStar) hT)
  let r := s / 2
  have hr : 0 < r := half_pos hs
  have hrlt : r < s := by dsimp [r]; linarith
  have hclosed : Metric.closedBall gStar r ⊆ U ∩ T :=
    (Metric.closedBall_subset_ball hrlt).trans hball
  have hstarT : gStar ∈ T := (hclosed (Metric.mem_closedBall_self hr.le)).2
  refine ⟨K, K.coe_nonneg, r, hr, ?_⟩
  intro g hg
  let a := ‖g - gStar‖
  have ha : 0 ≤ a := norm_nonneg _
  have hsmall : Metric.closedBall gStar a ⊆ Metric.closedBall gStar r :=
    Metric.closedBall_subset_closedBall hg
  have hdiff : ∀ z ∈ Metric.closedBall gStar a,
      DifferentiableAt ℝ data.populationMarginal z := by
    intro z hz
    have hzU := (hclosed (hsmall hz)).1
    exact (hC2.contDiffAt (hU.mem_nhds hzU)).differentiableAt (by norm_num)
  have hderbound : ∀ z ∈ Metric.closedBall gStar a,
      ‖fderiv ℝ data.populationMarginal z - J‖ ≤ (K : ℝ) * a := by
    intro z hz
    have hzT := (hclosed (hsmall hz)).2
    have hK := hLip.dist_le_mul z hzT gStar hstarT
    rw [dist_eq_norm, hJ.fderiv, dist_eq_norm] at hK
    exact hK.trans (mul_le_mul_of_nonneg_left
      (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hz) K.coe_nonneg)
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le' hdiff hderbound
    (convex_closedBall gStar a) (Metric.mem_closedBall_self ha)
    (show g ∈ Metric.closedBall gStar a by simp only [Metric.mem_closedBall, dist_eq_norm]; rfl)
  simpa only [populationLinearizationRemainder, a, pow_two, mul_assoc] using hmv

theorem populationLinearizationRemainder_local_quartic_energy_bound
    (data : HELLOSDOTData X Ω) (gStar : Fin data.n → ℝ)
    (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    {U : Set (Fin data.n → ℝ)} (hU : IsOpen U) (hgStar : gStar ∈ U)
    (hC2 : ContDiffOn ℝ 2 data.populationMarginal U)
    (hJ : HasFDerivAt data.populationMarginal J gStar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧ ∀ g, ‖g - gStar‖ ≤ r →
      weightedSquare data (populationLinearizationRemainder data gStar J g) ≤
        C * ‖g - gStar‖ ^ 4 := by
  obtain ⟨K, hK, r, hr, hbound⟩ :=
    populationLinearizationRemainder_local_quadratic_bound data gStar J hU hgStar hC2 hJ
  refine ⟨inverseWeightSum data * K ^ 2,
    mul_nonneg (inverseWeightSum_nonneg data) (sq_nonneg K), r, hr, fun g hg => ?_⟩
  calc
    weightedSquare data (populationLinearizationRemainder data gStar J g) ≤
        inverseWeightSum data * ‖populationLinearizationRemainder data gStar J g‖ ^ 2 :=
      weightedSquare_le_norm_sq data _
    _ ≤ inverseWeightSum data * (K * ‖g - gStar‖ ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_left
        ((sq_le_sq₀ (norm_nonneg _) (mul_nonneg hK (sq_nonneg _))).2 (hbound g hg))
        (inverseWeightSum_nonneg data)
    _ = _ := by ring

/-- Gauge alignment is performed before averaging. Consequently every
convex norm ball about the population potential is preserved by averaging. -/
theorem averagedEmpiricalPotential_sub_norm_le (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) {m R : ℕ} (hR : 0 < R)
    (batches : Fin R → ((Fin m → X) × Ω)) {r : ℝ}
    (hnear : ∀ k, ‖empiricalBatchPotential data m (batches k) - gStar‖ ≤ r) :
    ‖averagedEmpiricalPotential data m R batches - gStar‖ ≤ r := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast hR
  have hcenter : averagedEmpiricalPotential data m R batches - gStar =
      (R : ℝ)⁻¹ • ∑ k, (empiricalBatchPotential data m (batches k) - gStar) := by
    ext j
    simp only [averagedEmpiricalPotential, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply, one_div]
    field_simp
  rw [hcenter, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hRreal)]
  calc
    (R : ℝ)⁻¹ * ‖∑ k, (empiricalBatchPotential data m (batches k) - gStar)‖ ≤
        (R : ℝ)⁻¹ * ∑ k, ‖empiricalBatchPotential data m (batches k) - gStar‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_pos.mpr hRreal).le
    _ ≤ (R : ℝ)⁻¹ * ∑ _k : Fin R, r :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun k _ => hnear k)
        (inv_pos.mpr hRreal).le
    _ = r := by simp [hRreal.ne']

/-- A common radius for all repetitions gives the quartic bound for the
population remainder of their average, with constants independent of `R`. -/
theorem averagedPopulationRemainder_localization_bound
    (data : HELLOSDOTData X Ω) (gStar : Fin data.n → ℝ)
    (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    {U : Set (Fin data.n → ℝ)} (hU : IsOpen U) (hgStar : gStar ∈ U)
    (hC2 : ContDiffOn ℝ 2 data.populationMarginal U)
    (hJ : HasFDerivAt data.populationMarginal J gStar) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r₀ : ℝ, 0 < r₀ ∧ ∀ {m R : ℕ}, 0 < R →
      ∀ batches : Fin R → ((Fin m → X) × Ω), ∀ {r : ℝ}, 0 ≤ r → r ≤ r₀ →
      (∀ k, ‖empiricalBatchPotential data m (batches k) - gStar‖ ≤ r) →
      weightedSquare data (populationLinearizationRemainder data gStar J
        (averagedEmpiricalPotential data m R batches)) ≤ C * r ^ 4 := by
  obtain ⟨C, hC, r₀, hr₀, hbound⟩ :=
    populationLinearizationRemainder_local_quartic_energy_bound data gStar J hU hgStar hC2 hJ
  refine ⟨C, hC, r₀, hr₀, ?_⟩
  intro m R hR batches r hr hrr₀ hnear
  have haverage := averagedEmpiricalPotential_sub_norm_le data gStar hR batches hnear
  calc
    weightedSquare data (populationLinearizationRemainder data gStar J
        (averagedEmpiricalPotential data m R batches)) ≤
        C * ‖averagedEmpiricalPotential data m R batches - gStar‖ ^ 4 :=
      hbound _ (haverage.trans hrr₀)
    _ ≤ C * r ^ 4 := by gcongr

noncomputable def averagedPotentialSecondMoment (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (m R : ℕ) : ℝ :=
  ∫ batches, ‖averagedEmpiricalPotential data m R batches - gStar‖ ^ 2
    ∂repetitionMeasure data m R

noncomputable def averagedPotentialTailSecondMoment (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (r : ℝ) (m R : ℕ) : ℝ :=
  ∫ batches, if r ≤ ‖averagedEmpiricalPotential data m R batches - gStar‖ then
      ‖averagedEmpiricalPotential data m R batches - gStar‖ ^ 2 else 0
    ∂repetitionMeasure data m R

noncomputable def averagedPopulationRemainderEnergy (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (m R : ℕ) : ℝ :=
  ∫ batches, weightedSquare data (populationLinearizationRemainder data gStar J
      (averagedEmpiricalPotential data m R batches)) ∂repetitionMeasure data m R

theorem averagedPopulationRemainderEnergy_nonneg (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (m R : ℕ) : 0 ≤ averagedPopulationRemainderEnergy data gStar J m R :=
  integral_nonneg fun _ => Finset.sum_nonneg fun j _ =>
    div_nonneg (sq_nonneg _) (data.b_pos j).le

theorem integrable_averagedPopulationRemainderSquare (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ)) {m : ℕ} (hm : 0 < m) (R : ℕ)
    (hsecond : Integrable (fun batches =>
      ‖averagedEmpiricalPotential data m R batches - gStar‖ ^ 2)
      (repetitionMeasure data m R)) :
    Integrable (fun batches => weightedSquare data (populationLinearizationRemainder
      data gStar J (averagedEmpiricalPotential data m R batches)))
      (repetitionMeasure data m R) := by
  have hg := measurable_averagedEmpiricalPotential data hexact hm R
  have hdevmeas : Measurable fun batches =>
      averagedEmpiricalPotential data m R batches - gStar := by fun_prop
  have hdev := (memLp_two_iff_integrable_sq_norm hdevmeas.aestronglyMeasurable).2 hsecond
  have hpmeas : Measurable fun batches =>
      data.populationMarginal (averagedEmpiricalPotential data m R batches) :=
    (measurable_populationMarginal data).comp hg
  have hp : MemLp (fun batches => data.populationMarginal
      (averagedEmpiricalPotential data m R batches)) 2 (repetitionMeasure data m R) :=
    MemLp.of_bound hpmeas.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun batches => populationMarginal_norm_le_one data _)
  have hrem : MemLp (fun batches => populationLinearizationRemainder data gStar J
      (averagedEmpiricalPotential data m R batches)) 2 (repetitionMeasure data m R) :=
    (hp.sub (memLp_const (data.populationMarginal gStar))).sub
      (hdev.continuousLinearMap_comp J)
  have hnormsq := hrem.norm.integrable_sq
  have hmeas : Measurable fun batches => weightedSquare data
      (populationLinearizationRemainder data gStar J
        (averagedEmpiricalPotential data m R batches)) := by
    unfold weightedSquare populationLinearizationRemainder
    fun_prop
  apply (hnormsq.const_mul (inverseWeightSum data)).mono' hmeas.aestronglyMeasurable
  filter_upwards [] with batches
  have hnonneg : 0 ≤ weightedSquare data (populationLinearizationRemainder data gStar J
      (averagedEmpiricalPotential data m R batches)) :=
    Finset.sum_nonneg fun j _ => div_nonneg (sq_nonneg _) (data.b_pos j).le
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact weightedSquare_le_norm_sq data _

/-- The complete local/remote integral partition in Lemma F.6, also valid
for the averaged potential in Proposition F.4. -/
theorem averagedPopulationRemainderEnergy_partition (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ)
    (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (hJ : HasFDerivAt data.populationMarginal J gStar) {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ {m : ℕ}, 0 < m → ∀ R : ℕ,
      Integrable (fun batches =>
        ‖averagedEmpiricalPotential data m R batches - gStar‖ ^ 2)
        (repetitionMeasure data m R) →
      averagedPopulationRemainderEnergy data gStar J m R ≤
        ε * averagedPotentialSecondMoment data gStar m R +
        (inverseWeightSum data * (2 / r + ‖J‖) ^ 2) *
          averagedPotentialTailSecondMoment data gStar r m R := by
  obtain ⟨r, hr, hlocal⟩ := populationLinearizationRemainder_local_bound data gStar J hJ hε
  refine ⟨r, hr, ?_⟩
  intro m hm R hsecond
  let S := fun batches => ‖averagedEmpiricalPotential data m R batches - gStar‖ ^ 2
  let T := fun batches => if r ≤ ‖averagedEmpiricalPotential data m R batches - gStar‖ then
      S batches else 0
  let K := inverseWeightSum data * (2 / r + ‖J‖) ^ 2
  have hg := measurable_averagedEmpiricalPotential data hexact hm R
  have hs : MeasurableSet {batches |
      r ≤ ‖averagedEmpiricalPotential data m R batches - gStar‖} := by
    apply measurableSet_le measurable_const
    fun_prop
  have hT : Integrable T (repetitionMeasure data m R) := by
    simpa only [Set.indicator, Set.mem_setOf_eq] using hsecond.indicator hs
  have hpoint (batches) : weightedSquare data (populationLinearizationRemainder data gStar J
      (averagedEmpiricalPotential data m R batches)) ≤ ε * S batches + K * T batches := by
    by_cases hnear : ‖averagedEmpiricalPotential data m R batches - gStar‖ < r
    · simpa only [T, not_le.mpr hnear, ↓reduceIte, mul_zero, add_zero] using
        hlocal _ hnear
    · have hremote := populationLinearizationRemainder_remote_bound data gStar J hr
        (averagedEmpiricalPotential data m R batches) (le_of_not_gt hnear)
      have hpositive : 0 ≤ ε * S batches := mul_nonneg hε.le (sq_nonneg _)
      simp only [T, le_of_not_gt hnear, ↓reduceIte]
      exact hremote.trans (le_add_of_nonneg_left hpositive)
  have hmono := integral_mono
    (integrable_averagedPopulationRemainderSquare data hexact gStar J hm R hsecond)
    ((hsecond.const_mul ε).add (hT.const_mul K)) hpoint
  simp only [Pi.add_apply] at hmono
  rw [integral_add (hsecond.const_mul ε) (hT.const_mul K), integral_const_mul,
    integral_const_mul] at hmono
  exact hmono

/-- Lemma F.6 and Proposition F.4 (46), with the second-moment and tail
estimates isolated as genuine probabilistic premises. -/
theorem averagedPopulationRemainderEnergy_isUniformLittleO
    (data : HELLOSDOTData X Ω) (hexact : HasExactEmpiricalOTSolves data)
    (gStar : Fin data.n → ℝ) (J : (Fin data.n → ℝ) →L[ℝ] (Fin data.n → ℝ))
    (hJ : HasFDerivAt data.populationMarginal J gStar)
    (hsecond : ∀ {m : ℕ}, 0 < m → ∀ R : ℕ, Integrable (fun batches =>
      ‖averagedEmpiricalPotential data m R batches - gStar‖ ^ 2)
        (repetitionMeasure data m R))
    {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ {m : ℕ}, 0 < m → ∀ R : ℕ, 1 ≤ R → R ≤ data.rmax →
      averagedPotentialSecondMoment data gStar m R ≤ C * |1 / (m : ℝ)|)
    (htail : ∀ r : ℝ, 0 < r → IsUniformLittleOInM data.rmax
      (averagedPotentialTailSecondMoment data gStar r) (fun m => 1 / (m : ℝ))) :
    IsUniformLittleOInM data.rmax (averagedPopulationRemainderEnergy data gStar J)
      (fun m => 1 / (m : ℝ)) := by
  intro δ hδ
  let ε := δ / (2 * (C + 1))
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hεC : ε * C ≤ δ / 2 := by
    have heq : ε * (2 * (C + 1)) = δ := div_mul_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨r, hr, hpartition⟩ :=
    averagedPopulationRemainderEnergy_partition data hexact gStar J hJ hε
  let K := inverseWeightSum data * (2 / r + ‖J‖) ^ 2
  have hK : 0 ≤ K := mul_nonneg (inverseWeightSum_nonneg data) (sq_nonneg _)
  let τ := δ / (2 * (K + 1))
  have hτ : 0 < τ := div_pos hδ (by positivity)
  have hKτ : K * τ ≤ δ / 2 := by
    have heq : τ * (2 * (K + 1)) = δ := div_mul_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨M, hM⟩ := htail r hr τ hτ
  refine ⟨max M 1, ?_⟩
  intro m hm R hR hRmax
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right M 1).trans hm)
  have hsmall := hM m ((le_max_left M 1).trans hm) R hR hRmax
  rw [abs_of_nonneg (averagedPopulationRemainderEnergy_nonneg data gStar J m R)]
  have htail_nonneg : 0 ≤ averagedPotentialTailSecondMoment data gStar r m R :=
    integral_nonneg fun _ => by split <;> positivity
  calc
    averagedPopulationRemainderEnergy data gStar J m R ≤
        ε * averagedPotentialSecondMoment data gStar m R +
          K * averagedPotentialTailSecondMoment data gStar r m R :=
      hpartition hmpos R (hsecond hmpos R)
    _ ≤ ε * (C * |1 / (m : ℝ)|) + K * (τ * |1 / (m : ℝ)|) :=
      add_le_add (mul_le_mul_of_nonneg_left (hbound hmpos R hR hRmax) hε.le)
        (mul_le_mul_of_nonneg_left
          (by simpa only [abs_of_nonneg htail_nonneg] using hsmall) hK)
    _ = (ε * C) * |1 / (m : ℝ)| + (K * τ) * |1 / (m : ℝ)| := by ring
    _ ≤ (δ / 2) * |1 / (m : ℝ)| + (δ / 2) * |1 / (m : ℝ)| :=
      add_le_add (mul_le_mul_of_nonneg_right hεC (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hKτ (abs_nonneg _))
    _ = δ * |1 / (m : ℝ)| := by ring

end DualGuided2026
