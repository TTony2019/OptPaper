import TheoremLib.Dual_guided_2026.SDOTGeometry

/-!
# The empirical tie residual of Lemma F.5

An exact empirical maximizer can be perturbed in every direction after gauge
alignment. Untied rows keep their minimizing site under a sufficiently small
perturbation; tied rows contribute at most twice the perturbation size.
-/

namespace DualGuided2026

open MeasureTheory
open scoped BigOperators

theorem integral_iidAverage_sq_le {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (f : A → ℝ) (hf : MemLp f 2 μ)
    {R : ℕ} (hR : 1 ≤ R) :
    (∫ samples, (iidAverage f R samples) ^ 2 ∂Measure.pi (fun _ : Fin R => μ)) ≤
      ∫ x, (f x) ^ 2 ∂μ := by
  have hRpos : 0 < R := lt_of_lt_of_le Nat.zero_lt_one hR
  have hvar := ProbabilityTheory.variance_eq_sub hf
  have hvarAvg := ProbabilityTheory.variance_eq_sub (memLp_iidAverage μ hf R)
  have hmean := integral_iidAverage μ hf hRpos
  simp only [Pi.pow_apply] at hvar hvarAvg
  rw [hmean, variance_iidAverage μ hf hRpos] at hvarAvg
  have hle := div_le_self (ProbabilityTheory.variance_nonneg f μ)
    (show (1 : ℝ) ≤ R by exact_mod_cast hR)
  linarith

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

noncomputable def laguerreAssignment (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (x : X) : Fin data.n :=
  (exists_unique_laguerreCell data g x).choose

theorem laguerreAssignment_mem (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (x : X) : x ∈ laguerreCell data g (laguerreAssignment data g x) :=
  (exists_unique_laguerreCell data g x).choose_spec.1

theorem cellIndicator_eq_assignment (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (x : X) (j : Fin data.n) :
    cellIndicator data g j x = if laguerreAssignment data g x = j then 1 else 0 := by
  classical
  have hiff : x ∈ laguerreCell data g j ↔ laguerreAssignment data g x = j := by
    constructor
    · intro hj
      exact ((exists_unique_laguerreCell data g x).choose_spec.2 j hj).symm
    · intro hj
      rw [← hj]
      exact laguerreAssignment_mem data g x
  simp only [cellIndicator, Set.indicator_apply, hiff]

theorem sum_cellIndicator_mul (data : HELLOSDOTData X Ω)
    (g v : Fin data.n → ℝ) (x : X) :
    ∑ j, cellIndicator data g j x * v j = v (laguerreAssignment data g x) := by
  classical
  simp only [cellIndicator_eq_assignment]
  simp

theorem semiDualMinimum_eq_active (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (x : X) {j : Fin data.n} (hj : IsActiveTarget data x g j) :
    sInf (Set.range fun k => sdCost data x k - g k) = sdCost data x j - g j := by
  exact (show IsLeast (Set.range fun k => sdCost data x k - g k)
    (sdCost data x j - g j) from
      ⟨Set.mem_range_self j, by rintro _ ⟨k, rfl⟩; exact hj k⟩).csInf_eq

theorem empiricalSemiDualObjective_center (data : HELLOSDOTData X Ω)
    {m : ℕ} (hm : 0 < m) (samples : Fin m → X) (g : Fin data.n → ℝ) :
    empiricalSemiDualObjective data samples (centerPotential data g) =
      empiricalSemiDualObjective data samples g := by
  classical
  let c := ∑ j, data.b j * g j
  have hmin (k : Fin m) :
      sInf (Set.range fun j => sdCost data (samples k) j - centerPotential data g j) =
        sInf (Set.range fun j => sdCost data (samples k) j - g j) + c := by
    let j := laguerreAssignment data g (samples k)
    have hj := (laguerreAssignment_mem data g (samples k)).1
    have hj' : IsActiveTarget data (samples k) (centerPotential data g) j := by
      intro i
      dsimp only [centerPotential]
      linarith [hj i]
    rw [semiDualMinimum_eq_active data _ _ hj', semiDualMinimum_eq_active data _ _ hj]
    dsimp only [centerPotential, c]
    ring
  unfold empiricalSemiDualObjective
  rw [show (∑ j, data.b j * centerPotential data g j) = 0 from
    centerPotential_isBGauge data g]
  simp_rw [hmin]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  change 0 + (1 / (m : ℝ)) * (_ + (m : ℝ) * c) = c + (1 / (m : ℝ)) * _
  field_simp
  ring

theorem IsEmpiricalDualMaximizer.le_objective (data : HELLOSDOTData X Ω)
    {m : ℕ} (hm : 0 < m) {samples : Fin m → X} {g : Fin data.n → ℝ}
    (hg : IsEmpiricalDualMaximizer data samples g) (g' : Fin data.n → ℝ) :
    empiricalSemiDualObjective data samples g' ≤ empiricalSemiDualObjective data samples g := by
  have h := hg.2 (centerPotential data g') (centerPotential_isBGauge data g')
  rwa [empiricalSemiDualObjective_center data hm] at h

/-- The actual empirical mass with the same tie convention as the population
cells, and the residual `ρₘ = Pₘ a(·; Gₘ) - b`. -/
noncomputable def empiricalCellMass (data : HELLOSDOTData X Ω) {m : ℕ}
    (samples : Fin m → X) (g : Fin data.n → ℝ) (j : Fin data.n) : ℝ :=
  iidAverage (cellIndicator data g j) m samples

noncomputable def empiricalTieResidual (data : HELLOSDOTData X Ω) {m : ℕ}
    (samples : Fin m → X) (g : Fin data.n → ℝ) (j : Fin data.n) : ℝ :=
  empiricalCellMass data samples g j - data.b j

theorem sum_empiricalCellMass_mul (data : HELLOSDOTData X Ω) {m : ℕ}
    (samples : Fin m → X) (g v : Fin data.n → ℝ) :
    ∑ j, empiricalCellMass data samples g j * v j =
      (1 / (m : ℝ)) * ∑ k, v (laguerreAssignment data g (samples k)) := by
  simp only [empiricalCellMass, iidAverage]
  simp_rw [mul_assoc, Finset.sum_mul]
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp_rw [sum_cellIndicator_mul]

/-- A finite family of strictly positive gaps has a common positive lower
bound, including when some comparisons are ties. -/
theorem exists_small_score_perturbation {ι κ : Type*} [Finite ι] [Finite κ]
    (score : ι → κ → ℝ) (a : ι → κ) :
    ∃ t : ℝ, 0 < t ∧ ∀ k j, score k (a k) < score k j →
      2 * t < score k j - score k (a k) := by
  classical
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite κ
  let d : ι × κ → ℝ := fun p =>
    if score p.1 (a p.1) < score p.1 p.2 then
      score p.1 p.2 - score p.1 (a p.1) else 1
  let D := insert 1 (Finset.univ.image d)
  have hD : D.Nonempty := Finset.insert_nonempty _ _
  have hpos (x : ℝ) (hx : x ∈ D) : 0 < x := by
    rcases Finset.mem_insert.mp hx with rfl | hx
    · norm_num
    · obtain ⟨⟨k, j⟩, _, rfl⟩ := Finset.mem_image.mp hx
      dsimp only [d]
      split_ifs with h
      · exact sub_pos.mpr h
      · norm_num
  refine ⟨D.min' hD / 4, div_pos (hpos _ (D.min'_mem hD)) (by norm_num), ?_⟩
  intro k j hj
  have hmem : score k j - score k (a k) ∈ D := by
    apply Finset.mem_insert_of_mem
    exact Finset.mem_image.mpr ⟨(k, j), Finset.mem_univ _, by simp [d, hj]⟩
  have hle := D.min'_le _ hmem
  have := hpos _ (D.min'_mem hD)
  linarith

theorem strict_score_of_not_tied (data : HELLOSDOTData X Ω) {m : ℕ}
    (samples : Fin m → X) (g : Fin data.n → ℝ) {k : Fin m}
    (hk : k ∉ empiricalTieRows data samples g) {j : Fin data.n}
    (hj : j ≠ laguerreAssignment data g (samples k)) :
    sdCost data (samples k) (laguerreAssignment data g (samples k)) -
      g (laguerreAssignment data g (samples k)) < sdCost data (samples k) j - g j := by
  classical
  have ha := (laguerreAssignment_mem data g (samples k)).1
  apply lt_of_le_of_ne (ha j)
  intro heq
  apply hk
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, j, laguerreAssignment data g (samples k), hj, ?_, ha⟩
  intro i
  rw [← heq]
  exact ha i

/-- Optimality bounds the empirical mass imbalance against every direction
whose coordinates have absolute value at most one. -/
theorem empiricalTieResidual_direction_bound (data : HELLOSDOTData X Ω)
    {m : ℕ} (hm : 0 < m) (samples : Fin m → X) (g : Fin data.n → ℝ)
    (hg : IsEmpiricalDualMaximizer data samples g) (v : Fin data.n → ℝ)
    (hv : ∀ j, |v j| ≤ 1) :
    -(∑ j, empiricalTieResidual data samples g j * v j) ≤
      2 * (empiricalTieRows data samples g).card / (m : ℝ) := by
  classical
  let a := fun k => laguerreAssignment data g (samples k)
  let score := fun k j => sdCost data (samples k) j - g j
  let T := empiricalTieRows data samples g
  let e : Fin m → ℝ := fun k => if k ∈ T then 1 else 0
  obtain ⟨t, ht, hsmall⟩ := exists_small_score_perturbation score a
  have hperturb (k : Fin m) :
      sInf (Set.range fun j => sdCost data (samples k) j - (g j + t * v j)) ≥
        score k (a k) - t * v (a k) - 2 * t * e k := by
    apply le_csInf ⟨_, Set.mem_range_self (a k)⟩
    rintro _ ⟨j, rfl⟩
    have ha : score k (a k) ≤ score k j := (laguerreAssignment_mem data g (samples k)).1 j
    have hva := abs_le.mp (hv (a k))
    have hvj := abs_le.mp (hv j)
    by_cases hk : k ∈ T
    · simp only [e, if_pos hk]
      dsimp only [score] at ha ⊢
      nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hva.1),
        mul_nonneg ht.le (sub_nonneg.mpr hvj.2)]
    · simp only [e, if_neg hk, mul_zero, sub_zero]
      by_cases hj : j = a k
      · subst j
        dsimp only [score]
        linarith
      · have hstrict := strict_score_of_not_tied data samples g hk hj
        have hgap := hsmall k j hstrict
        dsimp only [score] at hgap ⊢
        nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hva.1),
          mul_nonneg ht.le (sub_nonneg.mpr hvj.2)]
  have he : ∑ k, e k = (T.card : ℝ) := by
    simp only [e]
    rw [← Finset.sum_filter]
    simp
  have hmin (k : Fin m) :
      sInf (Set.range fun j => sdCost data (samples k) j - g j) = score k (a k) :=
    semiDualMinimum_eq_active data g _ (laguerreAssignment_mem data g (samples k)).1
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hsum := mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hperturb k))
    (show 0 ≤ 1 / (m : ℝ) by positivity)
  have hopt := hg.le_objective data hm (fun j => g j + t * v j)
  unfold empiricalSemiDualObjective at hopt
  simp_rw [hmin] at hopt
  simp only [mul_add, Finset.sum_add_distrib] at hopt
  have hweights : (∑ j, data.b j * (t * v j)) = t * ∑ j, data.b j * v j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hweights] at hopt
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, he] at hsum
  have hstationary : (∑ j, data.b j * v j) -
      (1 / (m : ℝ)) * ∑ k, v (a k) ≤ 2 * T.card / (m : ℝ) := by
    apply (mul_le_mul_iff_right₀ ht).mp
    simp only [div_eq_mul_inv, one_mul] at hopt hsum ⊢
    nlinarith
  rw [← sum_empiricalCellMass_mul data samples g v] at hstationary
  simp only [empiricalTieResidual, sub_mul, Finset.sum_sub_distrib]
  convert hstationary using 1
  ring

/-- Lemma F.5 (51), before applying the almost-sure bound on tied rows. -/
theorem empiricalTieResidual_l1_le_tieCount (data : HELLOSDOTData X Ω)
    {m : ℕ} (hm : 0 < m) (samples : Fin m → X) (g : Fin data.n → ℝ)
    (hg : IsEmpiricalDualMaximizer data samples g) :
    ∑ j, |empiricalTieResidual data samples g j| ≤
      2 * (empiricalTieRows data samples g).card / (m : ℝ) := by
  classical
  let v : Fin data.n → ℝ := fun j =>
    if 0 ≤ empiricalTieResidual data samples g j then -1 else 1
  have hv (j : Fin data.n) : |v j| ≤ 1 := by
    dsimp only [v]
    split_ifs <;> norm_num
  have h := empiricalTieResidual_direction_bound data hm samples g hg v hv
  rw [← Finset.sum_neg_distrib] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [v]
  split_ifs with hj
  · rw [abs_of_nonneg hj]
    ring
  · rw [abs_of_neg (lt_of_not_ge hj)]
    ring

/-- The simultaneous deterministic form of Lemma F.5 (51). -/
theorem empiricalTieResidual_l1_le (data : HELLOSDOTData X Ω)
    {m : ℕ} (hm : 0 < m) (samples : Fin m → X)
    (hdistinct : PairwiseCostDistinct data samples) (g : Fin data.n → ℝ)
    (hg : IsEmpiricalDualMaximizer data samples g) :
    ∑ j, |empiricalTieResidual data samples g j| ≤ 2 * (data.n.choose 2) / (m : ℝ) := by
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  exact (empiricalTieResidual_l1_le_tieCount data hm samples g hg).trans
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (by exact_mod_cast empiricalTieRows_card_le data samples hdistinct g)
      (by norm_num)) hmreal.le)

/-- Lemma F.5 (51) for the actual batch oracle. -/
theorem ae_empiricalTieResidual_l1_le (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (hexact : HasExactEmpiricalOTSolves data)
    {m : ℕ} (hm : 0 < m) :
    ∀ᵐ batch ∂empiricalBatchMeasure data m,
      ∑ j, |empiricalTieResidual data batch.1 (empiricalBatchPotential data m batch) j| ≤
        2 * (data.n.choose 2) / (m : ℝ) := by
  filter_upwards [ae_pairwiseCostDistinct_batch data hregular m, hexact.2.2 hm]
    with batch hdistinct hg
  exact empiricalTieResidual_l1_le data hm batch.1 hdistinct _ hg

theorem measurable_jointCellIndicator (data : HELLOSDOTData X Ω) (j : Fin data.n) :
    Measurable fun z : (Fin data.n → ℝ) × X => cellIndicator data z.1 j z.2 := by
  convert (measurable_const : Measurable fun _ : (Fin data.n → ℝ) × X => (1 : ℝ)).indicator
    (measurableSet_jointLaguerreCell data j) using 1

theorem measurable_batchTieResidual (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) {m : ℕ} (hm : 0 < m) (j : Fin data.n) :
    Measurable fun batch : (Fin m → X) × Ω =>
      empiricalTieResidual data batch.1 (empiricalBatchPotential data m batch) j := by
  have hpotential := measurable_empiricalBatchPotential data hexact hm
  have hi (k : Fin m) : Measurable fun batch : (Fin m → X) × Ω =>
      cellIndicator data (empiricalBatchPotential data m batch) j (batch.1 k) :=
    (measurable_jointCellIndicator data j).comp
      (hpotential.prodMk ((measurable_pi_apply k).comp measurable_fst))
  unfold empiricalTieResidual empiricalCellMass iidAverage
  fun_prop

theorem abs_batchTieResidual_le (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (hexact : HasExactEmpiricalOTSolves data)
    {m : ℕ} (hm : 0 < m) (j : Fin data.n) :
    ∀ᵐ batch ∂empiricalBatchMeasure data m,
      |empiricalTieResidual data batch.1 (empiricalBatchPotential data m batch) j| ≤
        2 * (data.n.choose 2) / (m : ℝ) := by
  filter_upwards [ae_empiricalTieResidual_l1_le data hregular hexact hm] with batch hbatch
  exact (Finset.single_le_sum (fun k _ => abs_nonneg
    (empiricalTieResidual data batch.1 (empiricalBatchPotential data m batch) k))
      (Finset.mem_univ j)).trans hbatch

theorem memLp_batchTieResidual (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (hexact : HasExactEmpiricalOTSolves data)
    {m : ℕ} (hm : 0 < m) (j : Fin data.n) :
    MemLp (fun batch => empiricalTieResidual data batch.1 (empiricalBatchPotential data m batch) j)
      2 (empiricalBatchMeasure data m) := by
  apply MemLp.of_bound (measurable_batchTieResidual data hexact hm j).aestronglyMeasurable
    (2 * (data.n.choose 2) / (m : ℝ))
  simpa only [Real.norm_eq_abs] using abs_batchTieResidual_le data hregular hexact hm j

noncomputable def empiricalTieEnergy (data : HELLOSDOTData X Ω) (m : ℕ) : ℝ :=
  ∫ batch, ∑ j,
    (empiricalTieResidual data batch.1 (empiricalBatchPotential data m batch) j) ^ 2 / data.b j
      ∂empiricalBatchMeasure data m

theorem empiricalTieEnergy_nonneg (data : HELLOSDOTData X Ω) (m : ℕ) :
    0 ≤ empiricalTieEnergy data m :=
  integral_nonneg fun _ => Finset.sum_nonneg fun j _ =>
    div_nonneg (sq_nonneg _) (data.b_pos j).le

/-- Lemma F.5 (52), with an explicit constant independent of the batch size. -/
theorem empiricalTieEnergy_le (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (hexact : HasExactEmpiricalOTSolves data)
    {m : ℕ} (hm : 0 < m) :
    empiricalTieEnergy data m ≤
      (2 * (data.n.choose 2 : ℝ)) ^ 2 * (∑ j, 1 / data.b j) / (m : ℝ) ^ 2 := by
  have hint := integrable_finset_sum Finset.univ (fun j _ =>
    (memLp_batchTieResidual data hregular hexact hm j).integrable_sq.div_const (data.b j))
  have hpoint : ∀ᵐ batch ∂empiricalBatchMeasure data m,
      (∑ j, (empiricalTieResidual data batch.1 (empiricalBatchPotential data m batch) j) ^ 2 /
        data.b j) ≤ (2 * (data.n.choose 2) / (m : ℝ)) ^ 2 * ∑ j, 1 / data.b j := by
    have hall : ∀ᵐ batch ∂empiricalBatchMeasure data m, ∀ j,
        |empiricalTieResidual data batch.1 (empiricalBatchPotential data m batch) j| ≤
          2 * (data.n.choose 2) / (m : ℝ) :=
      ae_all_iff.mpr (abs_batchTieResidual_le data hregular hexact hm)
    filter_upwards [hall] with batch hbatch
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hs := mul_self_le_mul_self (abs_nonneg _) (hbatch j)
    rw [← sq, sq_abs, ← sq] at hs
    simpa only [div_eq_mul_inv, one_mul] using
      div_le_div_of_nonneg_right hs (data.b_pos j).le
  have h := integral_mono_ae hint (integrable_const _) hpoint
  simp only [integral_const, probReal_univ, one_smul] at h
  convert h using 1
  rw [div_pow]
  ring

/-- The tie term is already of lower order than the `m⁻¹` expectation scale. -/
theorem empiricalTieEnergy_uniformLittleO (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (hexact : HasExactEmpiricalOTSolves data) :
    IsUniformLittleOInM data.rmax (fun m _ => empiricalTieEnergy data m)
      (fun m => 1 / (m : ℝ)) := by
  let K := (2 * (data.n.choose 2 : ℝ)) ^ 2 * (∑ j, 1 / data.b j)
  intro δ hδ
  obtain ⟨M, hM⟩ := exists_nat_gt (K / δ)
  refine ⟨max M 1, ?_⟩
  intro m hm R hR hRmax
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right M 1).trans hm)
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hMm : (M : ℝ) ≤ m := by exact_mod_cast (le_max_left M 1).trans hm
  have hKm : K ≤ δ * (m : ℝ) := by
    have hdiv := hM.trans_le hMm
    exact (div_le_iff₀ hδ).mp hdiv.le |>.trans_eq (mul_comm _ _)
  rw [abs_of_nonneg (empiricalTieEnergy_nonneg data m),
    abs_of_pos (one_div_pos.mpr hmreal)]
  calc
    empiricalTieEnergy data m ≤ K / (m : ℝ) ^ 2 := empiricalTieEnergy_le data hregular hexact hmpos
    _ = (K / (m : ℝ)) * (1 / (m : ℝ)) := by ring
    _ ≤ δ * (1 / (m : ℝ)) := mul_le_mul_of_nonneg_right
      ((div_le_iff₀ hmreal).mpr hKm) (by positivity)

noncomputable def averagedEmpiricalTieResidual (data : HELLOSDOTData X Ω) (m R : ℕ)
    (batches : Fin R → ((Fin m → X) × Ω)) (j : Fin data.n) : ℝ :=
  iidAverage (fun batch =>
    empiricalTieResidual data batch.1 (empiricalBatchPotential data m batch) j) R batches

noncomputable def averagedEmpiricalTieEnergy (data : HELLOSDOTData X Ω) (m R : ℕ) : ℝ :=
  ∫ batches, ∑ j, (averagedEmpiricalTieResidual data m R batches j) ^ 2 / data.b j
    ∂repetitionMeasure data m R

theorem memLp_averagedEmpiricalTieResidual (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (hexact : HasExactEmpiricalOTSolves data)
    {m : ℕ} (hm : 0 < m) (R : ℕ) (j : Fin data.n) :
    MemLp (fun batches => averagedEmpiricalTieResidual data m R batches j) 2
      (repetitionMeasure data m R) :=
  memLp_iidAverage (empiricalBatchMeasure data m)
    (memLp_batchTieResidual data hregular hexact hm j) R

theorem averagedEmpiricalTieEnergy_nonneg (data : HELLOSDOTData X Ω) (m R : ℕ) :
    0 ≤ averagedEmpiricalTieEnergy data m R :=
  integral_nonneg fun _ => Finset.sum_nonneg fun j _ =>
    div_nonneg (sq_nonneg _) (data.b_pos j).le

theorem averagedEmpiricalTieEnergy_le (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (hexact : HasExactEmpiricalOTSolves data)
    {m R : ℕ} (hm : 0 < m) (hR : 1 ≤ R) :
    averagedEmpiricalTieEnergy data m R ≤ empiricalTieEnergy data m := by
  unfold averagedEmpiricalTieEnergy empiricalTieEnergy
  rw [integral_finset_sum Finset.univ (fun j _ =>
      (memLp_averagedEmpiricalTieResidual data hregular hexact hm R j).integrable_sq.div_const _),
    integral_finset_sum Finset.univ (fun j _ =>
      (memLp_batchTieResidual data hregular hexact hm j).integrable_sq.div_const _)]
  simp only [integral_div]
  apply Finset.sum_le_sum
  intro j _
  apply div_le_div_of_nonneg_right _ (data.b_pos j).le
  exact integral_iidAverage_sq_le (empiricalBatchMeasure data m) _
    (memLp_batchTieResidual data hregular hexact hm j) hR

/-- The averaged tie residual is uniformly negligible over the repetition
range in Proposition F.4; averaging cannot increase its second moment. -/
theorem averagedEmpiricalTieEnergy_uniformLittleO (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (hexact : HasExactEmpiricalOTSolves data) :
    IsUniformLittleOInM data.rmax (averagedEmpiricalTieEnergy data)
      (fun m => 1 / (m : ℝ)) := by
  intro δ hδ
  obtain ⟨M, hM⟩ := empiricalTieEnergy_uniformLittleO data hregular hexact δ hδ
  refine ⟨max M 1, ?_⟩
  intro m hm R hR hRmax
  have hmpos : 0 < m := lt_of_lt_of_le Nat.zero_lt_one ((le_max_right M 1).trans hm)
  rw [abs_of_nonneg (averagedEmpiricalTieEnergy_nonneg data m R)]
  calc
    averagedEmpiricalTieEnergy data m R ≤ empiricalTieEnergy data m :=
      averagedEmpiricalTieEnergy_le data hregular hexact hmpos hR
    _ = |empiricalTieEnergy data m| := (abs_of_nonneg (empiricalTieEnergy_nonneg data m)).symm
    _ ≤ δ * |1 / (m : ℝ)| := hM m ((le_max_left M 1).trans hm) R hR hRmax

end DualGuided2026
