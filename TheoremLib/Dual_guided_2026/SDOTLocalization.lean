import TheoremLib.Dual_guided_2026.SDOTTies

/-!
# Deterministic localization of empirical dual maximizers

Positive target weights force every target to be active in an empirical
maximizer. The number of active rows is at least the corresponding target
mass times the sample size, independently of the tie convention.
-/

namespace DualGuided2026

open MeasureTheory
open scoped BigOperators

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

noncomputable def empiricalActiveRows (data : HELLOSDOTData X Ω) {m : ℕ}
    (samples : Fin m → X) (g : Fin data.n → ℝ) (j : Fin data.n) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun k => IsActiveTarget data (samples k) g j)

/-- Increasing one target coordinate gives the support-count part of Lemma
F.9 directly, without choosing an optimal coupling. -/
theorem empiricalActiveRows_mass_le (data : HELLOSDOTData X Ω)
    {m : ℕ} (hm : 0 < m) (samples : Fin m → X) (g : Fin data.n → ℝ)
    (hg : IsEmpiricalDualMaximizer data samples g) (j : Fin data.n) :
    (m : ℝ) * data.b j ≤ (empiricalActiveRows data samples g j).card := by
  classical
  let a := fun k => laguerreAssignment data g (samples k)
  let score := fun k i => sdCost data (samples k) i - g i
  let A := empiricalActiveRows data samples g j
  let e : Fin m → ℝ := fun k => if k ∈ A then 1 else 0
  let v : Fin data.n → ℝ := fun i => if i = j then 1 else 0
  obtain ⟨t, ht, hsmall⟩ := exists_small_score_perturbation score a
  have hmin (k : Fin m) :
      sInf (Set.range fun i => sdCost data (samples k) i - g i) = score k (a k) :=
    semiDualMinimum_eq_active data g _ (laguerreAssignment_mem data g (samples k)).1
  have hperturb (k : Fin m) :
      sInf (Set.range fun i => sdCost data (samples k) i - (g i + t * v i)) =
        score k (a k) - t * e k := by
    by_cases hk : k ∈ A
    · have hj : IsActiveTarget data (samples k) g j :=
        (Finset.mem_filter.mp hk).2
      have hj' : IsActiveTarget data (samples k) (fun i => g i + t * v i) j := by
        intro i
        have hi := hj i
        dsimp only [v]
        by_cases hij : i = j
        · subst i
          exact le_rfl
        · simp only [ite_true, if_neg hij, mul_one, mul_zero, add_zero]
          linarith
      rw [semiDualMinimum_eq_active data _ _ hj']
      have heq : score k j = score k (a k) := le_antisymm (hj (a k))
        ((laguerreAssignment_mem data g (samples k)).1 j)
      simp only [v, if_pos rfl, mul_one, e, if_pos hk]
      dsimp only [score] at heq ⊢
      linarith
    · have hnot : ¬ IsActiveTarget data (samples k) g j := by
        simpa [A, empiricalActiveRows] using hk
      have haj : a k ≠ j := by
        intro heq
        apply hnot
        have ha : IsActiveTarget data (samples k) g (a k) :=
          (laguerreAssignment_mem data g (samples k)).1
        rwa [heq] at ha
      have hgap : 2 * t < score k j - score k (a k) := by
        apply hsmall k j
        apply lt_of_le_of_ne ((laguerreAssignment_mem data g (samples k)).1 j)
        intro heq
        apply hnot
        intro i
        rw [← heq]
        exact (laguerreAssignment_mem data g (samples k)).1 i
      have ha' : IsActiveTarget data (samples k) (fun i => g i + t * v i) (a k) := by
        intro i
        have hi := (laguerreAssignment_mem data g (samples k)).1 i
        dsimp only [v]
        simp only [if_neg haj, mul_zero, add_zero]
        by_cases hij : i = j
        · subst i
          simp only [ite_true, mul_one]
          dsimp only [score] at hgap
          linarith
        · simp only [if_neg hij, mul_zero, add_zero]
          exact hi
      rw [semiDualMinimum_eq_active data _ _ ha']
      simp only [v, if_neg haj, mul_zero, add_zero, e, if_neg hk, sub_zero]
      rfl
  have he : ∑ k, e k = (A.card : ℝ) := by
    simp only [e]
    rw [← Finset.sum_filter]
    simp
  have hb : ∑ i, data.b i * (t * v i) = data.b j * t := by
    simp [v]
  have hopt := hg.le_objective data hm (fun i => g i + t * v i)
  unfold empiricalSemiDualObjective at hopt
  simp_rw [hmin, hperturb] at hopt
  simp only [mul_add, Finset.sum_add_distrib, hb, Finset.sum_sub_distrib,
    ← Finset.mul_sum, he] at hopt
  have hmreal : 0 < (m : ℝ) := by exact_mod_cast hm
  have hcancel : data.b j * t ≤ (1 / (m : ℝ)) * (t * A.card) := by linarith
  have hprod : (m : ℝ) * (data.b j * t) ≤ t * A.card := by
    have h := mul_le_mul_of_nonneg_left hcancel hmreal.le
    field_simp at h
    nlinarith
  exact (mul_le_mul_iff_left₀ ht).mp (by nlinarith :
    ((m : ℝ) * data.b j) * t ≤ (A.card : ℝ) * t)

theorem empiricalActiveRows_nonempty (data : HELLOSDOTData X Ω)
    {m : ℕ} (hm : 0 < m) (samples : Fin m → X) (g : Fin data.n → ℝ)
    (hg : IsEmpiricalDualMaximizer data samples g) (j : Fin data.n) :
    (empiricalActiveRows data samples g j).Nonempty := by
  apply Finset.card_pos.mp
  have h := empiricalActiveRows_mass_le data hm samples g hg j
  have hpos : 0 < (m : ℝ) * data.b j := mul_pos (by exact_mod_cast hm) (data.b_pos j)
  exact_mod_cast (lt_of_lt_of_le hpos h)

theorem exists_empirical_active (data : HELLOSDOTData X Ω)
    {m : ℕ} (hm : 0 < m) (samples : Fin m → X) (g : Fin data.n → ℝ)
    (hg : IsEmpiricalDualMaximizer data samples g) (j : Fin data.n) :
    ∃ k, IsActiveTarget data (samples k) g j := by
  classical
  obtain ⟨k, hk⟩ := empiricalActiveRows_nonempty data hm samples g hg j
  exact ⟨k, (Finset.mem_filter.mp hk).2⟩

theorem costDifference_abs_le (data : HELLOSDOTData X Ω) (x : X)
    (i j : Fin data.n) {R : ℝ} (hx : ‖x‖ ≤ R) :
    |sdCost data x i - sdCost data x j| ≤
      4 * R * ‖data.targetSites‖ + 2 * ‖data.targetSites‖ ^ 2 := by
  have hi := norm_le_pi_norm data.targetSites i
  have hj := norm_le_pi_norm data.targetSites j
  have hd : ‖data.targetSites j - data.targetSites i‖ ≤ 2 * ‖data.targetSites‖ := by
    exact (norm_sub_le _ _).trans (by linarith)
  have hinner := abs_real_inner_le_norm (data.targetSites j - data.targetSites i) x
  have hsquares : |‖data.targetSites i‖ ^ 2 - ‖data.targetSites j‖ ^ 2| ≤
      2 * ‖data.targetSites‖ ^ 2 := by
    calc
      _ ≤ |‖data.targetSites i‖ ^ 2| + |‖data.targetSites j‖ ^ 2| := abs_sub _ _
      _ ≤ 2 * ‖data.targetSites‖ ^ 2 := by
        rw [abs_of_nonneg (sq_nonneg _), abs_of_nonneg (sq_nonneg _)]
        nlinarith [norm_nonneg (data.targetSites i), norm_nonneg (data.targetSites j),
          norm_nonneg data.targetSites]
  rw [sdCost_sub_sdCost]
  calc
    _ = |2 * inner ℝ (data.targetSites j - data.targetSites i) x +
        (‖data.targetSites i‖ ^ 2 - ‖data.targetSites j‖ ^ 2)| := by congr 1; ring
    _ ≤ |2 * inner ℝ (data.targetSites j - data.targetSites i) x| +
        |‖data.targetSites i‖ ^ 2 - ‖data.targetSites j‖ ^ 2| := abs_add_le _ _
    _ ≤ 4 * R * ‖data.targetSites‖ + 2 * ‖data.targetSites‖ ^ 2 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hp : ‖data.targetSites j - data.targetSites i‖ * ‖x‖ ≤
          (2 * ‖data.targetSites‖) * R := mul_le_mul hd hx (norm_nonneg _) (by positivity)
      linarith

theorem bgauge_eq_sum_differences (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (hg : IsBGauge data g) (i : Fin data.n) :
    g i = ∑ j, data.b j * (g i - g j) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul, data.b_sum, one_mul, hg, sub_zero]

/-- If each target is active at some bounded sample, all gauge-aligned
coordinates are bounded by a deterministic constant. -/
theorem empiricalPotential_norm_le_of_bounded_active (data : HELLOSDOTData X Ω)
    {m : ℕ} (samples : Fin m → X) (g : Fin data.n → ℝ)
    (hg : IsBGauge data g) {R : ℝ} (hR : 0 ≤ R)
    (hactive : ∀ j, ∃ k, IsActiveTarget data (samples k) g j ∧ ‖samples k‖ ≤ R) :
    ‖g‖ ≤ 4 * R * ‖data.targetSites‖ + 2 * ‖data.targetSites‖ ^ 2 := by
  let B := 4 * R * ‖data.targetSites‖ + 2 * ‖data.targetSites‖ ^ 2
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hdiff (i j : Fin data.n) : |g i - g j| ≤ B := by
    obtain ⟨ki, hi, hki⟩ := hactive i
    obtain ⟨kj, hj, hkj⟩ := hactive j
    have hlow := hi j
    have hupp := hj i
    have hci := abs_le.mp (costDifference_abs_le data (samples ki) i j hki)
    have hcj := abs_le.mp (costDifference_abs_le data (samples kj) i j hkj)
    apply abs_le.mpr
    dsimp only [B] at *
    constructor <;> linarith
  apply (pi_norm_le_iff_of_nonneg hB).mpr
  intro i
  rw [Real.norm_eq_abs, bgauge_eq_sum_differences data g hg i]
  calc
    _ ≤ ∑ j, |data.b j * (g i - g j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, data.b j * B := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul, abs_of_pos (data.b_pos j)]
      exact mul_le_mul_of_nonneg_left (hdiff i j) (data.b_pos j).le
    _ = B := by rw [← Finset.sum_mul, data.b_sum, one_mul]

/-- Lemma F.9's deterministic growth, for every empirical maximizer. The
Pi norm of the source batch is exactly its maximum sample radius. -/
theorem empiricalPotential_norm_le (data : HELLOSDOTData X Ω)
    {m : ℕ} (hm : 0 < m) (samples : Fin m → X) (g : Fin data.n → ℝ)
    (hg : IsEmpiricalDualMaximizer data samples g) :
    ‖g‖ ≤ 4 * ‖samples‖ * ‖data.targetSites‖ + 2 * ‖data.targetSites‖ ^ 2 := by
  apply empiricalPotential_norm_le_of_bounded_active data samples g hg.1 (norm_nonneg _)
  intro j
  obtain ⟨k, hk⟩ := exists_empirical_active data hm samples g hg j
  exact ⟨k, hk, norm_le_pi_norm samples k⟩

theorem empiricalPotential_displacement_growth (data : HELLOSDOTData X Ω)
    (gStar : Fin data.n → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {m : ℕ}, 0 < m → ∀ samples : Fin m → X,
      ∀ g : Fin data.n → ℝ, IsEmpiricalDualMaximizer data samples g →
        ‖g - gStar‖ ≤ C * (1 + ‖samples‖) := by
  let C := 1 + 4 * ‖data.targetSites‖ + 2 * ‖data.targetSites‖ ^ 2 + ‖gStar‖
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro m hm samples g hg
  have h := (norm_sub_le g gStar).trans
    (add_le_add (empiricalPotential_norm_le data hm samples g hg) (le_refl ‖gStar‖))
  have hnorm := norm_nonneg samples
  have hT := norm_nonneg data.targetSites
  have hgStar := norm_nonneg gStar
  dsimp only [C]
  nlinarith [mul_nonneg hnorm (sq_nonneg ‖data.targetSites‖),
    mul_nonneg hnorm hgStar]

noncomputable def sampleOutlierRows (samples : Fin m → X) (R : ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun k => R < ‖samples k‖)

/-- The compact-set certificate in Lemma F.10: too few outlying rows to
carry any target's positive mass forces a bounded active witness at each
target, simultaneously for all empirical maximizers. -/
theorem empiricalPotential_norm_le_of_few_outliers (data : HELLOSDOTData X Ω)
    {m : ℕ} (hm : 0 < m) (samples : Fin m → X) (g : Fin data.n → ℝ)
    (hg : IsEmpiricalDualMaximizer data samples g) {R : ℝ} (hR : 0 ≤ R)
    (hout : ∀ j, ((sampleOutlierRows samples R).card : ℝ) < (m : ℝ) * data.b j) :
    ‖g‖ ≤ 4 * R * ‖data.targetSites‖ + 2 * ‖data.targetSites‖ ^ 2 := by
  classical
  apply empiricalPotential_norm_le_of_bounded_active data samples g hg.1 hR
  intro j
  by_contra h
  have hsub : empiricalActiveRows data samples g j ⊆ sampleOutlierRows samples R := by
    intro k hk
    have hactive : IsActiveTarget data (samples k) g j := (Finset.mem_filter.mp hk).2
    have hnorm : R < ‖samples k‖ := by
      by_contra hle
      exact h ⟨k, hactive, le_of_not_gt hle⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hnorm⟩
  have hcard : ((empiricalActiveRows data samples g j).card : ℝ) ≤
      (sampleOutlierRows samples R).card := by exact_mod_cast Finset.card_le_card hsub
  exact (not_lt_of_ge ((empiricalActiveRows_mass_le data hm samples g hg j).trans hcard))
    (hout j)

theorem ae_empiricalPotential_displacement_growth (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) (gStar : Fin data.n → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {m : ℕ}, 0 < m →
      ∀ᵐ batch ∂empiricalBatchMeasure data m,
        ‖empiricalBatchPotential data m batch - gStar‖ ≤ C * (1 + ‖batch.1‖) := by
  obtain ⟨C, hC, hgrowth⟩ := empiricalPotential_displacement_growth data gStar
  refine ⟨C, hC, ?_⟩
  intro m hm
  filter_upwards [hexact.2.2 hm] with batch hbatch
  exact hgrowth hm batch.1 _ hbatch

theorem memLp_source_of_real_moment (data : HELLOSDOTData X Ω) {q : ℝ}
    (hq : 0 < q)
    (hmoment : (∫⁻ x, ENNReal.ofReal (Real.rpow ‖x‖ q) ∂data.sourceMeasure) < ⊤) :
    MemLp (id : X → X) (ENNReal.ofReal q) data.sourceMeasure := by
  have hqzero : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq
  have hint : Integrable (fun x : X => Real.rpow ‖x‖ q) data.sourceMeasure := by
    refine ⟨(measurable_norm.pow_const q).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal]
    · exact hmoment
    · exact Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  have hmem := memLp_one_iff_integrable.mpr hint
  have hiff := memLp_norm_rpow_iff (p := ENNReal.ofReal q) (q := ENNReal.ofReal q)
    (μ := data.sourceMeasure) (f := (id : X → X))
    measurable_id.aestronglyMeasurable hqzero ENNReal.ofReal_ne_top
  rw [ENNReal.div_self hqzero ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hq.le] at hiff
  exact hiff.mp hmem

omit [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
theorem norm_sourceBatch_le_sum {m : ℕ} (samples : Fin m → X) :
    ‖samples‖ ≤ ∑ k, ‖samples k‖ := by
  apply (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))).mpr
  intro k
  exact Finset.single_le_sum (fun i _ => norm_nonneg (samples i)) (Finset.mem_univ k)

theorem memLp_sourceBatch (data : HELLOSDOTData X Ω) {q : ℝ} (hq : 0 < q)
    (hmoment : (∫⁻ x, ENNReal.ofReal (Real.rpow ‖x‖ q) ∂data.sourceMeasure) < ⊤)
    (m : ℕ) : MemLp (id : (Fin m → X) → (Fin m → X)) (ENNReal.ofReal q)
      (sourceBatchMeasure data m) := by
  have hsource := memLp_source_of_real_moment data hq hmoment
  have hcoord (k : Fin m) : MemLp (fun samples : Fin m → X => ‖samples k‖)
      (ENNReal.ofReal q) (sourceBatchMeasure data m) :=
    (hsource.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin m => data.sourceMeasure) k)).norm
  have hsum := memLp_finset_sum Finset.univ (fun k _ => hcoord k)
  apply hsum.of_le measurable_id.aestronglyMeasurable
  filter_upwards [] with samples
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))]
  exact norm_sourceBatch_le_sum samples

omit [InnerProductSpace ℝ X] [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] in
theorem norm_sourceBatch_rpow_le_sum {m : ℕ} (hm : 0 < m)
    (samples : Fin m → X) (q : ℝ) :
    Real.rpow ‖samples‖ q ≤ ∑ k, Real.rpow ‖samples k‖ q := by
  classical
  have hnonempty : (Finset.univ : Finset (Fin m)).Nonempty :=
    ⟨⟨0, hm⟩, Finset.mem_univ _⟩
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ (fun k => ‖samples k‖) hnonempty
  have heq : ‖samples‖ = ‖samples k‖ := le_antisymm
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun i => hk i (Finset.mem_univ _)))
    (norm_le_pi_norm samples k)
  rw [heq]
  exact Finset.single_le_sum (fun i _ => Real.rpow_nonneg (norm_nonneg _) _) (Finset.mem_univ k)

/-- The maximum source radius has a moment growing at most linearly in
the batch size, the deterministic-source step of Proposition F.14. -/
theorem integral_norm_sourceBatch_rpow_le (data : HELLOSDOTData X Ω)
    {q : ℝ} (hq : 0 < q)
    (hmoment : (∫⁻ x, ENNReal.ofReal (Real.rpow ‖x‖ q) ∂data.sourceMeasure) < ⊤)
    {m : ℕ} (hm : 0 < m) :
    (∫ samples, Real.rpow ‖samples‖ q ∂sourceBatchMeasure data m) ≤
      (m : ℝ) * ∫ x, Real.rpow ‖x‖ q ∂data.sourceMeasure := by
  have hqzero : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq
  have hsource := (memLp_source_of_real_moment data hq hmoment).integrable_norm_rpow
    hqzero ENNReal.ofReal_ne_top
  simp only [ENNReal.toReal_ofReal hq.le, id_eq] at hsource
  have hbatch := (memLp_sourceBatch data hq hmoment m).integrable_norm_rpow
    hqzero ENNReal.ofReal_ne_top
  simp only [ENNReal.toReal_ofReal hq.le, id_eq] at hbatch
  have hcoord (k : Fin m) : Integrable
      (fun samples : Fin m → X => Real.rpow ‖samples k‖ q) (sourceBatchMeasure data m) :=
    (measurePreserving_eval (fun _ : Fin m => data.sourceMeasure) k).integrable_comp_of_integrable
      hsource
  calc
    _ ≤ ∫ samples, ∑ k, Real.rpow ‖samples k‖ q ∂sourceBatchMeasure data m :=
      integral_mono hbatch (integrable_finset_sum _ (fun k _ => hcoord k))
        (fun samples => norm_sourceBatch_rpow_le_sum hm samples q)
    _ = (m : ℝ) * ∫ x, Real.rpow ‖x‖ q ∂data.sourceMeasure := by
      rw [integral_finset_sum _ (fun k _ => hcoord k)]
      have heval (k : Fin m) :
          (∫ samples, Real.rpow ‖samples k‖ q ∂sourceBatchMeasure data m) =
            ∫ x, Real.rpow ‖x‖ q ∂data.sourceMeasure :=
        integral_comp_eval (μ := fun _ : Fin m => data.sourceMeasure) (i := k)
          hsource.aestronglyMeasurable
      simp only [heval, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The deterministic growth estimate makes every finite-sample empirical
potential inherit every available source moment. This is the integrability
input for the tail/Hölder step in Proposition F.14. -/
theorem memLp_empiricalBatchPotential (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) {q : ℝ} (hq : 0 < q)
    (hmoment : (∫⁻ x, ENNReal.ofReal (Real.rpow ‖x‖ q) ∂data.sourceMeasure) < ⊤)
    {m : ℕ} (hm : 0 < m) :
    MemLp (empiricalBatchPotential data m) (ENNReal.ofReal q) (empiricalBatchMeasure data m) := by
  have hsource := memLp_source_of_real_moment data hq hmoment
  have hcoord (k : Fin m) :
      MemLp (fun batch : (Fin m → X) × Ω => ‖batch.1 k‖)
        (ENNReal.ofReal q) (empiricalBatchMeasure data m) := by
    have hsample := hsource.comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin m => data.sourceMeasure) k)
    exact hsample.norm.comp_measurePreserving measurePreserving_fst
  obtain ⟨C, hC, hgrowth⟩ := ae_empiricalPotential_displacement_growth data hexact
    (0 : Fin data.n → ℝ)
  have hbound : MemLp (fun batch : (Fin m → X) × Ω => C * (1 + ∑ k, ‖batch.1 k‖))
      (ENNReal.ofReal q) (empiricalBatchMeasure data m) := by
    apply MemLp.const_mul
    exact (memLp_const (1 : ℝ)).add (memLp_finset_sum _ (fun k _ => hcoord k))
  apply hbound.of_le (measurable_empiricalBatchPotential data hexact hm).aestronglyMeasurable
  filter_upwards [hgrowth hm] with batch hbatch
  simp only [sub_zero] at hbatch
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact hbatch.trans (mul_le_mul_of_nonneg_left
    (by linarith [norm_sourceBatch_le_sum batch.1]) hC.le)

theorem rpow_one_add_le {r q : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) :
    Real.rpow (1 + r) q ≤ Real.rpow 2 q * (1 + Real.rpow r q) := by
  have hpow : 0 ≤ Real.rpow r q := Real.rpow_nonneg hr _
  have htwo : 0 ≤ Real.rpow 2 q := Real.rpow_nonneg (by norm_num) _
  by_cases h : r ≤ 1
  · have hle := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + r)
      (by linarith : 1 + r ≤ 2) hq
    change Real.rpow (1 + r) q ≤ Real.rpow 2 q at hle
    nlinarith [mul_nonneg htwo hpow]
  · have hle := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + r)
      (by linarith : 1 + r ≤ 2 * r) hq
    rw [Real.mul_rpow (by norm_num) hr] at hle
    change Real.rpow (1 + r) q ≤ Real.rpow 2 q * Real.rpow r q at hle
    nlinarith

/-- The global moment estimate used on the exponentially rare complement
of local empirical-maximizer events in Proposition F.14. The constant is
independent of the batch size and of the solver's internal seed. -/
theorem empiricalPotential_displacement_moment_growth (data : HELLOSDOTData X Ω)
    (hexact : HasExactEmpiricalOTSolves data) {q : ℝ} (hq : 0 < q)
    (hmoment : (∫⁻ x, ENNReal.ofReal (Real.rpow ‖x‖ q) ∂data.sourceMeasure) < ⊤)
    (gStar : Fin data.n → ℝ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {m : ℕ}, 0 < m →
      (∫ batch, Real.rpow ‖empiricalBatchPotential data m batch - gStar‖ q
        ∂empiricalBatchMeasure data m) ≤ K * (1 + (m : ℝ)) := by
  obtain ⟨C, hC, hgrowth⟩ := ae_empiricalPotential_displacement_growth data hexact gStar
  let A := Real.rpow C q * Real.rpow 2 q
  let M := ∫ x, Real.rpow ‖x‖ q ∂data.sourceMeasure
  have hA : 0 < A := by dsimp [A]; positivity
  have hM : 0 ≤ M := integral_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)
  refine ⟨1 + A * (1 + M), by positivity, ?_⟩
  intro m hm
  have hqzero : ENNReal.ofReal q ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hq
  have hpotential := ((memLp_empiricalBatchPotential data hexact hq hmoment hm).sub
    (memLp_const gStar)).integrable_norm_rpow hqzero ENNReal.ofReal_ne_top
  simp only [ENNReal.toReal_ofReal hq.le, Pi.sub_apply] at hpotential
  have hsource := (memLp_sourceBatch data hq hmoment m).integrable_norm_rpow
    hqzero ENNReal.ofReal_ne_top
  simp only [ENNReal.toReal_ofReal hq.le, id_eq] at hsource
  have hradius : Integrable (fun batch : (Fin m → X) × Ω => Real.rpow ‖batch.1‖ q)
      (empiricalBatchMeasure data m) := hsource.comp_fst (data.solverMeasure m)
  have hbound : Integrable (fun batch : (Fin m → X) × Ω => A * (1 + Real.rpow ‖batch.1‖ q))
      (empiricalBatchMeasure data m) := (integrable_const (1 : ℝ)).add hradius |>.const_mul A
  have hpoint : ∀ᵐ batch ∂empiricalBatchMeasure data m,
      Real.rpow ‖empiricalBatchPotential data m batch - gStar‖ q ≤
        A * (1 + Real.rpow ‖batch.1‖ q) := by
    filter_upwards [hgrowth hm] with batch hbatch
    have h := Real.rpow_le_rpow (norm_nonneg _) hbatch hq.le
    rw [Real.mul_rpow hC.le (by positivity)] at h
    exact h.trans (by
      dsimp only [A]
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (rpow_one_add_le (norm_nonneg _) hq.le)
        (Real.rpow_nonneg hC.le _))
  have hradiusIntegral :
      (∫ batch : (Fin m → X) × Ω, Real.rpow ‖batch.1‖ q ∂empiricalBatchMeasure data m) =
        ∫ samples, Real.rpow ‖samples‖ q ∂sourceBatchMeasure data m := by
    unfold empiricalBatchMeasure
    rw [integral_fun_fst (fun samples : Fin m → X => Real.rpow ‖samples‖ q)]
    simp
  have hcomparison := integral_mono_ae hpotential hbound hpoint
  rw [integral_const_mul, integral_add (integrable_const _) hradius,
    integral_const, probReal_univ, one_smul, hradiusIntegral] at hcomparison
  have hradiusBound := integral_norm_sourceBatch_rpow_le data hq hmoment hm
  have hmnonneg : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  dsimp only [M] at hM
  change _ ≤ (1 + A * (1 + M)) * (1 + (m : ℝ))
  have haux :
      A * (1 + ∫ samples, Real.rpow ‖samples‖ q ∂sourceBatchMeasure data m) ≤
        A * (1 + (m : ℝ) * M) := by
    apply mul_le_mul_of_nonneg_left _ hA.le
    exact add_le_add (le_refl 1) hradiusBound
  exact (hcomparison.trans haux).trans (by
    nlinarith [mul_nonneg hA.le hM, mul_nonneg hA.le hmnonneg,
      mul_nonneg (mul_nonneg hA.le hM) hmnonneg])

theorem semiDualMinimum_le_score (data : HELLOSDOTData X Ω)
    (x : X) (g : Fin data.n → ℝ) (j : Fin data.n) :
    sInf (Set.range fun i => sdCost data x i - g i) ≤ sdCost data x j - g j := by
  rw [semiDualMinimum_eq_active data g x (laguerreAssignment_mem data g x).1]
  exact (laguerreAssignment_mem data g x).1 j

theorem semiDualMinimum_sub_le_norm (data : HELLOSDOTData X Ω)
    (x : X) (g h : Fin data.n → ℝ) :
    sInf (Set.range fun i => sdCost data x i - g i) -
      sInf (Set.range fun i => sdCost data x i - h i) ≤ ‖g - h‖ := by
  let j := laguerreAssignment data h x
  rw [semiDualMinimum_eq_active data h x (laguerreAssignment_mem data h x).1]
  have hg := semiDualMinimum_le_score data x g j
  have hj := norm_le_pi_norm (g - h) j
  simp only [Pi.sub_apply, Real.norm_eq_abs] at hj
  have hcoord := (abs_le.mp hj).1
  change _ ≤ ‖g - h‖
  nlinarith

/-- The single-sample semidual contrast has a bounded envelope, even when
the source itself has unbounded support. -/
theorem semiDualMinimum_sub_abs_le_norm (data : HELLOSDOTData X Ω)
    (x : X) (g h : Fin data.n → ℝ) :
    |sInf (Set.range fun i => sdCost data x i - g i) -
      sInf (Set.range fun i => sdCost data x i - h i)| ≤ ‖g - h‖ := by
  apply abs_le.mpr
  have hg := semiDualMinimum_sub_le_norm data x g h
  have hh := semiDualMinimum_sub_le_norm data x h g
  rw [norm_sub_rev] at hh
  constructor <;> linarith

theorem empiricalSemiDualObjective_sub_abs_le_norm (data : HELLOSDOTData X Ω)
    {m : ℕ} (hm : 0 < m) (samples : Fin m → X) (g h : Fin data.n → ℝ)
    (hg : IsBGauge data g) (hh : IsBGauge data h) :
    |empiricalSemiDualObjective data samples g - empiricalSemiDualObjective data samples h| ≤
      ‖g - h‖ := by
  have hsum : |∑ k, (sInf (Set.range fun j => sdCost data (samples k) j - g j) -
      sInf (Set.range fun j => sdCost data (samples k) j - h j))| ≤ (m : ℝ) * ‖g - h‖ := by
    calc
      _ ≤ ∑ k, |sInf (Set.range fun j => sdCost data (samples k) j - g j) -
          sInf (Set.range fun j => sdCost data (samples k) j - h j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ : Fin m, ‖g - h‖ := Finset.sum_le_sum
        (fun k _ => semiDualMinimum_sub_abs_le_norm data (samples k) g h)
      _ = _ := by simp
  have hmreal : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold empiricalSemiDualObjective
  rw [hg, hh, zero_add, zero_add, ← mul_sub, ← Finset.sum_sub_distrib,
    abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / (m : ℝ))]
  calc
    _ ≤ (1 / (m : ℝ)) * ((m : ℝ) * ‖g - h‖) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by field_simp

theorem empiricalSemiDualObjective_concave (data : HELLOSDOTData X Ω)
    {m : ℕ} (samples : Fin m → X) (g h : Fin data.n → ℝ)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * empiricalSemiDualObjective data samples g +
      t * empiricalSemiDualObjective data samples h ≤
        empiricalSemiDualObjective data samples
          (fun j => (1 - t) * g j + t * h j) := by
  let gt : Fin data.n → ℝ := fun j => (1 - t) * g j + t * h j
  have hmin (k : Fin m) :
      (1 - t) * sInf (Set.range fun j => sdCost data (samples k) j - g j) +
        t * sInf (Set.range fun j => sdCost data (samples k) j - h j) ≤
          sInf (Set.range fun j => sdCost data (samples k) j - gt j) := by
    let j := laguerreAssignment data gt (samples k)
    rw [semiDualMinimum_eq_active data gt _ (laguerreAssignment_mem data gt (samples k)).1]
    have hg := semiDualMinimum_le_score data (samples k) g j
    have hh := semiDualMinimum_le_score data (samples k) h j
    have hbound := add_le_add (mul_le_mul_of_nonneg_left hg (sub_nonneg.mpr ht1))
      (mul_le_mul_of_nonneg_left hh ht0)
    change _ ≤ sdCost data (samples k) j - gt j
    dsimp only [gt] at *
    nlinarith
  have hlinear : (∑ j, data.b j * gt j) =
      (1 - t) * ∑ j, data.b j * g j + t * ∑ j, data.b j * h j := by
    simp only [gt, mul_add, Finset.sum_add_distrib]
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ Finset.univ) => hmin k)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have hweighted := mul_le_mul_of_nonneg_left hsum
    (show 0 ≤ 1 / (m : ℝ) by positivity)
  change _ ≤ empiricalSemiDualObjective data samples gt
  unfold empiricalSemiDualObjective
  rw [hlinear]
  nlinarith

/-- Concavity turns a distant empirical maximum into an empirical objective
violation on a prescribed sphere around a population candidate. This reduces
localization to bounded contrasts on a compact sphere. -/
theorem empiricalMaximizer_radial_witness (data : HELLOSDOTData X Ω)
    {m : ℕ} (hm : 0 < m) (samples : Fin m → X) (g gStar : Fin data.n → ℝ)
    (hg : IsEmpiricalDualMaximizer data samples g)
    (hstar : IsBGauge data gStar) {r : ℝ} (hr : 0 < r) (hfar : r ≤ ‖g - gStar‖) :
    ∃ g' : Fin data.n → ℝ, IsBGauge data g' ∧ ‖g' - gStar‖ = r ∧
      empiricalSemiDualObjective data samples gStar ≤
        empiricalSemiDualObjective data samples g' := by
  let t := r / ‖g - gStar‖
  have hnorm : 0 < ‖g - gStar‖ := hr.trans_le hfar
  have ht0 : 0 ≤ t := (div_pos hr hnorm).le
  have ht1 : t ≤ 1 := (div_le_one hnorm).mpr hfar
  let g' : Fin data.n → ℝ := fun j => (1 - t) * gStar j + t * g j
  have hlinear : (∑ j, data.b j * g' j) =
      (1 - t) * ∑ j, data.b j * gStar j + t * ∑ j, data.b j * g j := by
    simp only [g', mul_add, Finset.sum_add_distrib]
    rw [Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intro j _ <;> ring
  have hgauge : IsBGauge data g' := by
    unfold IsBGauge
    rw [hlinear, hstar, hg.1]
    ring
  have hdiff : g' - gStar = t • (g - gStar) := by
    ext j
    simp only [g', Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hradius : ‖g' - gStar‖ = r := by
    rw [hdiff, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact div_mul_cancel₀ r hnorm.ne'
  have hoptimal := hg.le_objective data hm gStar
  have hconcave := empiricalSemiDualObjective_concave data samples gStar g ht0 ht1
  refine ⟨g', hgauge, hradius, ?_⟩
  change _ ≤ empiricalSemiDualObjective data samples g' at hconcave
  have hcompare := mul_le_mul_of_nonneg_left hoptimal ht0
  nlinarith

end DualGuided2026
