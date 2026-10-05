import TheoremLib.Dual_guided_2026.SDOTMoments

/-!
# Laguerre boundaries and empirical ties

The anti-concentration hypothesis implies atomless pairwise cost differences.
Consequently, iid samples have distinct cost differences for every site pair,
uniformly over all potentials, as used in Lemma F.5.
-/

namespace DualGuided2026

open MeasureTheory
open scoped BigOperators

variable {X Ω : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
  [FiniteDimensional ℝ X] [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Ω]

theorem target_count_pos (data : HELLOSDOTData X Ω) : 0 < data.n := by
  by_contra h
  have hn : data.n = 0 := by omega
  haveI : IsEmpty (Fin data.n) := by rw [hn]; infer_instance
  have := data.b_sum
  simp at this

theorem exists_unique_laguerreCell (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) (x : X) : ∃! j, x ∈ laguerreCell data g j := by
  classical
  letI : Nonempty (Fin data.n) := ⟨⟨0, target_count_pos data⟩⟩
  obtain ⟨i, _, hi⟩ := Finset.exists_min_image Finset.univ
    (fun j => sdCost data x j - g j) Finset.univ_nonempty
  let A := Finset.univ.filter (fun j => sdCost data x j - g j = sdCost data x i - g i)
  have hA : A.Nonempty := ⟨i, by simp [A]⟩
  let j := A.min' hA
  have hj : sdCost data x j - g j = sdCost data x i - g i :=
    (Finset.mem_filter.mp (A.min'_mem hA)).2
  have hcell : x ∈ laguerreCell data g j := by
    constructor
    · intro k
      rw [hj]
      exact hi k (Finset.mem_univ k)
    · intro k hk
      apply lt_of_le_of_ne
      · rw [hj]
        exact hi k (Finset.mem_univ k)
      · intro heq
        have hkA : k ∈ A := by simp [A, ← heq, hj]
        exact (not_le_of_gt hk) (A.min'_le k hkA)
  refine ⟨j, hcell, ?_⟩
  intro k hk
  rcases lt_trichotomy k j with hkj | hkj | hjk
  · exact (not_lt_of_ge (hk.1 j) (hcell.2 k hkj)).elim
  · exact hkj
  · exact (not_lt_of_ge (hcell.1 k) (hk.2 j hjk)).elim

theorem laguerreCells_pairwiseDisjoint (data : HELLOSDOTData X Ω)
    (g : Fin data.n → ℝ) : Pairwise (fun i j => Disjoint (laguerreCell data g i)
      (laguerreCell data g j)) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hi hj
  obtain ⟨k, _, hk⟩ := exists_unique_laguerreCell data g x
  exact hij ((hk i hi).trans (hk j hj).symm)

theorem iUnion_laguerreCell (data : HELLOSDOTData X Ω) (g : Fin data.n → ℝ) :
    (⋃ j, laguerreCell data g j) = Set.univ := by
  ext x
  simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
  obtain ⟨j, hj, _⟩ := exists_unique_laguerreCell data g x
  exact ⟨j, hj⟩

theorem populationMarginal_sum (data : HELLOSDOTData X Ω) (g : Fin data.n → ℝ) :
    ∑ j, data.populationMarginal g j = 1 := by
  have h := measure_iUnion (μ := data.sourceMeasure) (laguerreCells_pairwiseDisjoint data g)
    (fun j => measurableSet_laguerreCell data g j)
  rw [iUnion_laguerreCell, measure_univ] at h
  rw [tsum_fintype] at h
  have hr := congrArg ENNReal.toReal h
  rw [ENNReal.toReal_sum (fun j _ => measure_ne_top data.sourceMeasure _)] at hr
  simpa [HELLOSDOTData.populationMarginal] using hr.symm

theorem pairwise_projection_atomless (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) {i j : Fin data.n} (hij : i ≠ j)
    (t : ℝ) :
    data.sourceMeasure {x | inner ℝ (targetUnitDirection data i j) x = t} = 0 := by
  obtain ⟨q, hq, hmoment, C, lambda, hC, hlambda, hac, hrest⟩ := hregular
  let E := {x | inner ℝ (targetUnitDirection data i j) x = t}
  have hfinite : data.sourceMeasure E ≠ ⊤ := measure_ne_top _ _
  have hzero : (data.sourceMeasure E).toReal = 0 := by
    apply le_antisymm _ ENNReal.toReal_nonneg
    by_contra h
    have ha : 0 < (data.sourceMeasure E).toReal := lt_of_not_ge h
    let s := (data.sourceMeasure E).toReal / (2 * (C + 1))
    have hs : 0 < s := div_pos ha (by positivity)
    have hsub : E ⊆ {x | |inner ℝ (targetUnitDirection data i j) x - t| ≤ s} := by
      intro x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      rw [hx, sub_self, abs_zero]
      exact hs.le
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top
      ((measure_mono hsub).trans (hac i j hij t s hs))
    rw [ENNReal.toReal_ofReal (mul_nonneg hC hs.le)] at hb
    have heq : s * (2 * (C + 1)) = (data.sourceMeasure E).toReal :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith
  exact ((ENNReal.toReal_eq_zero_iff _).mp hzero).resolve_right hfinite

theorem sdCost_sub_sdCost (data : HELLOSDOTData X Ω) (x : X) (i j : Fin data.n) :
    sdCost data x i - sdCost data x j =
      2 * inner ℝ (data.targetSites j - data.targetSites i) x +
        ‖data.targetSites i‖ ^ 2 - ‖data.targetSites j‖ ^ 2 := by
  simp only [sdCost, norm_sub_sq_real, inner_sub_left, real_inner_comm]
  ring

theorem pairwise_costDifference_atomless (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) {i j : Fin data.n} (hij : i ≠ j)
    (t : ℝ) : data.sourceMeasure {x | sdCost data x i - sdCost data x j = t} = 0 := by
  have hnorm : ‖data.targetSites j - data.targetSites i‖ ≠ 0 := by
    intro h
    exact hij.symm (data.targetSites_injective (sub_eq_zero.mp (norm_eq_zero.mp h)))
  apply measure_mono_null _ (pairwise_projection_atomless data hregular hij
    ((t - ‖data.targetSites i‖ ^ 2 + ‖data.targetSites j‖ ^ 2) /
      (2 * ‖data.targetSites j - data.targetSites i‖)))
  intro x hx
  simp only [Set.mem_setOf_eq, sdCost_sub_sdCost] at hx ⊢
  simp only [targetUnitDirection, real_inner_smul_left]
  field_simp [hnorm]
  linarith

theorem pairwise_boundary_null (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (g : Fin data.n → ℝ)
    {i j : Fin data.n} (hij : i ≠ j) :
    data.sourceMeasure {x | sdCost data x i - g i = sdCost data x j - g j} = 0 := by
  have hset : {x | sdCost data x i - g i = sdCost data x j - g j} =
      {x | sdCost data x i - sdCost data x j = g i - g j} := by
    ext x
    simp only [Set.mem_setOf_eq]
    constructor <;> intro h <;> linarith
  rw [hset]
  exact pairwise_costDifference_atomless data hregular hij (g i - g j)

/-- The property of the realized sample used in Lemma F.5, independent of
the empirical potential and of the oracle seed. -/
def PairwiseCostDistinct (data : HELLOSDOTData X Ω) {m : ℕ} (samples : Fin m → X) : Prop :=
  ∀ i j : Fin data.n, i ≠ j →
    Function.Injective (fun k => sdCost data (samples k) i - sdCost data (samples k) j)

theorem ae_pairwiseCostDistinct_sourceBatch (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (m : ℕ) :
    ∀ᵐ samples ∂sourceBatchMeasure data m, PairwiseCostDistinct data samples := by
  classical
  have hpair (i j : Fin data.n) (hij : i ≠ j) (k l : Fin m) (hkl : k ≠ l) :
      ∀ᵐ samples ∂sourceBatchMeasure data m,
        sdCost data (samples k) i - sdCost data (samples k) j ≠
          sdCost data (samples l) i - sdCost data (samples l) j := by
    let D := {z : X × X | sdCost data z.1 i - sdCost data z.1 j =
      sdCost data z.2 i - sdCost data z.2 j}
    have hmD : MeasurableSet D := by
      apply measurableSet_eq_fun <;> unfold sdCost <;> fun_prop
    have hD : data.sourceMeasure.prod data.sourceMeasure D = 0 := by
      apply (Measure.measure_prod_null hmD).mpr
      filter_upwards [] with x
      change data.sourceMeasure {y | sdCost data x i - sdCost data x j =
        sdCost data y i - sdCost data y j} = 0
      simpa only [eq_comm] using pairwise_costDifference_atomless data hregular hij
        (sdCost data x i - sdCost data x j)
    have hind := (ProbabilityTheory.iIndepFun_pi
      (μ := fun _ : Fin m => data.sourceMeasure)
      (X := fun _ => id) (fun _ => measurable_id.aemeasurable)).indepFun hkl
    have hmap := (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map
      (measurable_pi_apply k).aemeasurable (measurable_pi_apply l).aemeasurable).mp hind
    rw [(measurePreserving_eval (fun _ : Fin m => data.sourceMeasure) k).map_eq,
      (measurePreserving_eval (fun _ : Fin m => data.sourceMeasure) l).map_eq] at hmap
    have hpull := Measure.map_apply (μ := Measure.pi fun _ : Fin m => data.sourceMeasure)
      (by fun_prop :
      Measurable fun samples : Fin m → X => (samples k, samples l)) hmD
    rw [hmap, hD] at hpull
    apply ae_iff.mpr
    simpa only [sourceBatchMeasure, Set.compl_setOf, not_not] using hpull.symm
  simp only [PairwiseCostDistinct, Function.Injective, ae_all_iff]
  intro i j hij k l
  by_cases hkl : k = l
  · simp [hkl]
  · filter_upwards [hpair i j hij k l hkl] with samples hs
    exact fun heq => (hs heq).elim

theorem ae_pairwiseCostDistinct_batch (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (m : ℕ) :
    ∀ᵐ batch ∂empiricalBatchMeasure data m, PairwiseCostDistinct data batch.1 :=
  measurePreserving_fst.quasiMeasurePreserving.ae
    (ae_pairwiseCostDistinct_sourceBatch data hregular m)

def IsActiveTarget (data : HELLOSDOTData X Ω) (x : X) (g : Fin data.n → ℝ)
    (j : Fin data.n) : Prop :=
  ∀ i, sdCost data x j - g j ≤ sdCost data x i - g i

noncomputable def empiricalTieRows (data : HELLOSDOTData X Ω) {m : ℕ}
    (samples : Fin m → X) (g : Fin data.n → ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun k => ∃ i j, i ≠ j ∧
    IsActiveTarget data (samples k) g i ∧ IsActiveTarget data (samples k) g j)

theorem activeTargets_costDifference (data : HELLOSDOTData X Ω) (x : X)
    (g : Fin data.n → ℝ) {i j : Fin data.n}
    (hi : IsActiveTarget data x g i) (hj : IsActiveTarget data x g j) :
    sdCost data x i - sdCost data x j = g i - g j := by
  have := hi j
  have := hj i
  linarith

/-- The number of tied sample rows is at most the number of unordered site
pairs. This holds for every potential on the same realized sample. -/
theorem empiricalTieRows_card_le (data : HELLOSDOTData X Ω) {m : ℕ}
    (samples : Fin m → X) (hdistinct : PairwiseCostDistinct data samples)
    (g : Fin data.n → ℝ) : (empiricalTieRows data samples g).card ≤ data.n.choose 2 := by
  classical
  let T := empiricalTieRows data samples g
  have hwitness (k : T) : ∃ i j, i ≠ j ∧
      IsActiveTarget data (samples k) g i ∧ IsActiveTarget data (samples k) g j :=
    (Finset.mem_filter.mp k.2).2
  choose i j hij hi hj using hwitness
  let f : T → {p : Sym2 (Fin data.n) // ¬p.IsDiag} := fun k =>
    ⟨s(i k, j k), by simpa using hij k⟩
  have hf : Function.Injective f := by
    intro k l hkl
    have heq : s(i k, j k) = s(i l, j l) := congrArg Subtype.val hkl
    apply Subtype.ext
    rcases Sym2.eq_iff.mp heq with ⟨heqi, heqj⟩ | ⟨heqi, heqj⟩
    · apply hdistinct (i k) (j k) (hij k)
      dsimp only
      rw [activeTargets_costDifference data _ g (hi k) (hj k)]
      rw [heqi, heqj, activeTargets_costDifference data _ g (hi l) (hj l)]
    · apply hdistinct (i k) (j k) (hij k)
      dsimp only
      rw [activeTargets_costDifference data _ g (hi k) (hj k)]
      rw [heqi, heqj, activeTargets_costDifference data _ g (hj l) (hi l)]
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, Sym2.card_subtype_not_diag, Fintype.card_fin] using hcard

/-- The tie-count bound is simultaneous over all potentials, including
random potentials chosen from the sample by an arbitrary measurable oracle. -/
theorem ae_empiricalTieRows_card_le (data : HELLOSDOTData X Ω)
    (hregular : HasHELLOSDOTRegularity data) (m : ℕ) :
    ∀ᵐ batch ∂empiricalBatchMeasure data m, ∀ g,
      (empiricalTieRows data batch.1 g).card ≤ data.n.choose 2 := by
  filter_upwards [ae_pairwiseCostDistinct_batch data hregular m] with batch hbatch
  exact empiricalTieRows_card_le data batch.1 hbatch

end DualGuided2026
