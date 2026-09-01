import Mathlib
import Foundation.Analysis.ExtendedRealFunctions

/-!
# Topology Sequences

Sequential cluster points, sequential compactness/closedness, sequential spaces, and sequential lower semicontinuity.
-/

open Filter
open scoped Topology
open Filter ERealFunction

/-! Source item: Chap01/Text_1_0_46 -/

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Text 1.0.46: A point `x` is a sequential cluster point of a sequence `u` if some subsequence of
`u` converges to `x`. -/
def IsSequentialClusterPt (u : ℕ → X) (x : X) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x)

/-- `IsSequentialClusterPt u x` means that some strictly monotone subsequence of `u` converges to
`x`. -/
theorem isSequentialClusterPt_iff_exists_subseq_tendsto {u : ℕ → X} {x : X} :
    IsSequentialClusterPt u x ↔
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) :=
  Iff.rfl

/-- A sequential cluster point is a cluster point in the canonical filter-based sense. -/
theorem IsSequentialClusterPt.mapClusterPt {u : ℕ → X} {x : X}
    (hx : IsSequentialClusterPt u x) :
    MapClusterPt x atTop u := by
  rcases hx with ⟨φ, hφ, hφt⟩
  have hsubcluster : MapClusterPt x atTop (u ∘ φ) := hφt.mapClusterPt
  simpa [Function.comp] using hsubcluster.of_comp hφ.tendsto_atTop

/-- A sequential cluster point is witnessed by a strictly monotone subsequence converging to the
given point. -/
-- Proof sketch: unfold `IsSequentialClusterPt`; the required subsequence is exactly the witness in
-- the definition.
theorem IsSequentialClusterPt.exists_subseq_tendsto {u : ℕ → X} {x : X}
    (hx : IsSequentialClusterPt u x) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 x) :=
  isSequentialClusterPt_iff_exists_subseq_tendsto.mp hx

/-! Source item: Chap01/Text_1_0_58 -/


/-- Text 1.0.58: the canonical predicate `IsSeqClosed C` means that every convergent sequence in
`C` has its limit in `C`. This is just the defining equation of `IsSeqClosed`. -/
theorem isSeqClosed_iff_forall_tendsto_mem {X : Type u} [TopologicalSpace X] {C : Set X} :
    IsSeqClosed C ↔
      ∀ ⦃x : ℕ → X⦄ ⦃p : X⦄, (∀ n, x n ∈ C) → Tendsto x atTop (𝓝 p) → p ∈ C :=
  Iff.rfl

/-! Source item: Chap01/Text_1_0_61 -/


variable {X : Type u} [TopologicalSpace X] [SequentialSpace X]

/-- Text 1.0.61: for an extended-real-valued function on a sequential topological space, lower
semicontinuity is equivalent to sequential lower semicontinuity, meaning that every convergent
sequence satisfies the liminf inequality at its limit.
-/
-- Proof sketch: use `lowerSemicontinuous_iff_isClosed_preimage` to identify lower
-- semicontinuity with closedness of all real sublevel sets, then use `isSeqClosed_iff_isClosed`
-- in a sequential space to pass between closedness and sequential closedness. The sequential
-- closedness of all sublevel sets is equivalent to the stated sequence-`liminf` inequality.
theorem lowerSemicontinuous_iff_forall_seq_tendsto_le_liminf (f : X → EReal) :
    LowerSemicontinuous f ↔
      ∀ ⦃x : X⦄ ⦃u : ℕ → X⦄,
        Tendsto u atTop (nhds x) → f x ≤ liminf (f ∘ u) atTop := by
  constructor
  · intro hf x u hu
    -- Transport the neighborhood-filter `liminf` inequality along the convergent sequence.
    calc
      f x ≤ liminf f (nhds x) := hf.le_liminf x
      _ ≤ liminf f (map u atTop) := liminf_le_liminf_of_le hu
      _ = liminf (f ∘ u) atTop := rfl
  · intro hseq
    rw [lowerSemicontinuous_iff_isClosed_preimage]
    intro a
    rw [← isSeqClosed_iff_isClosed]
    intro u x hu_mem hu
    -- The sequence hypothesis gives the lower bound at the limit point.
    have hx_le : f x ≤ liminf (f ∘ u) atTop := hseq hu
    -- Pointwise membership in the sublevel set forces the sequence `liminf` below `a`.
    have hliminf_le : liminf (f ∘ u) atTop ≤ a := by
      refine liminf_le_of_frequently_le ?_
      refine Frequently.of_forall fun n ↦ ?_
      simpa [Set.mem_preimage, Set.mem_Iic] using hu_mem n
    -- Combining the two inequalities puts the limit point back in the same sublevel set.
    show x ∈ f ⁻¹' Set.Iic a
    simpa [Set.mem_preimage, Set.mem_Iic] using hx_le.trans hliminf_le

/-! Source item: Chap01/Text_1_0_62 -/


variable {X : Type u} [TopologicalSpace X]

private lemma eventually_mem_compl_of_isSeqClosed {s : Set X} (hs : IsSeqClosed s) {x : ℕ → X}
    {p : X} (hx : Tendsto x atTop (nhds p)) (hp : p ∈ sᶜ) :
    ∀ᶠ n in atTop, x n ∈ sᶜ := by
  by_contra hEvent
  have hFreq : ∃ᶠ n in atTop, x n ∈ s := by
    by_contra hFreq
    apply hEvent
    simpa [Filter.not_frequently] using hFreq
  rcases extraction_of_frequently_atTop hFreq with ⟨φ, hφ_mono, hφ_mem⟩
  exact hp <| hs hφ_mem <| hx.comp hφ_mono.tendsto_atTop

private lemma seqContinuous_ulift_mem_compl_of_isSeqClosed {s : Set X} (hs : IsSeqClosed s) :
    SeqContinuous (fun x : X ↦ ULift.up (x ∈ sᶜ)) := by
  intro x p hx
  by_cases hp : p ∈ sᶜ
  · have hmem : Tendsto (fun n ↦ x n ∈ sᶜ) atTop (nhds True) := by
      rw [tendsto_nhds_true]
      exact eventually_mem_compl_of_isSeqClosed hs hx hp
    simpa [Function.comp, hp] using continuous_uliftUp.seqContinuous hmem
  · have hfalse : Tendsto (fun n ↦ x n ∈ sᶜ) atTop (nhds False) := by
      simp [nhds_false]
    simpa [Function.comp, hp] using continuous_uliftUp.seqContinuous hfalse

/-- Text 1.0.62: a topological space is sequential if and only if every map from it to an
arbitrary topological space is continuous exactly when it is sequentially continuous. -/
-- Proof sketch: For the forward implication, use the existing theorem
-- `continuous_iff_seqContinuous` on a sequential space. For the converse, test the assumed
-- equivalence on the Sierpinski-valued characteristic map of `sᶜ`: sequential closedness of `s`
-- makes this map sequentially continuous, hence continuous, so `sᶜ` is open and `s` is closed.
theorem sequentialSpace_iff_forall_continuous_iff_seqContinuous :
    SequentialSpace X ↔
      ∀ ⦃Y : Type*⦄ [TopologicalSpace Y] (f : X → Y), Continuous f ↔ SeqContinuous f := by
  constructor
  · intro hX Y _ f
    letI : SequentialSpace X := hX
    exact (continuous_iff_seqContinuous : Continuous f ↔ SeqContinuous f)
  · intro h
    refine SequentialSpace.mk fun s hs ↦ ?_
    let f : X → ULift Prop := fun x ↦ ULift.up (x ∈ sᶜ)
    have hcont : Continuous f := (h f).2 (seqContinuous_ulift_mem_compl_of_isSeqClosed hs)
    have hcont' : Continuous (fun x : X ↦ x ∈ sᶜ) := by
      simpa [f, Function.comp] using continuous_uliftDown.comp hcont
    have hopen : IsOpen (sᶜ : Set X) := by
      simpa using (isOpen_iff_continuous_mem : IsOpen (sᶜ : Set X) ↔
        Continuous (fun x : X ↦ x ∈ sᶜ)).2 hcont'
    exact isOpen_compl_iff.mp hopen

/-! Source item: Chap01/Lemma_1_34 -/

section SeqClosed

variable {X : Type u} [TopologicalSpace X] [T2Space X]
variable {C : Set X}

/-- Lemma 1.34 (1): a sequentially compact subset of a Hausdorff space is sequentially closed. -/
-- Proof sketch: given a convergent sequence in `C`, use sequential compactness to extract a
-- convergent subsequence with limit in `C`; in a Hausdorff space the subsequence has the same limit
-- as the original sequence, so the ambient limit belongs to `C`.
theorem IsSeqCompact.isSeqClosed (hC : IsSeqCompact C) :
    IsSeqClosed C := by
  intro u x hu hx
  -- Extract a convergent subsequence whose limit stays inside `C`.
  obtain ⟨y, hyC, φ, hφ_mono, hφ_tendsto⟩ := hC hu
  -- Reindex the original convergence along the subsequence map.
  have hφ_tendsto_x := hx.comp hφ_mono.tendsto_atTop
  -- In a Hausdorff space the subsequence limit must agree with the ambient limit.
  have hy_eq_x : y = x := tendsto_nhds_unique hφ_tendsto hφ_tendsto_x
  simpa [hy_eq_x] using hyC

end SeqClosed

section SeqCompact

variable {X : Type u} [TopologicalSpace X]
variable {A C : Set X}

/-- Lemma 1.34 (2): a sequentially closed subset of a sequentially compact set is sequentially
compact. -/
-- Proof sketch: start with a sequence in `A`; since `A ⊆ C`, sequential compactness of `C`
-- provides a convergent subsequence with limit in `C`; sequential closedness of `A` forces that
-- limit to lie in `A`, yielding sequential compactness of `A`.
theorem IsSeqCompact.of_isSeqClosed_subset (hC : IsSeqCompact C) (hA_closed : IsSeqClosed A)
    (hA : A ⊆ C) :
    IsSeqCompact A := by
  intro u huA
  -- View the sequence as taking values in `C` and extract a convergent subsequence there.
  obtain ⟨x, hxC, φ, hφ_mono, hφ_tendsto⟩ := hC (fun n ↦ hA (huA n))
  -- The subsequence still lies in `A`, so sequential closedness forces its limit back into `A`.
  have hsubseq_mem_A : ∀ n, (u ∘ φ) n ∈ A := by
    intro n
    exact huA (φ n)
  have hxA : x ∈ A := hA_closed hsubseq_mem_A hφ_tendsto
  exact ⟨x, hxA, φ, hφ_mono, hφ_tendsto⟩

end SeqCompact

/-! Source item: Chap01/Lemma_1_35 -/

variable {X : Type u} [TopologicalSpace X]

/-- Lemma 1.35: if a sequence in a sequentially compact subset has a unique
sequential cluster point, expressed by the canonical predicate `IsSequentialClusterPt`, then the
whole sequence converges to that point. -/
-- Proof sketch: argue by contradiction. If `u` does not converge to `x`, choose a neighborhood of
-- `x` missed infinitely often and extract a subsequence in `C \ U`. Sequential compactness of `C`
-- gives a further convergent subsequence with limit `y`; by uniqueness of sequential cluster
-- points, `y = x`. This contradicts eventual membership in `U` for a subsequence converging to
-- `x`.
theorem tendsto_of_unique_sequential_cluster_point {C : Set X} (hC : IsSeqCompact C)
    {u : ℕ → X} (huC : ∀ n, u n ∈ C) {x : X}
    (hunique : ∀ y : X, IsSequentialClusterPt u y → y = x) :
    Tendsto u atTop (nhds x) := by
  -- Assume the sequence does not converge and extract a neighborhood missed infinitely often.
  by_contra hu_not
  rcases Filter.not_tendsto_iff_exists_frequently_notMem.1 hu_not with ⟨U, hUx, hfreqU⟩
  rcases Filter.extraction_of_frequently_atTop hfreqU with ⟨φ, hφmono, hφU⟩
  have huφC : ∀ n, (u ∘ φ) n ∈ C := by
    intro n
    exact huC (φ n)
  -- Sequential compactness gives a convergent subsubsequence of the bad subsequence.
  rcases hC huφC with ⟨y, _, ψ, hψmono, hconv⟩
  have hy_eq_x : y = x := by
    apply hunique y
    exact ⟨φ ∘ ψ, hφmono.comp hψmono, by simpa [Function.comp] using hconv⟩
  have hconvx : Tendsto (u ∘ (φ ∘ ψ)) atTop (nhds x) := by
    simpa [Function.comp, hy_eq_x] using hconv
  -- The convergent subsubsequence is eventually in every neighborhood of `x`.
  have hEventIn : ∀ᶠ n in atTop, u ((φ ∘ ψ) n) ∈ U := by
    exact hconvx.eventually_mem hUx
  have hEventOut : ∀ᶠ n in atTop, u ((φ ∘ ψ) n) ∉ U := by
    exact Filter.Eventually.of_forall fun n ↦ by
      simpa [Function.comp] using hφU (ψ n)
  -- The subsequence cannot be eventually both inside and outside `U`.
  rcases (hEventIn.and hEventOut).exists with ⟨n, hnIn, hnOut⟩
  exact hnOut hnIn

/-! Source item: Chap01/Lemma_1_36 -/


variable {X : Type u} [TopologicalSpace X]

private lemma seq_lower_semicontinuous_implies_real_epigraph_seq_closed
    (f : X → EReal)
    (hseq : ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, Tendsto u atTop (nhds x) →
      f x ≤ liminf (fun n ↦ f (u n)) atTop) :
    IsSeqClosed (epigraph f) := by
  intro u p hu_mem hu_tendsto
  have hfst : Tendsto (fun n ↦ (u n).1) atTop (nhds p.1) := by
    simpa using (continuous_fst.tendsto p).comp hu_tendsto
  have hsnd : Tendsto (fun n ↦ (u n).2) atTop (nhds p.2) := by
    simpa using (continuous_snd.tendsto p).comp hu_tendsto
  have hsnd_ereal : Tendsto (fun n ↦ ((u n).2 : EReal)) atTop (nhds (p.2 : EReal)) := by
    exact (continuous_coe_real_ereal.tendsto p.2).comp hsnd
  have hlimsnd : liminf (fun n ↦ ((u n).2 : EReal)) atTop = (p.2 : EReal) := by
    simpa using Filter.Tendsto.liminf_eq hsnd_ereal
  have hlim_le :
      liminf (fun n ↦ f ((u n).1)) atTop ≤ liminf (fun n ↦ ((u n).2 : EReal)) atTop := by
    refine Filter.liminf_le_liminf <| Filter.Eventually.of_forall fun n ↦ ?_
    simpa using hu_mem n
  calc
    f p.1 ≤ liminf (fun n ↦ f ((u n).1)) atTop := hseq hfst
    _ ≤ liminf (fun n ↦ ((u n).2 : EReal)) atTop := hlim_le
    _ = (p.2 : EReal) := hlimsnd

private lemma real_epigraph_seq_closed_implies_lower_level_set_seq_closed
    (f : X → EReal)
    (hEpi : IsSeqClosed (epigraph f)) :
    ∀ ξ : ℝ, IsSeqClosed (lowerLevelSet f ξ) := by
  intro ξ u x hu_mem hu_tendsto
  have hprod_mem : ∀ n, (u n, ξ) ∈ epigraph f := by
    intro n
    simpa using hu_mem n
  have hprod_tendsto : Tendsto (fun n ↦ (u n, ξ)) atTop (nhds (x, ξ)) := by
    exact Filter.Tendsto.prodMk_nhds hu_tendsto tendsto_const_nhds
  simpa using hEpi hprod_mem hprod_tendsto

private lemma subseq_mem_lower_level_set_of_liminf_lt
    (f : X → EReal) {u : ℕ → X} {x : X} {ξ : ℝ}
    (hu : Tendsto u atTop (nhds x))
    (hξ : liminf (fun n ↦ f (u n)) atTop < (ξ : EReal)) :
    ∃ ns : ℕ → ℕ, Tendsto (fun n ↦ u (ns n)) atTop (nhds x) ∧
      ∀ n, f (u (ns n)) ≤ (ξ : EReal) := by
  let p : X → Prop := fun y ↦ f y < (ξ : EReal)
  have hfreq : ∃ᶠ n in atTop, p (u n) := by
    exact Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hξ
  obtain ⟨ns, hns_tendsto, hns_mem⟩ := Filter.subseq_forall_of_frequently hu hfreq
  exact ⟨ns, hns_tendsto, fun n ↦ le_of_lt (hns_mem n)⟩

private lemma lower_level_set_seq_closed_implies_seq_lower_semicontinuous
    (f : X → EReal)
    (hLevel : ∀ ξ : ℝ, IsSeqClosed (lowerLevelSet f ξ)) :
    ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, Tendsto u atTop (nhds x) →
      f x ≤ liminf (fun n ↦ f (u n)) atTop := by
  intro u x hu
  by_contra hnot
  have hlt : liminf (fun n ↦ f (u n)) atTop < f x := lt_of_not_ge hnot
  obtain ⟨ξ, hξ_left, hξ_right⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
  obtain ⟨ns, hns_tendsto, hns_mem⟩ :=
    subseq_mem_lower_level_set_of_liminf_lt f hu hξ_left
  have hx_mem : f x ≤ (ξ : EReal) := by
    exact hLevel ξ hns_mem hns_tendsto
  exact (not_le_of_gt hξ_right) hx_mem

/-- Lemma 1.36: for an extended-real-valued function on a topological space, sequential lower
semicontinuity, sequential closedness of the real-height epigraph, and sequential closedness of
every real lower level set are equivalent. -/
theorem sequentialLowerSemicontinuous_real_epigraph_seqClosed_lowerLevelSet_seqClosed_tfae
    (f : X → EReal) :
    List.TFAE [
      ∀ ⦃u : ℕ → X⦄ ⦃x : X⦄, Tendsto u atTop (nhds x) →
        f x ≤ liminf (fun n ↦ f (u n)) atTop,
      IsSeqClosed (epigraph f),
      ∀ ξ : ℝ, IsSeqClosed (lowerLevelSet f ξ)
    ] := by
  tfae_have 1 → 2 := seq_lower_semicontinuous_implies_real_epigraph_seq_closed f
  tfae_have 2 → 3 := real_epigraph_seq_closed_implies_lower_level_set_seq_closed f
  tfae_have 3 → 1 := lower_level_set_seq_closed_implies_seq_lower_semicontinuous f
  tfae_finish

/-! Source item: Chap01/Lemma_1_42 -/

variable {X : Type u}

/-- The set of sequential limit inferiors of `f` at `x`. -/
def sequentialLiminfValuesAt [TopologicalSpace X] (f : X → EReal) (x : X) :
    Set EReal :=
  {r | ∃ u : ℕ → X, Tendsto u atTop (nhds x) ∧ liminf (f ∘ u) atTop = r}

private theorem clusterPt_liminf_map_nhds [TopologicalSpace X] (f : X → EReal) (x : X) :
    ClusterPt (liminf f (nhds x)) (map f (nhds x)) := by
  let L := liminf f (nhds x)
  rcases eq_or_ne L ⊤ with htop | htop
  · rw [clusterPt_iff_frequently]
    intro s hs
    have hs_top : s ∈ nhds (⊤ : EReal) := by
      simpa [L, htop] using hs
    rcases EReal.nhds_top_basis.mem_iff.1 hs_top with ⟨a, -, ha⟩
    have hgt : ∀ᶠ y in nhds x, (a : EReal) < f y := by
      have : (a : EReal) < liminf f (nhds x) := by
        simp [L, htop]
      exact eventually_lt_of_lt_liminf this
    have hmem : ∀ᶠ z in map f (nhds x), z ∈ Set.Ioi (a : EReal) := by
      simpa [Filter.Eventually, mem_map'] using hgt
    exact hmem.frequently.mono fun z hz ↦ ha hz
  · rcases eq_or_ne L ⊥ with hbot | hbot
    · rw [clusterPt_iff_frequently]
      intro s hs
      have hs_bot : s ∈ nhds (⊥ : EReal) := by
        simpa [L, hbot] using hs
      rcases EReal.nhds_bot_basis.mem_iff.1 hs_bot with ⟨a, -, ha⟩
      have hlt : ∃ᶠ y in nhds x, f y < (a : EReal) := by
        have : liminf f (nhds x) < (a : EReal) := by
          simp [L, hbot]
        exact frequently_lt_of_liminf_lt (by isBoundedDefault) this
      have hmem : ∃ᶠ z in map f (nhds x), z ∈ Set.Iio (a : EReal) := by
        simpa [Filter.Frequently, Filter.Eventually, mem_map'] using hlt
      exact hmem.mono fun z hz ↦ ha hz
    · have hLfin : ((L.toReal : EReal) = L) := EReal.coe_toReal htop hbot
      have hbasis : (nhds L).HasBasis
          (fun p : ℝ × ℝ ↦ p.1 < L.toReal ∧ L.toReal < p.2)
          (fun p ↦ Set.Ioo (p.1 : EReal) (p.2 : EReal)) := by
        rw [← hLfin, EReal.nhds_coe]
        simpa [EReal.image_coe_Ioo] using
          (Filter.HasBasis.map (fun r : ℝ ↦ (r : EReal)) (nhds_basis_Ioo L.toReal))
      rw [clusterPt_iff_frequently]
      intro s hs
      rcases hbasis.mem_iff.mp hs with ⟨p, hp, hps⟩
      have hgt : ∀ᶠ y in nhds x, (p.1 : EReal) < f y := by
        have hp1 : (p.1 : EReal) < L := by
          calc
            (p.1 : EReal) < (L.toReal : EReal) := by
              exact_mod_cast hp.1
            _ = L := hLfin
        have : (p.1 : EReal) < liminf f (nhds x) := by
          simpa [L] using hp1
        exact eventually_lt_of_lt_liminf this
      have hlt : ∃ᶠ y in nhds x, f y < (p.2 : EReal) := by
        have hp2 : L < (p.2 : EReal) := by
          calc
            L = (L.toReal : EReal) := hLfin.symm
            _ < (p.2 : EReal) := by
              exact_mod_cast hp.2
        have : liminf f (nhds x) < (p.2 : EReal) := by
          simpa [L] using hp2
        exact frequently_lt_of_liminf_lt (by isBoundedDefault) this
      exact (hlt.and_eventually hgt).mono fun y hy ↦ hps ⟨hy.2, hy.1⟩

private theorem liminf_mem_sequentialLiminfValuesAt [MetricSpace X] (f : X → EReal) (x : X) :
    liminf f (nhds x) ∈ sequentialLiminfValuesAt f x := by
  let L := liminf f (nhds x)
  have hcluster : ClusterPt L (map f (nhds x)) := by
    simpa [L] using clusterPt_liminf_map_nhds f x
  have hne : NeBot (nhds x ⊓ comap f (nhds L)) := by
    have hmap : NeBot (map f (comap f (nhds L) ⊓ nhds x)) := by
      rw [show map f (comap f (nhds L) ⊓ nhds x) = nhds L ⊓ map f (nhds x) by
        simpa [inf_comm] using (Filter.push_pull' f (nhds x) (nhds L))]
      simpa [ClusterPt] using hcluster
    have hsource : NeBot (comap f (nhds L) ⊓ nhds x) := NeBot.of_map hmap
    simpa [inf_comm] using hsource
  haveI : NeBot (nhds x ⊓ comap f (nhds L)) := hne
  rcases exists_seq_tendsto (nhds x ⊓ comap f (nhds L)) with ⟨u, hu⟩
  have hu' := tendsto_inf.1 hu
  refine ⟨u, hu'.1, ?_⟩
  have hfu : Tendsto (f ∘ u) atTop (nhds L) := by
    simpa [tendsto_iff_comap, Function.comp, comap_comap] using hu'.2
  simpa [L] using hfu.liminf_eq

private theorem liminfAt_le_of_mem_sequentialLiminfValuesAt [TopologicalSpace X] (f : X → EReal)
    (x : X) {r : EReal} (hr : r ∈ sequentialLiminfValuesAt f x) :
    liminf f (nhds x) ≤ r := by
  rcases hr with ⟨u, hu, rfl⟩
  simpa using (liminf_le_liminf_of_le hu : liminf f (nhds x) ≤ liminf f (map u atTop))

-- Proof sketch: the lower bound follows from the monotonicity of `Filter.liminf` under any
-- convergent sequence `u : ℕ → X`. For the reverse inequality, use the metric neighborhood basis
-- of shrinking balls around `x`, choose points whose function values approximate the infimum on
-- each ball, and show that the resulting sequence converges to `x` and realizes the neighborhood
-- `liminf`.
/-- Lemma 1.42: in a metric space, the neighborhood-filter limit inferior of `f` at `x` is the
minimum of the sequential limit inferiors along sequences converging to `x`. -/
theorem liminfAt_isLeast_sequentialLiminfValues [MetricSpace X] (f : X → EReal)
    (x : X) : IsLeast (sequentialLiminfValuesAt f x) (liminf f (nhds x)) := by
  exact ⟨liminf_mem_sequentialLiminfValuesAt f x, fun r hr ↦
    liminfAt_le_of_mem_sequentialLiminfValuesAt f x hr⟩

/-! Source item:
`TheoremLib/Attouch_Convergence_of_a_Relaxed_Inertial_Forward_Backward_Algorithm_for_Structured_Monotone_Inclusions_2019/items/ext_cor_1`
(Corollary 3.7, Combettes--Yamada: two real-analysis helpers). -/

/-- A nonnegative sequence `a` bounded above by the successive differences
`d k - d (k + 1)` of a nonnegative sequence `d` is summable (by telescoping). -/
theorem ext_cor_1_summable_of_nonneg_le_diff (a d : ℕ → ℝ)
    (ha : ∀ k, 0 ≤ a k) (hd : ∀ k, a k ≤ d k - d (k + 1))
    (hd_nonneg : ∀ k, 0 ≤ d k) : Summable a := by
  apply summable_of_sum_range_le ha
  intro n
  calc
    ∑ k ∈ Finset.range n, a k ≤ ∑ k ∈ Finset.range n, (d k - d (k + 1)) :=
      Finset.sum_le_sum fun k _ => hd k
    _ = d 0 - d n := by
      rw [Finset.sum_range_sub']
    _ ≤ d 0 := sub_le_self _ (hd_nonneg n)

/-- A nonnegative real sequence whose squares tend to zero tends to zero itself. -/
theorem ext_cor_1_sq_tendsto_implies_norm_tendsto_zero (r : ℕ → ℝ)
    (hr : ∀ k, 0 ≤ r k)
    (hlim : Filter.Tendsto (fun k => r k ^ 2) Filter.atTop (nhds 0)) :
    Filter.Tendsto r Filter.atTop (nhds 0) := by
  have hfun : (fun k => Real.sqrt (r k ^ 2)) = r := by
    funext k
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (hr k)]
  simpa [Function.comp_def, hfun] using (Real.continuous_sqrt.tendsto 0).comp hlim

/-! Source item:
`TheoremLib/Attouch_Convergence_of_a_Relaxed_Inertial_Forward_Backward_Algorithm_for_Structured_Monotone_Inclusions_2019/items/ext_lem_4`
(Lemma C.2: column weights with total mass one). -/


/-- A two-index family of real weights whose `k`-th column sums to `1` is summable
in that column: `∑' i, tau i k = 1` forces `Summable (fun i => tau i k)`. -/
theorem weights_summable (tau : ℕ → ℕ → ℝ)
    (hweights_sum : ∀ k, ∑' i, tau i k = 1) (k : ℕ) :
    Summable (fun i => tau i k) := by
  by_contra h
  have hz : (∑' i, tau i k) = 0 := tsum_eq_zero_of_not_summable h
  linarith [hweights_sum k]
