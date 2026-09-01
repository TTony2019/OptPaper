import Mathlib
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Topology Basic

Topological bases, closure/interior tools, compactness, Baire-style G-delta facts, and metric-space closure criteria.
-/

open _root_.EReal _root_.TopologicalSpace
open Filter Topology
open Set TopologicalSpace
open Set
open scoped Topology
open Metric
open Set Filter

/-! Source item: Chap01/Text_1_0_35 -/
universe u

/-- A set belongs to the neighborhood filter of `x` exactly when it contains an open set
containing `x`. -/
-- Proof sketch: this is a direct restatement of `mem_nhds_iff`, rearranging the existential
-- witnesses into the textbook order `IsOpen U ∧ x ∈ U ∧ U ⊆ V`.
theorem mem_nhds_iff_exists_open_subset {X : Type u} [TopologicalSpace X] {x : X} {V : Set X} :
    V ∈ nhds x ↔ ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ U ⊆ V := by
  simpa [and_assoc, and_left_comm, and_comm] using
    (mem_nhds_iff : V ∈ nhds x ↔ ∃ U ⊆ V, IsOpen U ∧ x ∈ U)

/-! Source item: Chap01/Text_1_0_37 -/

namespace TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/-- Text 1.0.37 in the textbook's unpacked basis hypotheses. -/
theorem open_eq_sUnion_basis_subsets {B : Set (Set X)} (hB_open : ∀ V ∈ B, IsOpen V)
    (hB_basis : ∀ x (U : Set X), x ∈ U → IsOpen U → ∃ V ∈ B, x ∈ V ∧ V ⊆ U)
    {U : Set X} (hU : IsOpen U) :
    U = ⋃₀ {V ∈ B | V ⊆ U} := by
  simpa using (isTopologicalBasis_of_isOpen_of_nhds hB_open hB_basis).open_eq_sUnion' hU

end TopologicalSpace

/-! Source item: Chap01/Text_1_0_38 -/

/- A point belongs to `interior C` exactly when `C` is a neighborhood of that point. -/
#check mem_interior_iff_mem_nhds

/-- Text 1.0.38: equivalently, a point lies in `interior C` exactly when `C` contains a
neighborhood of that point. -/
theorem mem_interior_iff_exists_mem_nhds_subset {X : Type u} [TopologicalSpace X] {x : X}
    {C : Set X} : x ∈ interior C ↔ ∃ V : Set X, V ∈ 𝓝 x ∧ V ⊆ C := by
  rw [mem_interior_iff_mem_nhds]
  constructor
  · intro hC
    exact ⟨C, hC, fun _ hx ↦ hx⟩
  · rintro ⟨V, hV, hVC⟩
    exact Filter.mem_of_superset hV hVC

/-! Source item: Chap01/Text_1_0_41 -/
universe v

namespace TopologicalSpace

variable {X₁ : Type u} [TopologicalSpace X₁]
variable {X₂ : Type v} [TopologicalSpace X₂]

/-- Text 1.0.41: if `B₁` and `B₂` are bases for the given topologies on `X₁` and `X₂`, then the
family of rectangles `U ×ˢ V` with `U ∈ B₁` and `V ∈ B₂` is a basis for the product topology on
`X₁ × X₂`. This is the textbook set-builder form of the canonical theorem
`TopologicalSpace.IsTopologicalBasis.prod`. -/
theorem IsTopologicalBasis.rectangles {B₁ : Set (Set X₁)} {B₂ : Set (Set X₂)}
    (h₁ : IsTopologicalBasis B₁) (h₂ : IsTopologicalBasis B₂) :
    IsTopologicalBasis {s : Set (X₁ × X₂) | ∃ U ∈ B₁, ∃ V ∈ B₂, s = U ×ˢ V} := by
  have hrect :
      Set.image2 (· ×ˢ ·) B₁ B₂ =
        {s : Set (X₁ × X₂) | ∃ U ∈ B₁, ∃ V ∈ B₂, s = U ×ˢ V} := by
    ext s
    simp [Set.mem_image2, eq_comm]
  rw [← hrect]
  exact h₁.prod h₂

end TopologicalSpace

/-! Source item: Chap01/Text_1_0_48 -/

/-- Text 1.0.48: the usual topology on `ℝ` has as a basis the family of open intervals
`(a, b)` with `a < b`. -/
-- Proof sketch: apply `isTopologicalBasis_of_isOpen_of_nhds`; openness of each interval is
-- `isOpen_Ioo`, and the neighborhood basis condition is exactly
-- `mem_nhds_iff_exists_Ioo_subset`.
theorem real_isTopologicalBasis_Ioo :
    TopologicalSpace.IsTopologicalBasis { s : Set ℝ | ∃ a b, a < b ∧ s = Ioo a b } := by
  refine isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro s ⟨a, b, hab, rfl⟩
    exact isOpen_Ioo
  · intro x s hx hs
    rcases mem_nhds_iff_exists_Ioo_subset.1 (hs.mem_nhds hx) with ⟨a, b, hxIoo, hIoo⟩
    exact ⟨Ioo a b, ⟨a, b, hxIoo.1.trans hxIoo.2, rfl⟩, hxIoo, hIoo⟩

/-! Source item: Chap01/Text_1_0_49 -/

namespace EReal

/-- The family of real open intervals together with the lower and upper infinite rays in `EReal`.
-/
abbrev realIntervalRayBasis : Set (Set EReal) :=
  {s | (∃ a b : ℝ, s = Ioo (a : EReal) (b : EReal)) ∨
      (∃ ξ : ℝ, s = Iio (ξ : EReal)) ∨
      ∃ ξ : ℝ, s = Ioi (ξ : EReal)}

/-- Text 1.0.49: the canonical topology on the extended real line `EReal` has as a basis the
family of all embedded real open intervals `(a, b)` together with the lower rays `[-∞, ξ)` and
the upper rays `(ξ, +∞]`, represented in Lean by `Ioo (a : EReal) (b : EReal)`, `Iio (ξ : EReal)`,
and `Ioi (ξ : EReal)`. -/
-- Proof sketch: use that `EReal` carries the order topology and identify the textbook basis as
-- the standard basis by open intervals at finite points together with the one-sided ray bases at
-- `⊥` and `⊤`.
theorem realIntervalRayBasis_isTopologicalBasis :
    TopologicalSpace.IsTopologicalBasis realIntervalRayBasis := by
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · intro s hs
    rcases hs with hs | hs
    · rcases hs with ⟨a, b, rfl⟩
      exact isOpen_Ioo
    · rcases hs with hs | hs
      · rcases hs with ⟨ξ, rfl⟩
        exact isOpen_Iio
      · rcases hs with ⟨ξ, rfl⟩
        exact isOpen_Ioi
  · intro x u hx hu
    by_cases hbot : x = ⊥
    · subst hbot
      rcases mem_nhds_bot_iff.mp (IsOpen.mem_nhds hu hx) with ⟨ξ, hξ⟩
      exact ⟨Iio (ξ : EReal), Or.inr <| Or.inl ⟨ξ, rfl⟩, bot_lt_coe ξ, hξ⟩
    by_cases htop : x = ⊤
    · subst htop
      rcases mem_nhds_top_iff.mp (IsOpen.mem_nhds hu hx) with ⟨ξ, hξ⟩
      exact ⟨Ioi (ξ : EReal), Or.inr <| Or.inr ⟨ξ, rfl⟩, coe_lt_top ξ, hξ⟩
    lift x to ℝ using ⟨htop, hbot⟩
    have hpre : Real.toEReal ⁻¹' u ∈ 𝓝 x := by
      simpa [nhds_coe] using (IsOpen.mem_nhds hu hx)
    rcases mem_nhds_iff_exists_Ioo_subset.mp hpre with ⟨a, b, hxab, hab⟩
    refine ⟨Ioo (a : EReal) (b : EReal), Or.inl ⟨a, b, rfl⟩, ?_, ?_⟩
    · simpa using hxab
    · simpa [image_coe_Ioo] using image_subset_iff.mpr hab

end EReal

/-! Source item: Chap01/Text_1_0_50 -/
/-- Text 1.0.50 (1): the real line with its usual metric topology is Hausdorff. -/
theorem real_t2Space : T2Space ℝ := inferInstance

/-- Text 1.0.50 (2): the real line with its usual topology is not compact. -/
theorem real_not_compact : ¬ CompactSpace ℝ := by
  simpa [not_compactSpace_iff] using (inferInstance : NoncompactSpace ℝ)

/-! Source item: Chap01/Text_1_0_51 -/
/-- Text 1.0.51: the extended real line `EReal = [-∞, +∞]`, equipped with its canonical order
topology, is compact. The textbook description by real intervals together with rays at `⊥` and
`⊤` describes this same topology. -/
theorem extendedReal_compactSpace : CompactSpace EReal := inferInstance

/-! Source item: Chap01/Lemma_1_12 -/

/-- Lemma 1.12: a compact subset of a Hausdorff topological space is closed. -/
theorem isClosed_of_isCompact
    {X : Type u} [TopologicalSpace X] [T2Space X] {C : Set X} :
    IsCompact C → IsClosed C :=
  IsCompact.isClosed

/-! Source item: Chap01/Lemma_1_40 -/

variable {α : Type u} [MetricSpace α]

/-- Lemma 1.40: if every intersection `C ∩ B[z; n]` with a closed ball of integer radius
`n ≥ 1` centered at `z` is closed, then `C` itself is closed. -/
-- Proof sketch: Use the sequential characterization of closed sets in metric spaces. A sequence
-- in `C` converging in the ambient space is bounded, so it is contained in some
-- `closedBall z n` with `1 ≤ n`; the assumed closedness of `C ∩ closedBall z n`
-- then forces the limit to lie in `C`.
theorem isClosed_of_isClosed_inter_closedBall_nat (C : Set α) (z : α)
    (hC : ∀ n : ℕ, 1 ≤ n → IsClosed (C ∩ closedBall z n)) :
    IsClosed C := by
  rw [← isSeqClosed_iff_isClosed]
  intro u x hu hx
  -- A convergent sequence has bounded range, so one integer closed ball captures every term.
  obtain ⟨n, hn, hrange⟩ : ∃ n : ℕ, 1 ≤ n ∧ Set.range u ⊆ closedBall z n := by
    obtain ⟨r, hr, hsubset⟩ := (isBounded_range_of_tendsto u hx).subset_closedBall_lt 0 z
    refine ⟨Nat.ceil r, Nat.one_le_ceil_iff.mpr hr, ?_⟩
    exact hsubset.trans <| closedBall_subset_closedBall (Nat.le_ceil r)
  have hu_inter : ∀ k, u k ∈ C ∩ closedBall z n := by
    intro k
    exact ⟨hu k, hrange (Set.mem_range_self k)⟩
  -- Closedness of the trapped intersection forces the limit into the same intersection.
  have hx_inter : x ∈ C ∩ closedBall z n := by
    exact (hC n hn).mem_of_tendsto hx (Filter.Eventually.of_forall hu_inter)
  exact hx_inter.1

/-! Source item: Chap01/Lemma_1_41 -/

variable {X : Type u} [MetricSpace X] {C : Set X}

/-- Lemma 1.41: a compact subset of a metric space is closed and bounded. -/
theorem isClosed_and_isBounded_of_isCompact (hC : IsCompact C) :
    IsClosed C ∧ Bornology.IsBounded C := by
  exact ⟨hC.isClosed, hC.isBounded⟩

/-! Source item: Chap01/Fact_1_38 -/

variable {X : Type u} [MetricSpace X]
variable {Y : Type v} [TopologicalSpace Y]

/-- Fact 1.38: for a map from a metric space to a topological space, continuity is equivalent to
sequential continuity; no Hausdorff assumption on the codomain is needed. -/
-- Proof sketch: A metric space is first countable, hence a sequential space. Apply the existing
-- theorem `continuous_iff_seqContinuous` for maps out of sequential spaces.
theorem continuous_iff_seqContinuous_of_metricSpace {f : X → Y} :
    Continuous f ↔ SeqContinuous f := by
  -- Metric spaces are sequential spaces, so the general sequential-space criterion applies.
  -- This matches the textbook route while delegating the topology infrastructure to mathlib.
  simpa using (continuous_iff_seqContinuous : Continuous f ↔ SeqContinuous f)

/-! Source item: Chap01/Fact_1_39 -/

variable {X : Type u} [MetricSpace X]

/-- Fact 1.39: a subset of a metric space is compact if and only if it is sequentially compact. -/
-- Proof sketch: metric spaces are pseudometrizable, so this is the canonical mathlib theorem
-- `isCompact_iff_isSeqCompact` specialized to the subset `C`.
theorem isCompact_iff_isSeqCompact_of_metricSpace (C : Set X) :
    IsCompact C ↔ IsSeqCompact C := by
  simpa using (isCompact_iff_isSeqCompact : IsCompact C ↔ IsSeqCompact C)

/-! Source item: Chap01/Lemma_1_43 -/


variable {X : Type u} [MetricSpace X]

/-- Helper for Lemma 1.43: antitonicity pushes the boundedness of the initial set to every later
set in the chain. -/
lemma bounded_of_antitone_base
    (C : ℕ → Set X) (hanti : Antitone C) (hbdd : Bornology.IsBounded (C 0)) :
    ∀ n, Bornology.IsBounded (C n) := by
  -- Every `C n` sits inside `C 0`, so the bounded initial set controls all later sets.
  intro n
  exact Bornology.IsBounded.subset hbdd (hanti (Nat.zero_le n))

/-- Helper for Lemma 1.43: every finite intersection in an antitone nonempty family is nonempty. -/
lemma finite_intersection_nonempty_of_antitone
    (C : ℕ → Set X) (hnonempty : ∀ n, (C n).Nonempty) (hanti : Antitone C) :
    ∀ N, (⋂ n ≤ N, C n).Nonempty := by
  -- A point of `C N` belongs to each earlier `C n` because the family is decreasing.
  intro N
  rcases hnonempty N with ⟨x, hx⟩
  refine ⟨x, mem_iInter.2 (fun n ↦ mem_iInter.2 (fun hn ↦ ?_))⟩
  exact hanti hn hx

/-- Helper for Lemma 1.43: two points lying in all sets of the chain must coincide once the
diameters converge to `0`. -/
lemma eq_of_mem_iInter_of_diam_tendsto_zero
    (C : ℕ → Set X) (hbounded : ∀ n, Bornology.IsBounded (C n))
    (hdiam : Tendsto (Metric.diam ∘ C) atTop (nhds 0))
    {x y : X} (hx : x ∈ ⋂ n, C n) (hy : y ∈ ⋂ n, C n) :
    x = y := by
  -- If `x ≠ y`, the positive distance `dist x y` eventually dominates the diameters.
  by_contra hxy
  have hxy_pos : 0 < dist x y := dist_pos.mpr hxy
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hdiam (dist x y) hxy_pos
  have hxN : x ∈ C N := mem_iInter.mp hx N
  have hyN : y ∈ C N := mem_iInter.mp hy N
  have hdist_le : dist x y ≤ Metric.diam (C N) :=
    Metric.dist_le_diam_of_mem (hbounded N) hxN hyN
  have hdiam_lt : Metric.diam (C N) < dist x y := by
    -- The convergence hypothesis turns the metric-neighborhood statement into a real inequality.
    have hsmall := hN N le_rfl
    simpa [Function.comp, Real.dist_eq,
      abs_of_nonneg (Metric.diam_nonneg : 0 ≤ Metric.diam (C N))] using hsmall
  exact not_lt_of_ge hdist_le hdiam_lt

variable [CompleteSpace X]

/-- Lemma 1.43 (Cantor): in a complete metric space, a bounded antitone sequence of nonempty
closed sets whose diameters converge to `0` has intersection equal to a singleton. -/
-- Proof sketch: choose points `x n ∈ C n`; the nesting and diameter hypothesis make `(x n)` Cauchy,
-- so completeness gives a limit `x`; closedness puts `x` in every `C n`; uniqueness follows because
-- any two points in every `C n` have distance bounded by `Metric.diam (C n)`, which tends to `0`;
-- the boundedness hypothesis ensures that `Metric.diam` has its intended metric meaning.
theorem exists_eq_singleton_iInter_of_nonempty_isClosed_antitone_diam_tendsto_zero
    (C : ℕ → Set X) (hnonempty : ∀ n, (C n).Nonempty) (hclosed : ∀ n, IsClosed (C n))
    (hanti : Antitone C) (hbdd : Bornology.IsBounded (C 0))
    (hdiam : Tendsto (Metric.diam ∘ C) atTop (nhds 0)) :
    ∃ x : X, (⋂ n, C n) = {x} := by
  -- Route correction: use mathlib's packaged Cantor-intersection existence theorem, then prove
  -- uniqueness separately from the vanishing-diameter estimate.
  let hbounded : ∀ n, Bornology.IsBounded (C n) :=
    bounded_of_antitone_base C hanti hbdd
  let hfinite : ∀ N, (⋂ n ≤ N, C n).Nonempty :=
    finite_intersection_nonempty_of_antitone C hnonempty hanti
  have hnonempty_iInter : (⋂ n, C n).Nonempty :=
    Metric.nonempty_iInter_of_nonempty_biInter hclosed hbounded hfinite <|
      by simpa [Function.comp] using hdiam
  rcases hnonempty_iInter with ⟨x, hx⟩
  refine ⟨x, Set.eq_singleton_iff_unique_mem.2 ⟨hx, ?_⟩⟩
  -- Any other point in the total intersection equals `x` by the diameter-collapse argument.
  intro y hy
  exact (eq_of_mem_iInter_of_diam_tendsto_zero C hbounded hdiam (x := x) (y := y) hx hy).symm

/-- Lemma 1.43 (Cantor), in the textbook successor-step formulation with bounded initial set. -/
theorem exists_eq_singleton_iInter_of_nonempty_isClosed_succ_subset_diam_tendsto_zero
    (C : ℕ → Set X) (hnonempty : ∀ n, (C n).Nonempty) (hclosed : ∀ n, IsClosed (C n))
    (hnest : ∀ n, C (n + 1) ⊆ C n) (hbdd : Bornology.IsBounded (C 0))
    (hdiam : Tendsto (fun n ↦ Metric.diam (C n)) atTop (nhds 0)) :
    ∃ x : X, (⋂ n, C n) = {x} := by
  simpa [Function.comp] using
    exists_eq_singleton_iInter_of_nonempty_isClosed_antitone_diam_tendsto_zero
      C hnonempty hclosed (antitone_nat_of_succ_le hnest) hbdd hdiam

/-! Source item: Chap01/Lemma_1_44 -/


section BaireSpace

variable {X : Type u} [TopologicalSpace X] [BaireSpace X]

/-- Baire-space form of the corrected open-set clause used in Lemma 1.44: for a countable family
of open sets, taking the interior after the closure of the intersection agrees with taking the
interior after intersecting the closures. -/
theorem interior_closure_iInter_eq_interior_iInter_closure_of_isOpen
    (U : ℕ → Set X) (hopen : ∀ n, IsOpen (U n)) :
    interior (closure (⋂ n, U n)) = interior (⋂ n, closure (U n)) := by
  let s : Set X := interior (⋂ n, closure (U n))
  have hs_open : IsOpen s := isOpen_interior
  have hs_subset_closure : ∀ n, s ⊆ closure (U n) := fun n ↦
    interior_subset.trans <| iInter_subset _ n
  have hdense : ∀ n, Dense (((↑) : s → X) ⁻¹' U n) := fun n ↦ by
    rw [dense_iff_closure_eq]
    apply eq_univ_iff_forall.2
    intro x
    rw [← hs_open.isOpenMap_subtype_val.preimage_closure_eq_closure_preimage
      continuous_subtype_val]
    exact hs_subset_closure n x.2
  let _ : BaireSpace s := hs_open.baireSpace
  have hpreimage_dense :
      Dense (⋂ n, (((↑) : s → X) ⁻¹' U n)) :=
    dense_iInter_of_isOpen_nat (fun n ↦ (hopen n).preimage continuous_subtype_val) hdense
  have hs_subset : s ⊆ closure (⋂ n, U n) := by
    intro x hx
    have hx' : x ∈ closure (((↑) : s → X) '' (⋂ n, (((↑) : s → X) ⁻¹' U n))) :=
      (Subtype.dense_iff.mp hpreimage_dense) hx
    exact (closure_mono (by
      rintro y ⟨y, hy, rfl⟩
      have hy' : ∀ n, (y : X) ∈ U n := by
        simpa [Set.mem_iInter] using hy
      exact mem_iInter.2 hy') hx')
  refine Subset.antisymm ?_ (interior_maximal hs_subset hs_open)
  exact interior_mono <|
    closure_minimal (iInter_mono fun n ↦ subset_closure) <|
      isClosed_iInter fun _ ↦ isClosed_closure

/-- Baire-space form of the corrected closed-set clause used in Lemma 1.44, dual to
`interior_closure_iInter_eq_interior_iInter_closure_of_isOpen`. -/
theorem closure_iUnion_interior_eq_closure_interior_iUnion_of_isClosed
    (C : ℕ → Set X) (hclosed : ∀ n, IsClosed (C n)) :
    closure (⋃ n, interior (C n)) = closure (interior (⋃ n, C n)) := by
  let U : ℕ → Set X := fun n ↦ (C n)ᶜ
  have hU :
      interior (closure (⋂ n, U n)) = interior (⋂ n, closure (U n)) :=
    interior_closure_iInter_eq_interior_iInter_closure_of_isOpen U
      (fun n ↦ (hclosed n).isOpen_compl)
  have hU' := congrArg Compl.compl hU
  rw [← closure_compl, ← closure_compl] at hU'
  simpa [U, compl_iInter, compl_iUnion, ← interior_compl] using hU'.symm

end BaireSpace

section CompleteMetric

variable {X : Type u} [MetricSpace X] [CompleteSpace X]

/-- Lemma 1.44 [Ursescu]: specialized to complete metric spaces through their canonical
`BaireSpace` instance, the corrected Baire-category identities for countable unions of closed sets
and countable intersections of open sets hold with the necessary closure operators. -/
theorem lemma_1_44 :
    (∀ C : ℕ → Set X, (∀ n, IsClosed (C n)) →
      closure (⋃ n, interior (C n)) = closure (interior (⋃ n, C n))) ∧
    ∀ U : ℕ → Set X, (∀ n, IsOpen (U n)) →
      interior (closure (⋂ n, U n)) = interior (⋂ n, closure (U n)) := by
  constructor
  · intro C hclosed
    exact closure_iUnion_interior_eq_closure_interior_iUnion_of_isClosed C hclosed
  · intro U hopen
    exact interior_closure_iInter_eq_interior_iInter_closure_of_isOpen U hopen

end CompleteMetric

/-! Source item: Chap01/Corollary_1_45 -/


variable {X : Type u} [MetricSpace X] [CompleteSpace X]

/-- Corollary 1.45: in a complete metric space, the intersection of a sequence of dense open
subsets is again a dense `Gδ` subset. -/
-- Proof sketch: use
-- `interior_closure_iInter_eq_interior_iInter_closure_of_isOpen`
-- to identify
-- `interior (closure (⋂ n, C n))` with `interior (⋂ n, closure (C n)) = univ`, hence
-- `closure (⋂ n, C n) = univ`, and conclude with `IsGδ.iInter_of_isOpen`.
theorem dense_isGδ_iInter_of_dense_open (C : ℕ → Set X)
    (h_open : ∀ n, IsOpen (C n)) (h_dense : ∀ n, Dense (C n)) :
    Dense (⋂ n, C n) ∧ IsGδ (⋂ n, C n) := by
  constructor
  · rw [dense_iff_closure_eq]
    have hclosure : ∀ n, closure (C n) = univ := fun n ↦ Dense.closure_eq (h_dense n)
    have hinterior :
        interior (closure (⋂ n, C n)) = univ := by
      calc
        interior (closure (⋂ n, C n))
            = interior (⋂ n, closure (C n)) :=
              interior_closure_iInter_eq_interior_iInter_closure_of_isOpen C h_open
        _ = univ := by simp [hclosure]
    refine subset_antisymm (subset_univ _) ?_
    simpa [hinterior] using
      (interior_subset : interior (closure (⋂ n, C n)) ⊆ closure (⋂ n, C n))
  · -- The `Gδ` part is the countable intersection of the given open sets.
    exact IsGδ.iInter_of_isOpen h_open

/-! Source item: Attouch_Complexity_Analysis_Based_on_Tuning_the_Viscosity_Parameter_of_the_Su_Boyd_Cand_s_Inertial_Gradient_Dynamics_2024 (ext_thm_4) -/

/-- Finite-dimensional Ascoli--Arzela compactness on a compact interval. -/
theorem finite_dimensional_ascoli_arzela {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    (K : Set ℝ) (hK : IsCompact K) (u : ℕ → ℝ → E)
    (hbounded : ∃ R : ℝ, ∀ n t, t ∈ K → ‖u n t‖ ≤ R)
    (hequicont : ∀ ε > 0, ∃ δ > 0, ∀ n s t, s ∈ K → t ∈ K →
      |s - t| < δ → ‖u n s - u n t‖ < ε) :
    ∃ (φ : ℕ → ℕ) (g : ℝ → E), StrictMono φ ∧
      ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ t, t ∈ K → ‖u (φ n) t - g t‖ < ε := by
  by_cases hKempty : K = ∅
  · refine ⟨id, fun _ => 0, strictMono_id, ?_⟩
    simp [hKempty]
  · letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
    classical
    have hucont : ∀ n, Continuous (fun x : K => u n x) := by
      intro n
      apply (Metric.uniformContinuousOn_iff.mpr ?_).continuousOn.restrict
      intro ε hε
      rcases hequicont ε hε with ⟨δ, hδ, hmod⟩
      refine ⟨δ, hδ, ?_⟩
      intro s hs t ht hst
      simpa only [Real.dist_eq, dist_eq_norm] using hmod n s t hs ht hst
    let A : ℕ → BoundedContinuousFunction K E := fun n =>
      BoundedContinuousFunction.mkOfCompact ⟨fun x => u n x, hucont n⟩
    have hUE : UniformEquicontinuous (fun n : ℕ => fun x : K => A n x) := by
      rw [Metric.uniformEquicontinuous_iff]
      intro ε hε
      rcases hequicont ε hε with ⟨δ, hδ, hmod⟩
      refine ⟨δ, hδ, ?_⟩
      intro x y hxy n
      simpa only [Real.dist_eq, dist_eq_norm] using hmod n x y x.property y.property hxy
    have hEqui : Equicontinuous ((↑) : Set.range A → K → E) := by
      choose idx hidx using fun f : Set.range A => f.property
      have h := hUE.equicontinuous.comp idx
      convert h using 1
      ext f x
      exact DFunLike.congr_fun (hidx f).symm x
    rcases hbounded with ⟨R, hR⟩
    let R' := max R 0
    letI : ProperSpace E := FiniteDimensional.proper ℝ E
    have hball : ∀ n (x : K), A n x ∈ Metric.closedBall (0 : E) R' := by
      intro n x
      rw [Metric.mem_closedBall]
      change dist (u n x) 0 ≤ R'
      rw [dist_zero_right]
      exact (hR n x x.property).trans (le_max_left _ _)
    have hcompact := BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : E) R')
      (isCompact_closedBall 0 R') (Set.range A) (by
        rintro f x ⟨n, rfl⟩
        exact hball n x) hEqui
    rcases hcompact.tendsto_subseq (fun n => subset_closure ⟨n, rfl⟩) with
      ⟨gB, hgB, φ, hφ, hconv⟩
    refine ⟨φ, fun t => if ht : t ∈ K then gB ⟨t, ht⟩ else 0, hφ, ?_⟩
    intro ε hε
    rcases Metric.tendsto_atTop.mp hconv ε hε with ⟨N, hN⟩
    refine ⟨N, ?_⟩
    intro n hn t ht
    have hdist := ContinuousMap.dist_apply_le_dist (f := (A (φ n)).toContinuousMap)
      (g := gB.toContinuousMap) ⟨t, ht⟩
    change ‖u (φ n) t - (if h : t ∈ K then gB ⟨t, h⟩ else 0)‖ < ε
    rw [dif_pos ht]
    rw [← dist_eq_norm]
    refine lt_of_le_of_lt ?_ (hN n hn)
    simpa [A] using hdist
