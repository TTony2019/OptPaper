import Mathlib
import Foundation.Analysis.ExtendedRealFunctions

/-!
# Analysis Semicontinuity

Lower semicontinuity, liminf-at constructions, envelopes, finite infima, sums, composition, and compact minimizers.
-/

open _root_.EReal
open ERealFunction
open Filter
open scoped Topology
open Set
open scoped BigOperators

/-! Source item: Chap01/Text_1_0_53_1_33 -/

universe u v

/-- Text 1.0.53 (1.33), neighborhood form: lower semicontinuity of an extended-real-valued
function at a point is equivalently the condition that every strict lower bound of `f x` remains a
strict lower bound of `f` on some neighborhood of `x`. -/
theorem lowerSemicontinuousAt_iff_exists_mem_nhds_forall_lt
    {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X} :
    LowerSemicontinuousAt f x ↔
      ∀ ξ, ξ < f x → ∃ V : Set X, V ∈ 𝓝 x ∧ ∀ y ∈ V, ξ < f y := by
  rw [lowerSemicontinuousAt_iff]
  constructor
  · intro h ξ hξ
    have hlt : {y : X | ξ < f y} ∈ 𝓝 x := h ξ hξ
    rcases
        (Filter.exists_mem_subset_iff :
          (∃ V ∈ 𝓝 x, V ⊆ {y : X | ξ < f y}) ↔ {y : X | ξ < f y} ∈ 𝓝 x).2 hlt with
      ⟨V, hV, hltV⟩
    exact ⟨V, hV, fun y hy ↦ hltV hy⟩
  · intro h ξ hξ
    rcases h ξ hξ with ⟨V, hV, hlt⟩
    exact mem_of_superset hV (fun y hy ↦ hlt y hy)

/-! Source item: Chap01/Text_1_0_54 -/


/-- Text 1.0.54 (1): an extended-real-valued function is lower semicontinuous on the whole space
exactly when it is lower semicontinuous at every point. -/
-- Proof sketch: this is the direct pointwise expansion of the canonical predicate
-- `LowerSemicontinuous`.
theorem lowerSemicontinuous_iff_forall_lowerSemicontinuousAt
    {X : Type u} [TopologicalSpace X] {f : X → EReal} :
    LowerSemicontinuous f ↔ ∀ x, LowerSemicontinuousAt f x :=
  lowerSemicontinuous_iff

/-- Text 1.0.54 (2): an extended-real-valued function is upper semicontinuous at `x` exactly when
its negation is lower semicontinuous at `x`. -/
-- Proof sketch: use that negation on `EReal` reverses the order and transports the defining
-- neighborhoods for lower semicontinuity to those for upper semicontinuity.
theorem upperSemicontinuousAt_iff_lowerSemicontinuousAt_neg
    {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X} :
    UpperSemicontinuousAt f x ↔ LowerSemicontinuousAt (fun y ↦ -f y) x := by
  rw [upperSemicontinuousAt_iff, lowerSemicontinuousAt_iff]
  constructor
  · intro h y hy
    have hxy : f x < -y := EReal.lt_neg_comm.mp hy
    simpa [EReal.lt_neg_comm] using h (-y) hxy
  · intro h y hy
    have hxy : -y < -f x := EReal.neg_lt_neg_iff.2 hy
    simpa [EReal.neg_lt_neg_iff] using h (-y) hxy

private lemma point_mem_of_frequently {X : Type u} [TopologicalSpace X] {x : X}
    {P : X → Prop} (hP : ∃ᶠ z in nhds x, P z) {U : Set X} (hU : U ∈ nhds x) :
    ∃ z, z ∈ U ∧ P z := by
  have hBoth : ∃ᶠ z in nhds x, P z ∧ z ∈ U := by
    simpa [and_left_comm, and_assoc] using hP.and_eventually hU
  rcases hBoth.exists with ⟨z, hzP, hzU⟩
  exact ⟨z, hzU, hzP⟩

private structure NeighborhoodIndex {X : Type u} [TopologicalSpace X] (x : X) where
  carrier : Set X
  mem_nhds : carrier ∈ nhds x

private instance {X : Type u} [TopologicalSpace X] (x : X) : Nonempty (NeighborhoodIndex x) :=
  ⟨⟨Set.univ, Filter.univ_mem⟩⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : LE (NeighborhoodIndex x) :=
  ⟨fun U W ↦ W.carrier ⊆ U.carrier⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : Preorder (NeighborhoodIndex x) where
  le := (· ≤ ·)
  le_refl U := by
    intro y hy
    exact hy
  le_trans U V W hUV hVW := by
    intro y hy
    exact hUV (hVW hy)

private def infNeighborhoodIndex {X : Type u} [TopologicalSpace X] {x : X}
    (U W : NeighborhoodIndex x) : NeighborhoodIndex x :=
  ⟨U.carrier ∩ W.carrier, Filter.inter_mem U.mem_nhds W.mem_nhds⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} :
    IsDirectedOrder (NeighborhoodIndex x) :=
  ⟨fun U W ↦
    ⟨infNeighborhoodIndex U W,
      by
        intro y hy
        exact hy.1,
      by
        intro y hy
        exact hy.2⟩⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} :
    IsDirectedOrder (ULift.{v} (NeighborhoodIndex x)) :=
  ⟨fun U W ↦
    ⟨ULift.up (infNeighborhoodIndex U.down W.down),
      by
        intro y hy
        exact hy.1,
      by
        intro y hy
        exact hy.2⟩⟩

private noncomputable def badUpperNet {X : Type u} [TopologicalSpace X]
    {f : X → EReal} {x : X} {y : EReal} (hfreq : ∃ᶠ z in nhds x, y ≤ f z) :
    NeighborhoodIndex x → X :=
  fun U ↦ Classical.choose (point_mem_of_frequently hfreq U.mem_nhds)

private lemma badUpperNet_mem {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X}
    {y : EReal} (hfreq : ∃ᶠ z in nhds x, y ≤ f z) (U : NeighborhoodIndex x) :
    badUpperNet hfreq U ∈ U.carrier := by
  exact (Classical.choose_spec (point_mem_of_frequently hfreq U.mem_nhds)).1

private lemma le_badUpperNet {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X}
    {y : EReal} (hfreq : ∃ᶠ z in nhds x, y ≤ f z) (U : NeighborhoodIndex x) :
    y ≤ f (badUpperNet hfreq U) := by
  exact (Classical.choose_spec (point_mem_of_frequently hfreq U.mem_nhds)).2

private lemma tendsto_liftedBadUpperNet {X : Type u} [TopologicalSpace X] {f : X → EReal}
    {x : X} {y : EReal} (hfreq : ∃ᶠ z in nhds x, y ≤ f z) :
    Tendsto (fun U : ULift.{v} (NeighborhoodIndex x) ↦ badUpperNet hfreq U.down) atTop
      (nhds x) := by
  rw [Filter.tendsto_def]
  intro U hU
  rw [Filter.mem_atTop_sets]
  refine ⟨ULift.up ⟨U, hU⟩, ?_⟩
  intro W hW
  exact hW (badUpperNet_mem hfreq W.down)

private structure NhdsPoint {X : Type u} [TopologicalSpace X] (x : X) where
  value : X
  carrier : Set X
  value_mem : value ∈ carrier
  carrier_mem_nhds : carrier ∈ nhds x

private instance {X : Type u} [TopologicalSpace X] (x : X) : Nonempty (NhdsPoint x) :=
  ⟨⟨x, Set.univ, by simp, by simp⟩⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : LE (NhdsPoint x) :=
  ⟨fun p q ↦ q.carrier ⊆ p.carrier⟩

private instance {X : Type u} [TopologicalSpace X] {x : X} : Preorder (NhdsPoint x) where
  le := (· ≤ ·)
  le_refl p := by
    intro y hy
    exact hy
  le_trans p q r hpq hqr := by
    intro y hy
    exact hpq (hqr hy)

private instance {X : Type u} [TopologicalSpace X] {x : X} : IsDirectedOrder (NhdsPoint x) := by
  refine ⟨?_⟩
  intro p q
  have hMemNhds : p.carrier ∩ q.carrier ∈ nhds x :=
    Filter.inter_mem p.carrier_mem_nhds q.carrier_mem_nhds
  refine ⟨⟨x, p.carrier ∩ q.carrier, mem_of_mem_nhds hMemNhds, hMemNhds⟩, ?_, ?_⟩
  · intro y hy
    exact hy.1
  · intro y hy
    exact hy.2

private instance {X : Type u} [TopologicalSpace X] {x : X} :
    IsDirectedOrder (ULift.{v} (NhdsPoint x)) :=
  ⟨fun p q ↦
    let r : NhdsPoint x := by
      have hMemNhds : p.down.carrier ∩ q.down.carrier ∈ nhds x :=
        Filter.inter_mem p.down.carrier_mem_nhds q.down.carrier_mem_nhds
      exact ⟨x, p.down.carrier ∩ q.down.carrier, mem_of_mem_nhds hMemNhds, hMemNhds⟩
    ⟨ULift.up r,
      by
        intro y hy
        exact hy.1,
      by
        intro y hy
        exact hy.2⟩⟩

private lemma tendsto_liftedNhdsPoint {X : Type u} [TopologicalSpace X] {x : X} :
    Tendsto (fun p : ULift.{v} (NhdsPoint x) ↦ p.down.value) atTop (nhds x) := by
  rw [Filter.tendsto_def]
  intro U hU
  rw [Filter.mem_atTop_sets]
  refine ⟨ULift.up ⟨x, U, mem_of_mem_nhds hU, hU⟩, ?_⟩
  intro p hp
  exact hp p.down.value_mem

private lemma continuousAt_of_tendsto_liftedNhdsPoint {X : Type u} [TopologicalSpace X]
    {f : X → EReal} {x : X}
    (h : Tendsto (fun p : ULift.{v} (NhdsPoint x) ↦ f p.down.value) atTop (nhds (f x))) :
    ContinuousAt f x := by
  rw [Filter.tendsto_def] at h
  rw [ContinuousAt, Filter.tendsto_def]
  intro V hV
  rcases (Filter.mem_atTop_sets.mp (h V hV)) with ⟨p, hp⟩
  refine Filter.mem_of_superset p.down.carrier_mem_nhds ?_
  intro y hy
  have hyV := hp (ULift.up ⟨y, p.down.carrier, hy, p.down.carrier_mem_nhds⟩) (by
    intro z hz
    exact hz)
  simpa using hyV

/-- Text 1.0.54 (2), net form: upper semicontinuity at `x` is equivalent to the limsup bound
along every convergent net `ξ`. -/
-- Proof sketch: the forward implication composes the convergent net with the canonical limsup
-- characterization `upperSemicontinuousAt_iff_limsup_le`. For the reverse implication, if some
-- threshold `y > f x` is not eventually avoided near `x`, choose from each neighborhood a point
-- where `f` stays at least `y`; the resulting neighborhood-indexed net converges to `x` and has
-- limsup at least `y`, contradicting the assumed net inequality.
theorem upperSemicontinuousAt_iff_net_limsup_le
    {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X} :
    UpperSemicontinuousAt f x ↔
      ∀ {A : Type (max u v)} [Preorder A] [IsDirectedOrder A] (ξ : A → X),
        Tendsto ξ atTop (nhds x) → limsup (f ∘ ξ) atTop ≤ f x := by
  constructor
  · intro h A _ _ ξ hξ
    calc
      limsup (f ∘ ξ) atTop = limsup f (map ξ atTop) := rfl
      _ ≤ limsup f (nhds x) := limsup_le_limsup_of_le hξ
      _ ≤ f x := h.limsup_le
  · intro h
    rw [upperSemicontinuousAt_iff]
    intro y hy
    by_contra hyEvent
    have hyFreq : ∃ᶠ z in nhds x, y ≤ f z := by
      simpa [not_lt] using Filter.not_eventually.mp hyEvent
    let ξ : ULift.{v} (NeighborhoodIndex x) → X := fun U ↦ badUpperNet hyFreq U.down
    have hξ : Tendsto ξ atTop (nhds x) := tendsto_liftedBadUpperNet hyFreq
    have hLimsup : limsup (f ∘ ξ) atTop ≤ f x := h ξ hξ
    have hyLe : y ≤ limsup (f ∘ ξ) atTop := by
      refine le_limsup_of_frequently_le ?_
      exact Filter.Frequently.of_forall fun U ↦ le_badUpperNet hyFreq U.down
    exact (not_le_of_gt hy) (hyLe.trans hLimsup)

/-- Text 1.0.54 (3): an extended-real-valued function is continuous at `x` exactly when it is both
lower semicontinuous and upper semicontinuous at `x`. -/
-- Proof sketch: apply the standard equivalence between continuity at a point and simultaneous
-- lower and upper semicontinuity.
theorem continuousAt_iff_lower_and_upperSemicontinuousAt
    {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X} :
    ContinuousAt f x ↔ LowerSemicontinuousAt f x ∧ UpperSemicontinuousAt f x :=
  continuousAt_iff_lower_upperSemicontinuousAt

/-- Text 1.0.54 (3), net form: continuity at `x` is equivalent to preservation of convergence
along every net converging to `x`. -/
-- Proof sketch: the forward implication composes a convergent net with `ContinuousAt.tendsto`.
-- For the reverse implication, use the universal neighborhood-point net, whose indices are pairs
-- `(y, U)` with `U ∈ 𝓝 x` and `y ∈ U`; convergence of its image shows that some neighborhood of
-- `x` is mapped into each neighborhood of `f x`.
theorem continuousAt_iff_net_tendsto
    {X : Type u} [TopologicalSpace X] {f : X → EReal} {x : X} :
    ContinuousAt f x ↔
      ∀ {A : Type (max u v)} [Preorder A] [IsDirectedOrder A] (ξ : A → X),
        Tendsto ξ atTop (nhds x) → Tendsto (f ∘ ξ) atTop (nhds (f x)) := by
  constructor
  · intro h A _ _ ξ hξ
    simpa [Function.comp] using h.tendsto.comp hξ
  · intro h
    let ξ : ULift.{v} (NhdsPoint x) → X := fun p ↦ p.down.value
    have hξ : Tendsto ξ atTop (nhds x) := tendsto_liftedNhdsPoint
    have hImage : Tendsto (f ∘ ξ) atTop (nhds (f x)) := h ξ hξ
    exact continuousAt_of_tendsto_liftedNhdsPoint <| by
      simpa [ξ, Function.comp] using hImage

/-! Source item: Chap01/Text_1_0_56_1_36 -/

namespace ERealFunction

variable {X : Type u} [TopologicalSpace X]

/-- Text 1.0.56 (1.36): the limit inferior of an extended-real-valued function `f` at `x` is the
filter `liminf` of `f` along the neighborhood filter `nhds x`. -/
noncomputable abbrev liminfAt (f : X → EReal) (x : X) : EReal :=
  liminf f (nhds x)

/-- The textbook neighborhood formula for the pointwise limit inferior. -/
-- Proof sketch: unfold `liminfAt` and specialize the standard filter formula for `Filter.liminf`
-- to the neighborhood filter `nhds x`.
theorem liminfAt_eq_sSup_nhds_sInf (f : X → EReal) (x : X) :
    liminfAt f x = sSup ((fun V : Set X ↦ sInf (f '' V)) '' {V : Set X | V ∈ nhds x}) := by
  simpa [liminfAt] using (liminf_eq_sSup_sInf (nhds x) f)

end ERealFunction

/-! Source item: Chap01/Text_1_0_57 -/


/-- Text 1.0.57: for a topological space `X` and a subset `C ⊆ X`, the extended-real indicator
`ν_C`, equal to `0` on `C` and `+∞` on `Cᶜ`, is lower semicontinuous if and only if `C` is
closed. -/
theorem lowerSemicontinuous_indicator_compl_top_iff_isClosed
    {X : Type u} [TopologicalSpace X] (C : Set X) :
    LowerSemicontinuous (indicatorFunction C) ↔ IsClosed C := by
  constructor
  · intro hν
    have hopen :
        IsOpen (indicatorFunction C ⁻¹' Ioi (0 : EReal)) :=
      hν.isOpen_preimage (0 : EReal)
    have hpreimage :
        (indicatorFunction C ⁻¹' Ioi (0 : EReal)) = Cᶜ := by
      ext x
      by_cases hx : x ∈ C
      · simp [indicatorFunction, hx]
      · simp [indicatorFunction, hx, EReal.zero_lt_top]
    simpa [hpreimage] using hopen.isClosed_compl
  · intro hC
    convert hC.isOpen_compl.lowerSemicontinuous_indicator (show (0 : EReal) ≤ ⊤ by simp) using 1
    funext x
    exact (indicatorFunction_eq_setIndicator_compl_top C x).symm

/-! Source item: Chap01/Definition_1_31 -/


namespace ERealFunction

variable {X : Type u} [TopologicalSpace X]

/-- The lower semicontinuous minorants of an extended-real-valued function. -/
def lowerSemicontinuousMinorants (f : X → EReal) : Set (X → EReal) :=
  {g | LowerSemicontinuous g ∧ g ≤ f}

/-- A function is a lower semicontinuous minorant of `f` exactly when it is lower semicontinuous
and lies below `f` pointwise. -/
theorem mem_lowerSemicontinuousMinorants_iff (f g : X → EReal) :
    g ∈ lowerSemicontinuousMinorants f ↔ LowerSemicontinuous g ∧ g ≤ f :=
  Iff.rfl

/-- Definition 1.31: the lower semicontinuous envelope of `f` is the supremum, in the function
lattice, of all lower semicontinuous extended-real-valued minorants of `f`. -/
noncomputable def lowerSemicontinuousEnvelope (f : X → EReal) : X → EReal :=
  sSup (lowerSemicontinuousMinorants f)

/-- The lower semicontinuous envelope is computed pointwise as the supremum of the values of all
lower semicontinuous minorants of `f` at that point. -/
theorem lowerSemicontinuousEnvelope_apply (f : X → EReal) (x : X) :
    lowerSemicontinuousEnvelope f x =
      sSup ((fun g : X → EReal ↦ g x) '' lowerSemicontinuousMinorants f) := by
  change sSup (lowerSemicontinuousMinorants f) x =
    sSup ((fun g : X → EReal ↦ g x) '' lowerSemicontinuousMinorants f)
  exact sSup_apply_eq_sSup_image

end ERealFunction

/-! Source item: Chap01/Lemma_1_26 -/

variable {X : Type u} [TopologicalSpace X]

private theorem lowerSemicontinuous_iInf_fintype {I : Type v} [Fintype I]
    {f : I → X → EReal} (hf : ∀ i, LowerSemicontinuous (f i)) :
    LowerSemicontinuous fun x ↦ ⨅ i, f i x := by
  classical
  have h_induction : ∀ (J : Type v) [Fintype J], ∀ (g : J → X → EReal),
      (∀ j, LowerSemicontinuous (g j)) →
        LowerSemicontinuous (fun x ↦ ⨅ j, g j x) := by
    intro J _
    refine Fintype.induction_empty_option
      (P := fun J _ ↦ ∀ (g : J → X → EReal), (∀ j, LowerSemicontinuous (g j)) →
        LowerSemicontinuous (fun x ↦ ⨅ j, g j x)) ?_ ?_ ?_ J
    · intro A B _ e hB g hg
      let gA : A → X → EReal := fun a x ↦ g (e a) x
      have hgA : ∀ a, LowerSemicontinuous (gA a) := by
        intro a
        simpa [gA] using hg (e a)
      have hA : LowerSemicontinuous (fun x ↦ ⨅ a, gA a x) := hB gA hgA
      have hiInf_eq : (fun x ↦ ⨅ a, gA a x) = fun x ↦ ⨅ b, g b x := by
        funext x
        exact Equiv.iInf_congr e (fun a ↦ rfl)
      simpa [hiInf_eq] using hA
    · intro g hg
      have hempty : (fun x ↦ ⨅ j : PEmpty, g j x) = fun _ : X ↦ (⊤ : EReal) := by
        funext x
        simp
      simpa [hempty] using
        (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : X ↦ (⊤ : EReal)))
    · intro A _ hA g hg
      have hnone : LowerSemicontinuous (g none) := hg none
      have hsome : LowerSemicontinuous (fun x ↦ ⨅ a, g (some a) x) := by
        exact hA (fun a x ↦ g (some a) x) (fun a ↦ hg (some a))
      simpa [iInf_option] using hnone.inf hsome
  exact h_induction I f hf

/-- Lemma 1.26 (2): for a finite family of lower semicontinuous extended-real-valued functions,
the pointwise minimum, written as a finite infimum, is lower semicontinuous. -/
theorem lowerSemicontinuous_iInf_of_finite {I : Type v} [Finite I] {f : I → X → EReal}
    (hf : ∀ i, LowerSemicontinuous (f i)) : LowerSemicontinuous fun x ↦ ⨅ i, f i x := by
  classical
  let _ : Fintype I := Fintype.ofFinite I
  simpa using lowerSemicontinuous_iInf_fintype hf

/-! Source item: Chap01/Lemma_1_27 -/


variable {X : Type u} [TopologicalSpace X]

private lemma lowerSemicontinuous_const_mul_of_pos {a : ℝ} (ha : 0 < a) {g : X → EReal}
    (hg : LowerSemicontinuous g) :
    LowerSemicontinuous (fun x ↦ (a : EReal) * g x) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro x
  have ha_nonneg : (0 : EReal) ≤ (a : EReal) := by
    exact_mod_cast (le_of_lt ha : 0 ≤ a)
  calc
    (a : EReal) * g x ≤ (a : EReal) * Filter.liminf g (nhds x) :=
      (monotone_mul_left_of_nonneg ha_nonneg) (hg.le_liminf x)
    _ = Filter.liminf (fun y ↦ (a : EReal) * g y) (nhds x) := by
      symm
      exact EReal.liminf_const_mul_of_nonneg_of_ne_top ha_nonneg (EReal.coe_ne_top a)

private lemma lowerSemicontinuous_add_ereal {g h : X → EReal} (hg : LowerSemicontinuous g)
    (hh : LowerSemicontinuous h) :
    LowerSemicontinuous (fun x ↦ g x + h x) := by
  rw [lowerSemicontinuous_iff_le_liminf]
  intro x
  calc
    g x + h x ≤ Filter.liminf g (nhds x) + Filter.liminf h (nhds x) :=
      add_le_add (hg.le_liminf x) (hh.le_liminf x)
    _ ≤ Filter.liminf (fun y ↦ g y + h y) (nhds x) := by
      simpa using (EReal.le_liminf_add : Filter.liminf g (nhds x) + Filter.liminf h (nhds x) ≤
        Filter.liminf (g + h) (nhds x))

private lemma lowerSemicontinuous_finset_sum_ereal {ι : Type v} {s : Finset ι}
    {f : ι → X → EReal} (hf : ∀ i ∈ s, LowerSemicontinuous (f i)) :
    LowerSemicontinuous (fun x ↦ s.sum fun i ↦ f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using (lowerSemicontinuous_const : LowerSemicontinuous (fun _ : X ↦ (0 : EReal)))
  | @insert i s hi ih =>
      have hi_term : LowerSemicontinuous (f i) := hf i (Finset.mem_insert_self i s)
      have hs_sum : LowerSemicontinuous (fun x ↦ s.sum fun j ↦ f j x) :=
        ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))
      simpa [Finset.sum_insert, hi] using lowerSemicontinuous_add_ereal hi_term hs_sum

/-- Lemma 1.27: a finite positive weighted sum of lower semicontinuous extended-real-valued
functions is lower semicontinuous.

This formulation is valid on any topological space, hence in particular on a Hausdorff space. -/
theorem lowerSemicontinuous_weighted_sum
    {ι : Type v} [Finite ι] {f : ι → X → EReal} {α : ι → ℝ}
    (hα : ∀ i, 0 < α i) (hf : ∀ i, LowerSemicontinuous (f i)) :
    let _ : Fintype ι := Fintype.ofFinite ι
    LowerSemicontinuous (fun x ↦ ∑ i, ((α i : EReal) * f i x)) := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  have hweighted :
      ∀ i ∈ (Finset.univ : Finset ι), LowerSemicontinuous (fun x ↦ (α i : EReal) * f i x) :=
    fun i _ ↦ lowerSemicontinuous_const_mul_of_pos (hα i) (hf i)
  simpa using lowerSemicontinuous_finset_sum_ereal hweighted

/-! Source item: Chap01/Lemma_1_28 -/

namespace ERealFunction

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

/-- Lemma 1.28: composing a lower semicontinuous extended-real-valued function with a continuous
map preserves lower semicontinuity. -/
theorem lowerSemicontinuous_comp {f : Y → EReal} {g : X → Y}
    (hf : LowerSemicontinuous f) (hg : Continuous g) :
    LowerSemicontinuous (f ∘ g) :=
  hf.comp hg

end ERealFunction

/-! Source item: Chap01/Theorem_1_29 -/

namespace ERealFunction

/-- Theorem 1.29: a lower semicontinuous extended-real-valued function on a Hausdorff space
attains a minimum on a compact set as soon as that compact set meets the domain of the function.
-/
-- Proof sketch: apply the canonical compact-attainment theorem
-- `LowerSemicontinuousOn.exists_isMinOn` to the restriction of `f` to `C`; the hypothesis
-- `(C ∩ {x | f x < ⊤}).Nonempty` supplies a point of `C`, so the compact set is nonempty.
theorem lowerSemicontinuous_exists_isMinOn_of_isCompact {X : Type u}
    [TopologicalSpace X] [T2Space X] {f : X → EReal} {C : Set X}
    (hf : LowerSemicontinuous f) (hC : IsCompact C)
    (hdom : (C ∩ { x | f x < ⊤ }).Nonempty) :
    ∃ x ∈ C, IsMinOn f C x := by
  obtain ⟨x, hxC, _⟩ := hdom
  exact (hf.lowerSemicontinuousOn C).exists_isMinOn ⟨x, hxC⟩ hC

/-- Theorem 1.29, infimum form: a minimizing point on the compact set realizes the infimum of the
image. -/
-- Proof sketch: obtain a minimizer from
-- `lowerSemicontinuous_exists_isMinOn_of_isCompact`, then identify its value with `sInf (f '' C)`
-- using the GLB characterization of `IsMinOn`.
theorem lowerSemicontinuous_exists_eq_sInf_image_of_isCompact {X : Type u}
    [TopologicalSpace X] [T2Space X] {f : X → EReal} {C : Set X}
    (hf : LowerSemicontinuous f) (hC : IsCompact C)
    (hdom : (C ∩ { x | f x < ⊤ }).Nonempty) :
    ∃ x ∈ C, f x = sInf (f '' C) := by
  obtain ⟨x, hxC, hmin⟩ := lowerSemicontinuous_exists_isMinOn_of_isCompact hf hC hdom
  exact ⟨x, hxC, eq_sInf_image_of_isMinOn hxC hmin⟩

end ERealFunction

/-! Source item: Chap01/Lemma_1_30 -/

private noncomputable abbrev compactRightInfimum {X : Type u} {Y : Type v}
    (φ : X × Y → EReal) : X → EReal :=
  fun x ↦ sInf (Set.range fun y : Y ↦ φ (x, y))

private theorem compactRightInfimum_eq_of_isMinOn {X : Type u} {Y : Type v}
    {φ : X × Y → EReal} {x : X} {y : Y}
    (hy : IsMinOn (fun y' : Y ↦ φ (x, y')) Set.univ y) :
    compactRightInfimum φ x = φ (x, y) := by
  rw [isMinOn_iff] at hy
  have hglb : IsGLB (Set.range fun y' : Y ↦ φ (x, y')) (φ (x, y)) := by
    refine ⟨?_, ?_⟩
    · intro z hz
      rcases hz with ⟨z, rfl⟩
      exact hy z (by simp)
    · intro b hb
      exact hb ⟨y, rfl⟩
  simpa [compactRightInfimum] using (hglb.unique (isGLB_sInf _)).symm

private lemma fiber_exists_isMinOn {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    [Nonempty Y] {φ : X × Y → EReal} (hφ : LowerSemicontinuous φ) :
    ∀ x : X, ∃ y : Y, IsMinOn (fun y' : Y ↦ φ (x, y')) Set.univ y := by
  intro x
  have hfiber : LowerSemicontinuous (fun y : Y ↦ φ (x, y)) := by
    simpa using hφ.comp (by
      continuity : Continuous fun y : Y ↦ (x, y))
  obtain ⟨y, -, hy⟩ :=
    (hfiber.lowerSemicontinuousOn Set.univ).exists_isMinOn Set.univ_nonempty isCompact_univ
  exact ⟨y, hy⟩

private lemma compactRightInfimum_epigraph_eq_image_fst {X : Type u} {Y : Type v}
    {φ : X × Y → EReal}
    (hmin : ∀ x : X, ∃ y : Y, IsMinOn (fun y' : Y ↦ φ (x, y')) Set.univ y) :
    {p : X × EReal | compactRightInfimum φ p.1 ≤ p.2} =
      Prod.fst '' {q : (X × EReal) × Y | φ (q.1.1, q.2) ≤ q.1.2} := by
  ext p
  constructor
  · intro hp
    obtain ⟨y, hy⟩ := hmin p.1
    refine ⟨(p, y), ?_, rfl⟩
    simpa [compactRightInfimum_eq_of_isMinOn hy] using hp
  · rintro ⟨q, hq, rfl⟩
    rcases q with ⟨⟨x, t⟩, y⟩
    have hy : φ (x, y) ∈ Set.range fun y' : Y ↦ φ (x, y') := ⟨y, rfl⟩
    exact le_trans (sInf_le hy) hq

private lemma isClosed_epigraph_compactRightInfimum {X : Type u} {Y : Type v}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    [Nonempty Y] {φ : X × Y → EReal} (hφ : LowerSemicontinuous φ) :
    IsClosed {p : X × EReal | compactRightInfimum φ p.1 ≤ p.2} := by
  let e : ((X × EReal) × Y) → (X × Y) × EReal := fun q ↦ ((q.1.1, q.2), q.1.2)
  have he : Continuous e := by
    fun_prop
  have hclosedFiberEpigraph : IsClosed {q : (X × EReal) × Y | φ (q.1.1, q.2) ≤ q.1.2} := by
    simpa [e] using
      (LowerSemicontinuous.isClosed_epigraph hφ).preimage he
  have hmin : ∀ x : X, ∃ y : Y, IsMinOn (fun y' : Y ↦ φ (x, y')) Set.univ y :=
    fiber_exists_isMinOn hφ
  rw [compactRightInfimum_epigraph_eq_image_fst hmin]
  exact isClosedMap_fst_of_compactSpace _ hclosedFiberEpigraph

/-- Lemma 1.30: over a nonempty compact second factor, the infimum of a lower semicontinuous
extended-real-valued function over the second variable is lower semicontinuous, and each fiber
section attains its minimum. -/
theorem lowerSemicontinuous_compactRightInfimum_and_exists_isMinOn
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace Y]
    [Nonempty Y] {φ : X × Y → EReal}
    (hφ : LowerSemicontinuous φ) :
    LowerSemicontinuous (fun x ↦ sInf (Set.range fun y : Y ↦ φ (x, y))) ∧
      ∀ x : X, ∃ y : Y, IsMinOn (fun y' : Y ↦ φ (x, y')) Set.univ y := by
  have hmin : ∀ x : X, ∃ y : Y, IsMinOn (fun y' : Y ↦ φ (x, y')) Set.univ y :=
    fiber_exists_isMinOn hφ
  refine ⟨?_, hmin⟩
  change LowerSemicontinuous (compactRightInfimum φ)
  rw [_root_.lowerSemicontinuous_iff_isClosed_epigraph]
  exact isClosed_epigraph_compactRightInfimum hφ

/-! Source item: Chap01/Lemma_1_32 -/

namespace ERealFunction

variable {X : Type u}

/-- Helper for Lemma 1.32: the textbook real-height epigraph is the pullback of the canonical
`EReal` epigraph along the coercion of the second coordinate. -/
private lemma epigraph_eq_preimage_ereal_epigraph (f : X → EReal) :
    epigraph f =
      (fun p : X × ℝ ↦ (p.1, (p.2 : EReal))) ⁻¹' {q : X × EReal | f q.1 ≤ q.2} := by
  rfl

variable [TopologicalSpace X]

/-- Helper for Lemma 1.32: monotonicity of the pointwise liminf under pointwise order. -/
private lemma liminfAt_mono {f g : X → EReal} (hfg : f ≤ g) (x : X) :
    liminfAt f x ≤ liminfAt g x := by
  -- The filter liminf is monotone under eventual pointwise order.
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hfg)

/-- Helper for Lemma 1.32: the constant-on-open-set function with value `ξ` and value `⊥`
outside is lower semicontinuous. -/
private lemma lowerSemicontinuous_piecewise_bot
    {U : Set X} [DecidablePred (· ∈ U)] (hU : IsOpen U)
    (ξ : EReal) :
    LowerSemicontinuous (fun x : X ↦ if x ∈ U then ξ else ⊥) := by
  -- At points of `U`, openness keeps the value equal to `ξ`; outside `U`, the claim is vacuous.
  rw [lowerSemicontinuous_iff]
  intro x
  rw [lowerSemicontinuousAt_iff]
  by_cases hx : x ∈ U
  · intro y hy
    have hyξ : y < ξ := by
      simpa [hx] using hy
    filter_upwards [hU.mem_nhds hx] with z hz
    simpa [hz] using hyξ
  · intro y hy
    simp [hx] at hy

-- Proof sketch: rewrite the lower semicontinuous envelope as the pointwise `iSup` of the subtype
-- of lower semicontinuous minorants; `lowerSemicontinuous_iSup` gives lower semicontinuity, and
-- the subtype indexing enforces the minorant and maximality properties.
/-- Lemma 1.32: the lower semicontinuous envelope is the greatest lower semicontinuous minorant of
`f`. -/
theorem lowerSemicontinuousHull_isGreatest (f : X → EReal) :
    IsGreatest {g : X → EReal | LowerSemicontinuous g ∧ g ≤ f}
      (lowerSemicontinuousEnvelope f) := by
  have hEnvelope_eq_iSup :
      lowerSemicontinuousEnvelope f =
        fun x ↦ ⨆ g : {g : X → EReal // g ∈ lowerSemicontinuousMinorants f}, g.1 x := by
    funext x
    rw [lowerSemicontinuousEnvelope_apply]
    apply le_antisymm
    · refine sSup_le fun y hy ↦ ?_
      rcases hy with ⟨g, hg, rfl⟩
      exact le_iSup_of_le ⟨g, hg⟩ le_rfl
    · refine iSup_le fun g ↦ ?_
      exact le_sSup ⟨g.1, g.2, rfl⟩
  -- The hull belongs to the class of lower semicontinuous minorants.
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · -- Lower semicontinuity follows from lower semicontinuity of each indexed minorant.
      simpa [hEnvelope_eq_iSup, lowerSemicontinuousMinorants] using
        (lowerSemicontinuous_iSup
          fun g : {g : X → EReal // g ∈ lowerSemicontinuousMinorants f} ↦ g.2.1)
    · -- Every indexed function is a minorant of `f`, so their supremum is as well.
      intro x
      rw [hEnvelope_eq_iSup]
      exact iSup_le fun g ↦ g.2.2 x
  · intro g hg x
    -- Any lower semicontinuous minorant appears in the indexing subtype.
    rw [hEnvelope_eq_iSup]
    exact le_iSup_of_le ⟨g, hg⟩ le_rfl

-- Proof sketch: the main envelope theorem gives that `lowerSemicontinuousEnvelope f` is lower
-- semicontinuous; then apply the epigraph characterization of lower semicontinuity.
/-- The epigraph of the lower semicontinuous envelope is closed. -/
theorem isClosed_epi_lowerSemicontinuousHull (f : X → EReal) :
    IsClosed (epigraph (lowerSemicontinuousEnvelope f)) := by
  rw [epigraph_eq_preimage_ereal_epigraph]
  exact (LowerSemicontinuous.isClosed_epigraph
      (lowerSemicontinuousHull_isGreatest f).1.1).preimage
    (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))

-- Proof sketch: any point with `f x < +∞` also satisfies `lowerSemicontinuousEnvelope f x < +∞`
-- because the envelope is majorized by `f`.
/-- The domain of `f` is contained in the domain of its lower semicontinuous hull. -/
theorem dom_subset_dom_lowerSemicontinuousHull (f : X → EReal) :
    dom f ⊆ dom (lowerSemicontinuousEnvelope f) := by
  intro x hx
  -- The hull is pointwise majorized by `f`, so finiteness of `f x` propagates to the hull.
  exact lt_of_le_of_lt ((lowerSemicontinuousHull_isGreatest f).1.2 x) hx

/-- Helper for Lemma 1.32: restricting a lower semicontinuous function to a closed set and
sending the complement to `+∞` preserves lower semicontinuity. -/
private lemma lowerSemicontinuous_piecewise_top_of_isClosed
    {s : Set X} [DecidablePred (· ∈ s)] {g : X → EReal} (hs : IsClosed s)
    (hg : LowerSemicontinuous g) :
    LowerSemicontinuous (fun x : X ↦ if x ∈ s then g x else ⊤) := by
  -- At points of `s`, lower semicontinuity comes from `g`; away from `s`, the open complement
  -- forces the value to stay equal to `⊤` on a neighborhood.
  rw [lowerSemicontinuous_iff]
  intro x
  rw [lowerSemicontinuousAt_iff]
  by_cases hx : x ∈ s
  · have hgx : LowerSemicontinuousAt g x := (lowerSemicontinuous_iff.mp hg) x
    rw [lowerSemicontinuousAt_iff] at hgx
    intro y hy
    have hyg : y < g x := by
      simpa [hx] using hy
    have hy_top : y < (⊤ : EReal) := hyg.trans_le le_top
    have h_event : ∀ᶠ z in nhds x, y < g z := hgx y hyg
    refine h_event.mp ?_
    filter_upwards with z hz_g
    by_cases hz_mem : z ∈ s
    · simpa [hz_mem] using hz_g
    · simpa [hz_mem] using hy_top
  · intro y hy
    have hy_top : y < (⊤ : EReal) := by
      simpa [hx] using hy
    refine Filter.mem_of_superset (hs.isOpen_compl.mem_nhds hx) ?_
    intro z hz
    have hz' : z ∉ s := by
      simpa using hz
    simpa [hz'] using hy_top

/-- Helper for Lemma 1.32: away from the closure of the domain, the lower semicontinuous hull takes
the value `+∞`. -/
private lemma lowerSemicontinuousHull_eq_top_of_notMem_closure_dom (f : X → EReal)
    {x : X} (hx : x ∉ closure (dom f)) :
    lowerSemicontinuousEnvelope f x = ⊤ := by
  classical
  let g : X → EReal :=
    fun y ↦ if y ∈ closure (dom f) then lowerSemicontinuousEnvelope f y else ⊤
  have hg_lsc : LowerSemicontinuous g := by
    -- The closed-set truncation of the hull is still lower semicontinuous.
    simpa [g] using
      (lowerSemicontinuous_piecewise_top_of_isClosed isClosed_closure
        (lowerSemicontinuousHull_isGreatest f).1.1)
  have hg_le_f : g ≤ f := by
    -- On the closure we use the hull minorization; outside it, `f` must already equal `⊤`.
    intro y
    by_cases hy : y ∈ closure (dom f)
    · simpa [g, hy] using (lowerSemicontinuousHull_isGreatest f).1.2 y
    · have hy_not_dom : y ∉ dom f := fun hy_dom ↦ hy (subset_closure hy_dom)
      have htop_le : (⊤ : EReal) ≤ f y := le_of_not_gt hy_not_dom
      simpa [g, hy] using htop_le
  have hg_le_hull : g ≤ lowerSemicontinuousEnvelope f :=
    (lowerSemicontinuousHull_isGreatest f).2 ⟨hg_lsc, hg_le_f⟩
  -- Evaluating the comparison at a point outside the closure forces the hull to be `⊤` there.
  have htop_le : (⊤ : EReal) ≤ lowerSemicontinuousEnvelope f x := by
    simpa [g, hx] using hg_le_hull x
  exact le_antisymm le_top htop_le

-- Proof sketch: truncate the hull outside `closure (dom f)` by setting it equal to
-- `+∞`; the resulting function is still lower semicontinuous and majorized by `f`, so maximality
-- of the hull forces the hull to be `+∞` away from `closure (dom f)`.
/-- The domain of the lower semicontinuous hull is contained in the closure of the domain of `f`. -/
theorem dom_lowerSemicontinuousHull_subset_closure_dom (f : X → EReal) :
    dom (lowerSemicontinuousEnvelope f) ⊆ closure (dom f) := by
  intro x hx
  -- Route correction: the domain inclusion is proved by the closed-set truncation/maximality
  -- argument, not by forward-referencing the later liminf formula.
  by_contra hx_closure
  have htop : lowerSemicontinuousEnvelope f x = ⊤ :=
    lowerSemicontinuousHull_eq_top_of_notMem_closure_dom f hx_closure
  have hx_not_dom : ¬ x ∈ dom (lowerSemicontinuousEnvelope f) := by
    simp [mem_dom_iff, htop]
  exact hx_not_dom hx

-- Proof sketch: show first that `x ↦ liminfAt f x` is lower semicontinuous and majorized by `f`,
-- hence bounded above by the hull; then compare any lower semicontinuous minorant of `f` with the
-- neighborhood-infimum formula for `liminfAt`.
/-- The lower semicontinuous hull agrees pointwise with the lower limit inferior of `f`. -/
theorem lowerSemicontinuousHull_eq_liminfAt (f : X → EReal) (x : X) :
    lowerSemicontinuousEnvelope f x = liminfAt f x := by
  classical
  refine le_antisymm ?_ ?_
  · -- Lower semicontinuity of the hull gives the upper bound by the liminf.
    exact ((lowerSemicontinuousHull_isGreatest f).1.1.le_liminf x).trans
      (liminfAt_mono (lowerSemicontinuousHull_isGreatest f).1.2 x)
  · -- Any real level strictly below the liminf can be realized by an open lower semicontinuous
    -- minorant, forcing the hull to stay above it.
    refine (EReal.ge_of_forall_gt_iff_ge).1 ?_
    intro z hz
    have hz_event :
        {y : X | (z : EReal) < f y} ∈ nhds x := by
      simpa [liminfAt] using
        (Filter.eventually_lt_of_lt_liminf hz : ∀ᶠ y in nhds x, (z : EReal) < f y)
    rcases mem_nhds_iff.mp hz_event with ⟨U, hUsub, hUopen, hxU⟩
    let g : X → EReal := fun y ↦ if y ∈ U then (z : EReal) else ⊥
    have hg_lsc : LowerSemicontinuous g := by
      -- The open set `U` supports a constant value, while outside `U` the value is `⊥`.
      simpa [g] using (lowerSemicontinuous_piecewise_bot hUopen (z : EReal))
    have hg_le_f : g ≤ f := by
      -- On `U` we use the neighborhood lower bound, and outside `U` we use `⊥ ≤ f`.
      intro y
      by_cases hy : y ∈ U
      · simpa [g, hy] using (hUsub hy).le
      · simp [g, hy]
    have hg_le_hull : g ≤ lowerSemicontinuousEnvelope f :=
      (lowerSemicontinuousHull_isGreatest f).2 ⟨hg_lsc, hg_le_f⟩
    -- Evaluating the auxiliary minorant at `x` gives the desired lower bound.
    simpa [g, hxU] using hg_le_hull x

-- Proof sketch: use the pointwise formula for the hull as a limit inferior, together with the
-- neighborhood characterization of lower semicontinuity at a point.
/-- A function is lower semicontinuous at `x` exactly when its lower semicontinuous hull agrees
with it at `x`. -/
theorem lowerSemicontinuousAt_iff_lowerSemicontinuousHull_eq (f : X → EReal) (x : X) :
    LowerSemicontinuousAt f x ↔ lowerSemicontinuousEnvelope f x = f x := by
  constructor
  · intro hfx
    -- The hull is always below `f`, while lower semicontinuity gives the reverse inequality.
    apply le_antisymm
    · exact (lowerSemicontinuousHull_isGreatest f).1.2 x
    · calc
        f x ≤ liminfAt f x := by
          simpa [liminfAt] using
            (LowerSemicontinuousAt.le_liminf hfx : f x ≤ Filter.liminf f (nhds x))
        _ = lowerSemicontinuousEnvelope f x := by
          symm
          exact lowerSemicontinuousHull_eq_liminfAt f x
  · intro hEq
    -- Rewriting the hull as the liminf turns the assumed equality into the standard criterion.
    rw [lowerSemicontinuousAt_iff_le_liminf]
    calc
      f x = lowerSemicontinuousEnvelope f x := hEq.symm
      _ = liminfAt f x := lowerSemicontinuousHull_eq_liminfAt f x
      _ ≤ Filter.liminf f (nhds x) := by
        rfl

/-- Helper for Lemma 1.32: each real-height epigraph point of the lower semicontinuous hull lies
in the closure of the real-height epigraph of the original function. -/
private lemma mem_closure_epigraph_of_mem_epigraph_lowerSemicontinuousHull
    (f : X → EReal) {x : X} {ξ : ℝ}
    (hξ : lowerSemicontinuousEnvelope f x ≤ (ξ : EReal)) :
    (x, ξ) ∈ closure (epigraph f) := by
  -- Test an arbitrary neighborhood of `(x, ξ)` and find an epigraph point of `f` inside it by
  -- combining a product neighborhood with a strict `liminf` witness below a nearby real height.
  rw [mem_closure_iff_nhds]
  intro t ht
  rcases mem_nhds_prod_iff.mp ht with ⟨V, hV, W, hW, hVW⟩
  obtain ⟨v, hξv, hvW⟩ := exists_Ico_subset_of_mem_nhds hW ⟨ξ + 1, by linarith⟩
  let u : ℝ := (ξ + v) / 2
  have hξu : ξ < u := by
    dsimp [u]
    linarith
  have huv : u < v := by
    dsimp [u]
    linarith
  have huW : u ∈ W := by
    apply hvW
    exact ⟨le_of_lt hξu, huv⟩
  have hHull_lt : lowerSemicontinuousEnvelope f x < (u : EReal) := by
    exact lt_of_le_of_lt hξ (by exact_mod_cast hξu)
  have hliminf_lt : liminfAt f x < (u : EReal) := by
    simpa [lowerSemicontinuousHull_eq_liminfAt f x] using hHull_lt
  have hbounded : (nhds x).IsCoboundedUnder (· ≥ ·) f := by
    isBoundedDefault
  have hfreq : ∃ᶠ y in nhds x, f y < (u : EReal) := by
    exact (Filter.frequently_lt_of_liminf_lt hbounded hliminf_lt :
      ∃ᶠ y in nhds x, f y < (u : EReal))
  have hfreqV : ∃ᶠ y in nhds x, f y < (u : EReal) ∧ y ∈ V := by
    exact hfreq.and_eventually hV
  obtain ⟨y, hy_lt, hyV⟩ := hfreqV.exists
  refine ⟨(y, u), ?_⟩
  constructor
  · exact hVW ⟨hyV, huW⟩
  · -- The chosen point lies below the nearby height `u`, hence it belongs to `epigraph f`.
    simpa [epigraph] using le_of_lt hy_lt

-- Proof sketch: one inclusion follows because `epi f ⊆ epi (lowerSemicontinuousHull f)` and the
-- hull epigraph is closed; for the reverse inclusion, use the pointwise `liminf` formula to hit
-- every neighborhood of a point of `epi (lowerSemicontinuousHull f)` with a point of `epi f`.
/-- The epigraph of the lower semicontinuous hull is the closure of the epigraph of `f`. -/
theorem epi_lowerSemicontinuousHull_eq_closure_epi (f : X → EReal) :
    epigraph (lowerSemicontinuousEnvelope f) = closure (epigraph f) := by
  ext p
  constructor
  · rcases p with ⟨x, ξ⟩
    intro hp
    -- The hard inclusion is exactly the closure helper for points of the hull epigraph.
    exact mem_closure_epigraph_of_mem_epigraph_lowerSemicontinuousHull f hp
  · intro hp
    -- The easy inclusion comes from `epigraph f ⊆ epigraph (lowerSemicontinuousHull f)` and
    -- closedness.
    exact closure_minimal
      (fun (q : X × ℝ) hq ↦ le_trans ((lowerSemicontinuousHull_isGreatest f).1.2 q.1) hq)
      (isClosed_epi_lowerSemicontinuousHull f) hp

end ERealFunction
