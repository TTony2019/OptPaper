import Mathlib

/-!
# Order EReal

Order-theoretic and extended-real lemmas for intervals, liminf/limsup, and scalar signs.
-/

open _root_.EReal
open Set
open Filter

/-! Source item: Chap01/Fact_1_1 -/
universe u

/-- Fact 1.1 (Zorn's lemma): if every chain in a preorder has an upper bound, then there exists
a maximal element. -/
theorem fact_1_1 {α : Type u} [Preorder α]
    (h : ∀ c : Set α, IsChain (fun a b : α ↦ a ≤ b) c → BddAbove c) :
    ∃ m : α, IsMax m :=
  zorn_le h

/-! Source item: Chap01/Remark_1_3 -/

/-- Remark 1.3 (1): the textbook ray `[0,+∞[` is the closed ray `Set.Ici 0`. -/
theorem positiveReals_eq_Ici : {ξ : ℝ | 0 ≤ ξ} = Ici 0 :=
  rfl

/-- Remark 1.3 (2): the textbook ray `]0,+∞[` is the open ray `Set.Ioi 0`. -/
theorem strictlyPositiveReals_eq_Ioi : {ξ : ℝ | 0 < ξ} = Ioi 0 :=
  rfl

/-- Remark 1.3 (3): the textbook ray `]-∞,0]` is the closed ray `Set.Iic 0`. -/
theorem negativeReals_eq_Iic : {ξ : ℝ | ξ ≤ 0} = Iic 0 :=
  rfl

/-- Remark 1.3 (4): the textbook ray `]-∞,0[` is the open ray `Set.Iio 0`. -/
theorem strictlyNegativeReals_eq_Iio : {ξ : ℝ | ξ < 0} = Iio 0 :=
  rfl

/-- Remark 1.3 (5): the textbook orthant `[0,+∞[^N` is the positive cone `Set.Ici 0`
for the pointwise order on `Fin N → ℝ`. -/
theorem positiveOrthant_eq_Ici {N : ℕ} : {x : Fin N → ℝ | ∀ i, 0 ≤ x i} = Ici 0 :=
  rfl

/-- Remark 1.3 (6): the textbook orthant `]0,+∞[^N` is the product of the open rays
`Set.Ioi 0`. -/
theorem strictlyPositiveOrthant_eq_pi_Ioi {N : ℕ} :
    {x : Fin N → ℝ | ∀ i, 0 < x i} = pi (univ : Set (Fin N)) (fun _ ↦ Ioi (0 : ℝ)) := by
  ext x
  simp

/-- Remark 1.3 (7): the textbook orthant `]-∞,0]^N` is the negative cone `Set.Iic 0`
for the pointwise order on `Fin N → ℝ`. -/
theorem negativeOrthant_eq_Iic {N : ℕ} : {x : Fin N → ℝ | ∀ i, x i ≤ 0} = Iic 0 :=
  rfl

/-- Remark 1.3 (8): the textbook orthant `]-∞,0[^N` is the product of the open rays
`Set.Iio 0`. -/
theorem strictlyNegativeOrthant_eq_pi_Iio {N : ℕ} :
    {x : Fin N → ℝ | ∀ i, x i < 0} = pi (univ : Set (Fin N)) (fun _ ↦ Iio (0 : ℝ)) := by
  ext x
  simp

/-- Remark 1.3 (9): for a function `f : D → [-∞,+∞]`, the textbook notion of being increasing on
`D` is the canonical predicate `MonotoneOn f D`. -/
theorem increasingOn_iff_monotoneOn {D : Set ℝ} {f : ℝ → EReal} :
    (∀ ⦃ξ : ℝ⦄, ξ ∈ D → ∀ ⦃η : ℝ⦄, η ∈ D → ξ < η → f ξ ≤ f η) ↔ MonotoneOn f D :=
  monotoneOn_iff_forall_lt.symm

/-- Remark 1.3 (10): for a function `f : D → [-∞,+∞]`, the textbook notion of being strictly
increasing on `D` is the canonical predicate `StrictMonoOn f D`. -/
theorem strictlyIncreasingOn_iff_strictMonoOn {D : Set ℝ} {f : ℝ → EReal} :
    (∀ ⦃ξ : ℝ⦄, ξ ∈ D → ∀ ⦃η : ℝ⦄, η ∈ D → ξ < η → f ξ < f η) ↔ StrictMonoOn f D :=
  Iff.rfl

/-- Remark 1.3 (11): for a function `f : D → [-∞,+∞]`, the textbook notion of being decreasing on
`D` means that `-f` is increasing on `D`; canonically this is `AntitoneOn f D`. -/
theorem decreasingOn_iff_antitoneOn {D : Set ℝ} {f : ℝ → EReal} :
    MonotoneOn (fun ξ ↦ -f ξ) D ↔ AntitoneOn f D := by
  constructor
  · intro h ξ hξ η hη hξη
    exact EReal.neg_le_neg_iff.mp (h hξ hη hξη)
  · intro h ξ hξ η hη hξη
    exact EReal.neg_le_neg_iff.mpr (h hξ hη hξη)

/-- Remark 1.3 (12): for a function `f : D → [-∞,+∞]`, the textbook notion of being strictly
decreasing on `D` means that `-f` is strictly increasing on `D`; canonically this is
`StrictAntiOn f D`. -/
theorem strictlyDecreasingOn_iff_strictAntiOn {D : Set ℝ} {f : ℝ → EReal} :
    StrictMonoOn (fun ξ ↦ -f ξ) D ↔ StrictAntiOn f D := by
  constructor
  · intro h ξ hξ η hη hξη
    exact EReal.neg_lt_neg_iff.mp (h hξ hη hξη)
  · intro h ξ hξ η hη hξη
    exact EReal.neg_lt_neg_iff.mpr (h hξ hη hξη)

/-! Source item: Chap01/Text_1_0_26 -/

namespace EReal

/-- Every real number lies strictly between `-∞` and `+∞` in the extended real line. -/
theorem real_strictly_between_infinities (ξ : ℝ) :
    (⊥ : EReal) < (ξ : EReal) ∧ (ξ : EReal) < ⊤ := by
  exact ⟨bot_lt_coe ξ, coe_lt_top ξ⟩

end EReal

/-! Source item: Chap01/Text_1_0_27 -/

namespace EReal

/-- Text 1.0.27: the extended interval `]ξ, +∞]` is the usual real interval `]ξ, +∞[`,
embedded into `EReal`, with the point `+∞` adjoined. -/
theorem openClosedUpperInfiniteInterval_eq_image_Ioi_union_top (ξ : ℝ) :
    Ioi (ξ : EReal) = Real.toEReal '' Ioi ξ ∪ ({(⊤ : EReal)} : Set EReal) := by
  rw [image_coe_Ioi]
  ext x
  simp [lt_top_iff_ne_top]

end EReal

/-! Source item: Chap01/Text_1_0_28 -/

namespace EReal

/-- The supremum of a set of extended reals is the negative of the infimum of its negated image. -/
theorem sSup_eq_neg_sInf_image_neg (S : Set EReal) :
    sSup S = -sInf ((-·) '' S) := by
  apply neg_injective
  rw [neg_neg]
  change (negOrderIso (sSup S) : ERealᵒᵈ) = sSup (negOrderIso '' S)
  exact (negOrderIso.isLUB_image'.2 (isLUB_sSup S)).unique (isLUB_sSup _)

end EReal

/-! Source item: Chap01/Text_1_0_29 -/

namespace Net

variable {A : Type u} [Preorder A] [IsDirectedOrder A]

/-- The limit inferior of a net is the supremum of the infima of its tails. -/
-- Proof sketch: unfold `Net.liminf`, rewrite `Filter.liminf` with
-- `Filter.liminf_eq_sSup_sInf`, and specialize `Filter.mem_atTop_sets` to identify the sets in
-- `atTop` with the tails `Set.Ici a`.
theorem liminf_eq_sSup_tail_sInf [Nonempty A] (ξ : A → EReal) :
    Filter.liminf ξ atTop = sSup (Set.range fun a : A ↦ sInf (ξ '' Set.Ici a)) := by
  refine le_antisymm ?_ ?_
  · calc
      Filter.liminf ξ atTop
          = sSup ((fun I ↦ sInf (ξ '' I)) '' (atTop : Filter A).sets) := by
              simpa using (Filter.liminf_eq_sSup_sInf (atTop : Filter A) ξ)
      _ ≤ sSup (Set.range fun a : A ↦ sInf (ξ '' Set.Ici a)) := by
            refine sSup_le ?_
            intro r hr
            rcases hr with ⟨I, hI, rfl⟩
            rcases mem_atTop_sets.mp hI with ⟨a, ha⟩
            exact le_trans (sInf_le_sInf (Set.image_mono ha)) (le_sSup ⟨a, rfl⟩)
  · calc
      sSup (Set.range fun a : A ↦ sInf (ξ '' Set.Ici a))
          ≤ sSup ((fun I ↦ sInf (ξ '' I)) '' (atTop : Filter A).sets) := by
            refine sSup_le ?_
            intro r hr
            rcases hr with ⟨a, rfl⟩
            exact le_sSup ⟨Set.Ici a, mem_atTop_sets.mpr ⟨a, fun _ hb ↦ hb⟩, rfl⟩
      _ = Filter.liminf ξ atTop := by
            simpa using (Filter.liminf_eq_sSup_sInf (atTop : Filter A) ξ).symm

/-- The limit superior of a net is the infimum of the suprema of its tails. -/
-- Proof sketch: unfold `Net.limsup`, rewrite `Filter.limsup` with
-- `Filter.limsup_eq_sInf_sSup`, and use `Filter.mem_atTop_sets` to replace sets in `atTop` by the
-- tails `Set.Ici a`.
theorem limsup_eq_sInf_tail_sSup [Nonempty A] (ξ : A → EReal) :
    Filter.limsup ξ atTop = sInf (Set.range fun a : A ↦ sSup (ξ '' Set.Ici a)) := by
  refine le_antisymm ?_ ?_
  · calc
      Filter.limsup ξ atTop
          = sInf ((fun I ↦ sSup (ξ '' I)) '' (atTop : Filter A).sets) := by
              simpa using (Filter.limsup_eq_sInf_sSup (atTop : Filter A) ξ)
      _ ≤ sInf (Set.range fun a : A ↦ sSup (ξ '' Set.Ici a)) := by
            refine le_sInf ?_
            intro r hr
            rcases hr with ⟨a, rfl⟩
            exact sInf_le_of_le
              ⟨Set.Ici a, mem_atTop_sets.mpr ⟨a, fun _ hb ↦ hb⟩, rfl⟩ le_rfl
  · calc
      sInf (Set.range fun a : A ↦ sSup (ξ '' Set.Ici a))
          ≤ sInf ((fun I ↦ sSup (ξ '' I)) '' (atTop : Filter A).sets) := by
            refine le_sInf ?_
            intro r hr
            rcases hr with ⟨I, hI, rfl⟩
            rcases mem_atTop_sets.mp hI with ⟨a, ha⟩
            exact sInf_le_of_le ⟨a, rfl⟩ (sSup_le_sSup (Set.image_mono ha))
      _ = Filter.limsup ξ atTop := by
            simpa using (Filter.limsup_eq_sInf_sSup (atTop : Filter A) ξ).symm

/-- Text 1.0.29: for an extended-real-valued net indexed by a nonempty directed set, the limit
inferior is the supremum of the infima of the tails and the limit superior is the infimum of the
suprema of the tails. -/
-- Proof sketch: combine `Net.liminf_eq_sSup_tail_sInf` and `Net.limsup_eq_sInf_tail_sSup`.
theorem tail_liminf_limsup_formulas [Nonempty A] (ξ : A → EReal) :
    Filter.liminf ξ atTop = sSup (Set.range fun a : A ↦ sInf (ξ '' Set.Ici a)) ∧
      Filter.limsup ξ atTop = sInf (Set.range fun a : A ↦ sSup (ξ '' Set.Ici a)) := by
  exact ⟨liminf_eq_sSup_tail_sInf ξ, limsup_eq_sInf_tail_sSup ξ⟩

end Net

/-! Source item: Chap01/Text_1_0_30 -/

namespace Net

variable {A : Type u} [Nonempty A] [Preorder A] [IsDirectedOrder A]

/-- Text 1.0.30: for an `EReal`-valued net on a nonempty directed index set, the lower limit is
bounded above by the upper limit. -/
theorem liminf_le_limsup (ξ : A → EReal) :
    liminf ξ atTop ≤ limsup ξ atTop := by
  simpa using (Filter.liminf_le_limsup : liminf ξ atTop ≤ limsup ξ atTop)

end Net

/-! Source item: Chap01/Lemma_1_16 -/


namespace Net

variable {A : Type u} [Preorder A]

/-- Lemma 1.16: if two extended-real-valued nets have lower limits strictly above `-∞`, then the
sum of their lower limits is bounded above by the lower limit of their pointwise sum. -/
-- Proof sketch: keep the source's hypotheses `liminf ξ > -∞` and `liminf η > -∞` in the
-- statement, then specialize the stronger canonical `EReal.le_liminf_add` theorem to the net
-- filter `atTop`.
theorem le_liminf_add [IsDirectedOrder A] (ξ η : A → EReal)
    (_hξ : (⊥ : EReal) < liminf ξ atTop) (_hη : (⊥ : EReal) < liminf η atTop) :
    liminf ξ atTop + liminf η atTop ≤ liminf (ξ + η) atTop := by
  simpa using
    (EReal.le_liminf_add :
      liminf ξ atTop + liminf η atTop ≤ liminf (ξ + η) atTop)

end Net

/-! Source item: Chap01/Lemma_1_20 -/
universe v

/-- Lemma 1.20: if `X` and `Y` are Hausdorff spaces, `T : X → Y` is continuous, and `C ⊆ X` is
compact, then `T(C)` is compact. This is the textbook Hausdorff-space specialization of the
canonical theorem `IsCompact.image`. -/
theorem lemma_1_20
    {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
    {C : Set X} {T : X → Y} (hC : IsCompact C) (hT : Continuous T) :
    IsCompact (T '' C) :=
  hC.image hT
