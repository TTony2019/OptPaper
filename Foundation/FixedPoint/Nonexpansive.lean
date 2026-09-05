import Mathlib
import Mathlib.Data.List.TFAE
import Foundation.Hilbert.Basic
import Foundation.Projection.BestApproximation

/-!
# FixedPoint Nonexpansive

Fixed-point sets and nonexpansive, quasinonexpansive, firmly nonexpansive, and cocoercive operators.
-/

open Function Set
open scoped RealInnerProductSpace
open scoped BigOperators InnerProductSpace
open ContinuousLinearMap
open scoped InnerProductSpace
open scoped Matrix
open Set

/-! Source item: Chap04/Definition_4_1 -/
universe u


section

variable {α : Type u}

/-
Thin compatibility abbreviation retained for downstream call sites.
-/
abbrev fixedPointSetOn (D : Set α) (T : α → α) : Set α :=
  D ∩ fixedPoints T

/-- Definition 4.1: the fixed-point set of `T` in `D` is `D ∩ Function.fixedPoints T`. -/
theorem fixedPointSetOn_eq_inter_fixedPoints (D : Set α) (T : α → α) :
    fixedPointSetOn D T = D ∩ fixedPoints T := rfl

/-- Membership in `fixedPointSetOn D T` means lying in `D` and being fixed by `T`. -/
-- Proof sketch: unfold `fixedPointSetOn` and `fixedPoints`, then simplify membership in
-- the intersection.
@[simp]
theorem mem_fixedPointSetOn_iff {D : Set α} {T : α → α} {x : α} :
    x ∈ fixedPointSetOn D T ↔ x ∈ D ∧ T x = x := by
  simp [fixedPointSetOn, Function.mem_fixedPoints, Function.IsFixedPt]

end

section

variable {H : Type u} [NormedAddCommGroup H]

/-- Definition 4.1(i): `T : D → H` is firmly nonexpansive when it satisfies the residual
inequality on the subtype domain `D`. -/
def IsFirmlyNonexpansiveOn {D : Set H} (T : D → H) : Prop :=
  ∀ x y : D,
    ‖T x - T y‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 - ‖((x : H) - T x) - ((y : H) - T y)‖ ^ 2

/-- Definition 4.1(i) restated: `IsFirmlyNonexpansiveOn` unfolds to its defining residual
inequality. -/
theorem isFirmlyNonexpansiveOn_iff {D : Set H} {T : D → H} :
    IsFirmlyNonexpansiveOn T ↔
      ∀ x y : D,
        ‖T x - T y‖ ^ 2 ≤
          ‖(x : H) - y‖ ^ 2 - ‖((x : H) - T x) - ((y : H) - T y)‖ ^ 2 := by
  rfl

/-- Thin compatibility bridge: an ambient self-map is firmly nonexpansive on `D` when its
restriction to `D` is firmly nonexpansive. -/
def AmbientFirmlyNonexpansiveOn (D : Set H) (T : H → H) : Prop :=
  IsFirmlyNonexpansiveOn (fun x : D ↦ T x)

/-- Thin compatibility bridge for ambient self-maps: the restricted map formulation rewrites to
the displayed ambient inequality on `D`. -/
-- Proof sketch: rewrite the subtype residual inequality in ambient coordinates and rearrange.
theorem ambientFirmlyNonexpansiveOn_iff {D : Set H} {T : H → H} :
    AmbientFirmlyNonexpansiveOn D T ↔
      ∀ x ∈ D, ∀ y ∈ D,
        ‖T x - T y‖ ^ 2 + ‖(x - T x) - (y - T y)‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  constructor
  · intro h x hx y hy
    have hxy :
        ‖T x - T y‖ ^ 2 ≤ ‖x - y‖ ^ 2 - ‖(x - T x) - (y - T y)‖ ^ 2 := by
      simpa using h ⟨x, hx⟩ ⟨y, hy⟩
    nlinarith
  · intro h x y
    have hxy :
        ‖T x - T y‖ ^ 2 + ‖((x : H) - T x) - ((y : H) - T y)‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 := by
      simpa using h x x.2 y y.2
    nlinarith

/-- Definition 4.1(ii): on the subtype domain `D`, the textbook pairwise nonexpansive inequality
is exactly the canonical `LipschitzWith 1` condition. -/
theorem isNonexpansiveOn_iff {D : Set H} {T : D → H} :
    (∀ x y : D, ‖T x - T y‖ ≤ ‖(x : H) - y‖) ↔ LipschitzWith 1 T := by
  constructor
  · intro hT
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa [Subtype.dist_eq, dist_eq_norm] using hT x y
  · intro hT x y
    simpa [Subtype.dist_eq, dist_eq_norm] using hT.dist_le_mul x y

/-- Restricting an ambient self-map to `D` identifies the textbook pairwise nonexpansive
inequality with the canonical `LipschitzOnWith 1` condition on `D`. -/
theorem isNonexpansiveOn_restrict_iff_lipschitzOnWith_one {D : Set H} {T : H → H} :
    (∀ x ∈ D, ∀ y ∈ D, ‖T x - T y‖ ≤ ‖x - y‖) ↔ LipschitzOnWith 1 T D := by
  constructor
  · intro hT
    refine LipschitzOnWith.of_dist_le_mul ?_
    intro x hx y hy
    simpa [dist_eq_norm] using hT x hx y hy
  · intro hT x hx y hy
    simpa [dist_eq_norm] using hT.dist_le_mul x hx y hy

/-- Definition 4.1(iii): `T : D → H` is strictly nonexpansive when it strictly decreases
distances between distinct points of `D`. -/
def IsStrictlyNonexpansiveOn {D : Set H} (T : D → H) : Prop :=
  ∀ x y : D, x ≠ y → ‖T x - T y‖ < ‖(x : H) - y‖

/-- Definition 4.1(iii) restated: `IsStrictlyNonexpansiveOn` unfolds to its defining strict
distance inequality. -/
theorem isStrictlyNonexpansiveOn_iff {D : Set H} {T : D → H} :
    IsStrictlyNonexpansiveOn T ↔
      ∀ x y : D, x ≠ y → ‖T x - T y‖ < ‖(x : H) - y‖ := by
  rfl

/-- For an ambient self-map, strict nonexpansiveness on the restriction to `D` is equivalent to
the displayed ambient inequality on `D`. -/
-- Proof sketch: rewrite the subtype inequality in ambient coordinates.
theorem strictlyNonexpansiveOn_iff {D : Set H} {T : H → H} :
    IsStrictlyNonexpansiveOn (fun x : D ↦ T x) ↔
      ∀ x ∈ D, ∀ y ∈ D, x ≠ y → ‖T x - T y‖ < ‖x - y‖ := by
  constructor
  · intro h x hx y hy hxy
    have hxy' : (⟨x, hx⟩ : D) ≠ ⟨y, hy⟩ := fun hEq ↦ hxy (congrArg Subtype.val hEq)
    simpa using h ⟨x, hx⟩ ⟨y, hy⟩ hxy'
  · intro h x y hxy
    have hxy' : (x : H) ≠ y := fun hEq ↦ hxy (Subtype.ext hEq)
    simpa using h x x.2 y y.2 hxy'

/-- Definition 4.1(iv): `T : D → H` is firmly quasinonexpansive when the firm distance estimate
holds against every fixed point in `D`. -/
def IsFirmlyQuasinonexpansiveOn {D : Set H} (T : D → H) : Prop :=
  ∀ x y : D, T y = (y : H) →
    ‖T x - y‖ ^ 2 + ‖(x : H) - T x‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2

/-- Definition 4.1(iv) restated: `IsFirmlyQuasinonexpansiveOn` unfolds to its defining inequality
against subtype fixed points. -/
theorem isFirmlyQuasinonexpansiveOn_iff {D : Set H} {T : D → H} :
    IsFirmlyQuasinonexpansiveOn T ↔
      ∀ x y : D, T y = (y : H) →
        ‖T x - y‖ ^ 2 + ‖(x : H) - T x‖ ^ 2 ≤ ‖(x : H) - y‖ ^ 2 := by
  rfl

/-- Thin compatibility bridge: an ambient self-map is firmly quasinonexpansive on `D` when its
restriction to `D` is firmly quasinonexpansive. -/
def FirmlyQuasinonexpansiveOn (D : Set H) (T : H → H) : Prop :=
  IsFirmlyQuasinonexpansiveOn (fun x : D ↦ T x)

/-- Thin compatibility bridge for ambient self-maps: the restricted fixed-point formulation
rewrites to the ambient fixed-point inequality on `D`. -/
-- Proof sketch: convert fixed points in `D` into fixed points of the subtype restriction.
theorem firmlyQuasinonexpansiveOn_iff {D : Set H} {T : H → H} :
    FirmlyQuasinonexpansiveOn D T ↔
      ∀ x ∈ D, ∀ y ∈ fixedPointSetOn D T,
        ‖T x - y‖ ^ 2 + ‖T x - x‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
  constructor
  · intro h x hx y hy
    rcases mem_fixedPointSetOn_iff.mp hy with ⟨hyD, hyfix⟩
    simpa [norm_sub_rev] using h ⟨x, hx⟩ ⟨y, hyD⟩ hyfix
  · intro h x y hy
    have hy' : (y : H) ∈ fixedPointSetOn D T := by
      exact mem_fixedPointSetOn_iff.mpr ⟨y.2, hy⟩
    simpa [norm_sub_rev] using h x x.2 y hy'

/-- Definition 4.1(v): `T : D → H` is quasinonexpansive when it does not increase distance to any
fixed point in `D`. -/
def IsQuasinonexpansiveOn {D : Set H} (T : D → H) : Prop :=
  ∀ x y : D, T y = (y : H) → ‖T x - y‖ ≤ ‖(x : H) - y‖

/-- Definition 4.1(v) restated: `IsQuasinonexpansiveOn` unfolds to its defining distance
inequality against subtype fixed points. -/
theorem isQuasinonexpansiveOn_iff {D : Set H} {T : D → H} :
    IsQuasinonexpansiveOn T ↔
      ∀ x y : D, T y = (y : H) → ‖T x - y‖ ≤ ‖(x : H) - y‖ := by
  rfl

/-- Thin compatibility bridge: an ambient self-map is quasinonexpansive on `D` when its
restriction to `D` is quasinonexpansive. -/
def QuasinonexpansiveOn (D : Set H) (T : H → H) : Prop :=
  IsQuasinonexpansiveOn (fun x : D ↦ T x)

/-- Thin compatibility bridge for ambient self-maps: the restricted fixed-point formulation
rewrites to the ambient fixed-point inequality on `D`. -/
-- Proof sketch: convert fixed points in `D` into fixed points of the subtype restriction.
theorem quasinonexpansiveOn_iff {D : Set H} {T : H → H} :
    QuasinonexpansiveOn D T ↔
      ∀ x ∈ D, ∀ y ∈ fixedPointSetOn D T, ‖T x - y‖ ≤ ‖x - y‖ := by
  constructor
  · intro h x hx y hy
    rcases mem_fixedPointSetOn_iff.mp hy with ⟨hyD, hyfix⟩
    simpa using h ⟨x, hx⟩ ⟨y, hyD⟩ hyfix
  · intro h x y hy
    have hy' : (y : H) ∈ fixedPointSetOn D T := by
      exact mem_fixedPointSetOn_iff.mpr ⟨y.2, hy⟩
    simpa using h x x.2 y hy'

/-- A `1`-Lipschitz map on `D` is quasinonexpansive there. -/
theorem LipschitzOnWith.quasinonexpansiveOn {D : Set H} {T : H → H}
    (hT : LipschitzOnWith 1 T D) :
    QuasinonexpansiveOn D T := by
  rw [quasinonexpansiveOn_iff]
  intro x hx y hy
  rcases mem_fixedPointSetOn_iff.mp hy with ⟨hyD, hyfixed⟩
  have hxy : ‖T x - y‖ ≤ (1 : ℝ) * ‖x - y‖ := by
    simpa [hyfixed, dist_eq_norm] using hT.dist_le_mul x hx y hyD
  simpa using hxy

/-- Definition 4.1(vi): `T : D → H` is strictly quasinonexpansive when every non-fixed point of
`D` moves strictly closer to each fixed point in `D`. -/
def IsStrictlyQuasinonexpansiveOn {D : Set H} (T : D → H) : Prop :=
  ∀ x y : D, T y = (y : H) → T x ≠ (x : H) → ‖T x - y‖ < ‖(x : H) - y‖

/-- Definition 4.1(vi) restated: `IsStrictlyQuasinonexpansiveOn` unfolds to its defining strict
inequality against subtype fixed points. -/
theorem isStrictlyQuasinonexpansiveOn_iff {D : Set H} {T : D → H} :
    IsStrictlyQuasinonexpansiveOn T ↔
      ∀ x y : D, T y = (y : H) → T x ≠ (x : H) → ‖T x - y‖ < ‖(x : H) - y‖ := by
  rfl

/-- Thin compatibility bridge: an ambient self-map is strictly quasinonexpansive on `D` when its
restriction to `D` is strictly quasinonexpansive. -/
def StrictlyQuasinonexpansiveOn (D : Set H) (T : H → H) : Prop :=
  IsStrictlyQuasinonexpansiveOn (fun x : D ↦ T x)

/-- Thin compatibility bridge for ambient self-maps: strict quasinonexpansiveness of the
restricted map rewrites to the ambient fixed-point inequality on `D`. -/
-- Proof sketch: the subtype condition `T x ≠ x` is the same as ambient non-membership in the
-- fixed-point set.
theorem strictlyQuasinonexpansiveOn_iff {D : Set H} {T : H → H} :
    StrictlyQuasinonexpansiveOn D T ↔
      ∀ x ∈ D \ fixedPointSetOn D T, ∀ y ∈ fixedPointSetOn D T, ‖T x - y‖ < ‖x - y‖ := by
  constructor
  · intro h x hx y hy
    rcases mem_fixedPointSetOn_iff.mp hy with ⟨hyD, hyfix⟩
    have hxnot : T x ≠ x := by
      intro hfix
      exact hx.2 <| mem_fixedPointSetOn_iff.mpr ⟨hx.1, hfix⟩
    simpa using h ⟨x, hx.1⟩ ⟨y, hyD⟩ hyfix hxnot
  · intro h x y hy hnot
    have hx : (x : H) ∈ D \ fixedPointSetOn D T := by
      refine ⟨x.2, ?_⟩
      intro hxfix
      exact hnot <| mem_fixedPointSetOn_iff.mp hxfix |>.2
    have hy' : (y : H) ∈ fixedPointSetOn D T := by
      exact mem_fixedPointSetOn_iff.mpr ⟨y.2, hy⟩
    simpa using h x hx y hy'

/-- A strictly quasinonexpansive self-map on `D` is quasinonexpansive there. -/
theorem StrictlyQuasinonexpansiveOn.quasinonexpansiveOn {D : Set H} {T : H → H}
    (hT : StrictlyQuasinonexpansiveOn D T) :
    QuasinonexpansiveOn D T := by
  rw [quasinonexpansiveOn_iff]
  rw [strictlyQuasinonexpansiveOn_iff] at hT
  intro x hx y hy
  by_cases hxFixed : x ∈ fixedPointSetOn D T
  · rw [mem_fixedPointSetOn_iff] at hxFixed
    rcases hxFixed with ⟨_, hxEq⟩
    simp [hxEq]
  · exact le_of_lt (hT x ⟨hx, hxFixed⟩ y hy)

end

/-! Source item: Chap04/FirmlyNonexpansiveOn -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A map `T : D → H` is firmly nonexpansive on `D` when its displacement satisfies the standard
Hilbert-space firm nonexpansiveness inequality for every pair of points in `D`. -/
def FirmlyNonexpansiveOn (D : Set H) (T : D → H) : Prop :=
  ∀ x y : D, ‖T x - T y‖ ^ (2 : ℕ) ≤ inner ℝ ((x : H) - y) (T x - T y)

/-- The predicate `FirmlyNonexpansiveOn D T` unfolds to the displayed inner-product inequality. -/
theorem firmlyNonexpansiveOn_iff (D : Set H) (T : D → H) :
    FirmlyNonexpansiveOn D T ↔
      ∀ x y : D, ‖T x - T y‖ ^ (2 : ℕ) ≤ inner ℝ ((x : H) - y) (T x - T y) := by
  rfl

/-- On the whole space, firm nonexpansiveness is exactly the standard Hilbert-space inequality
`‖T x - T y‖² ≤ ⟪T x - T y, x - y⟫`. -/
theorem firmlyNonexpansiveOn_univ_iff_norm_sq_le_inner {T : H → H} :
    FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T x) ↔
      ∀ x y : H, ‖T x - T y‖ ^ (2 : ℕ) ≤ inner ℝ (T x - T y) (x - y) := by
  rw [firmlyNonexpansiveOn_iff]
  constructor
  · intro h x y
    simpa [real_inner_comm] using h ⟨x, by simp⟩ ⟨y, by simp⟩
  · intro h x y
    simpa [real_inner_comm] using h (x : H) (y : H)

/-- A self-map is firmly nonexpansive when it is firmly nonexpansive on the whole space. -/
def FirmlyNonexpansive (T : H → H) : Prop :=
  FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T x)

/-- Unfolding `FirmlyNonexpansive` recovers the whole-space restriction formulation. -/
@[simp] theorem firmlyNonexpansive_iff_firmlyNonexpansiveOn_univ {T : H → H} :
    FirmlyNonexpansive T ↔
      FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T x) := by
  rfl

/-- On the whole space, firm nonexpansiveness is exactly the standard Hilbert-space inequality
`‖T x - T y‖² ≤ ⟪T x - T y, x - y⟫`. -/
theorem firmlyNonexpansive_iff_norm_sq_le_inner {T : H → H} :
    FirmlyNonexpansive T ↔
      ∀ x y : H, ‖T x - T y‖ ^ (2 : ℕ) ≤ inner ℝ (T x - T y) (x - y) := by
  exact firmlyNonexpansiveOn_univ_iff_norm_sq_le_inner

end

/-! Source item: Chap04/Proposition_4_2 -/


section

variable {E : Type u} {D : Set E}

/-- The fixed points of a map `T : D → E` relative to its domain `D`. -/
def fixedPointsWithin (T : D → E) : Set D :=
  {y | T y = (y : E)}

/-- Membership in `fixedPointsWithin T` means that `T` fixes the point in `D`. -/
-- Proof sketch: unfold `fixedPointsWithin`; the defining predicate is exactly `T y = y`.
@[simp] theorem mem_fixedPointsWithin_iff (T : D → E) {y : D} :
    y ∈ fixedPointsWithin T ↔ T y = (y : E) := by
  -- This is exactly the defining predicate of `fixedPointsWithin`.
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {D : Set E}

/-- The inner-product inequality from Proposition 4.2 (iii). -/
def tx_norm_sq_le_inner_on_fixedPoints (T : D → E) : Prop :=
  ∀ x y : D, T y = (y : E) →
    ‖T x - (y : E)‖ ^ 2 ≤ ⟪(x : E) - (y : E), T x - (y : E)⟫

/-- The inner-product inequality from Proposition 4.2 (iv). -/
def inner_yTx_xTx_nonpos_on_fixedPoints (T : D → E) : Prop :=
  ∀ x y : D, T y = (y : E) →
    ⟪(y : E) - T x, (x : E) - T x⟫ ≤ 0

/-- The inner-product inequality from Proposition 4.2 (v). -/
def displacement_norm_sq_le_inner_on_fixedPoints (T : D → E) : Prop :=
  ∀ x y : D, T y = (y : E) →
    ‖T x - (x : E)‖ ^ 2 ≤ ⟪(y : E) - (x : E), T x - (x : E)⟫

/-- The reflected map `2T - Id` has the same fixed points as `T`. -/
lemma reflectedMap_eq_self_iff (T : D → E) {y : D} :
    (2 : ℝ) • T y - (y : E) = (y : E) ↔ T y = (y : E) := by
  constructor
  · intro hy
    have hzero : (2 : ℝ) • (T y - (y : E)) = 0 := by
      calc
        (2 : ℝ) • (T y - (y : E)) = (2 : ℝ) • T y - (2 : ℝ) • (y : E) := by
          rw [smul_sub]
        _ = ((2 : ℝ) • T y - (y : E)) - (y : E) := by
          simp [two_smul, sub_eq_add_neg, add_assoc]
        _ = 0 := by rw [hy, sub_self]
    rcases smul_eq_zero.mp hzero with htwo | hsub
    · norm_num at htwo
    · exact sub_eq_zero.mp hsub
  · intro hy
    simp [hy, two_smul]

/-- Helper for Proposition 4.2: clause (i) is equivalent to clause (iii) by expanding
`x - y = (x - T x) + (T x - y)`. -/
-- Proof sketch: expand `‖x - y‖ ^ 2` with `norm_add_sq_real`, rewrite
-- `⟪x - y, T x - y⟫` using the same decomposition, and compare the resulting real inequalities.
lemma isFirmlyQuasinonexpansiveOn_iff_tx_norm_sq_le_inner_on_fixedPoints
    (T : D → E) :
    IsFirmlyQuasinonexpansiveOn T ↔ tx_norm_sq_le_inner_on_fixedPoints T := by
  constructor
  · intro hFirm x y hy
    let a : E := (x : E) - T x
    let b : E := T x - (y : E)
    have hdecomp : a + b = (x : E) - (y : E) := by
      -- Reassociate the difference into the source-proof decomposition.
      simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hnorm :
        ‖(x : E) - (y : E)‖ ^ 2 = ‖a‖ ^ 2 + 2 * ⟪a, b⟫ + ‖b‖ ^ 2 := by
      -- Expanding the squared norm isolates the cross term `⟪a, b⟫`.
      simpa [hdecomp] using norm_add_sq_real a b
    have hinner : ⟪(x : E) - (y : E), b⟫ = ⟪a, b⟫ + ‖b‖ ^ 2 := by
      -- The clause (iii) inner product is the same cross term plus `‖b‖^2`.
      calc
        ⟪(x : E) - (y : E), b⟫ = ⟪a + b, b⟫ := by rw [hdecomp]
        _ = ⟪a, b⟫ + ⟪b, b⟫ := by rw [inner_add_left]
        _ = ⟪a, b⟫ + ‖b‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have hFirm' : ‖b‖ ^ 2 + ‖a‖ ^ 2 ≤ ‖(x : E) - (y : E)‖ ^ 2 := by
      simpa [a, b, add_comm, add_left_comm, add_assoc] using hFirm x y hy
    -- The quadratic expansion shows that the missing slack is exactly `2 * ⟪a, b⟫`.
    nlinarith [hFirm', hnorm, hinner]
  · intro hTx x y hy
    let a : E := (x : E) - T x
    let b : E := T x - (y : E)
    have hdecomp : a + b = (x : E) - (y : E) := by
      -- Reassociate the difference into the source-proof decomposition.
      simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hnorm :
        ‖(x : E) - (y : E)‖ ^ 2 = ‖a‖ ^ 2 + 2 * ⟪a, b⟫ + ‖b‖ ^ 2 := by
      -- Expanding the squared norm isolates the same cross term as above.
      simpa [hdecomp] using norm_add_sq_real a b
    have hinner : ⟪(x : E) - (y : E), b⟫ = ⟪a, b⟫ + ‖b‖ ^ 2 := by
      -- Rewriting clause (iii) into the `a`/`b` coordinates makes the reversal identical.
      calc
        ⟪(x : E) - (y : E), b⟫ = ⟪a + b, b⟫ := by rw [hdecomp]
        _ = ⟪a, b⟫ + ⟪b, b⟫ := by rw [inner_add_left]
        _ = ⟪a, b⟫ + ‖b‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have hTx' : ‖b‖ ^ 2 ≤ ⟪(x : E) - (y : E), b⟫ := by
      simpa [b] using hTx x y hy
    -- Reversing the expansion recovers the firm quasinonexpansive inequality.
    nlinarith [hTx', hnorm, hinner]

/-- Helper for Proposition 4.2: clause (iii) is equivalent to clause (iv) by a sign change in the
cross term. -/
-- Proof sketch: rewrite `⟪x - y, T x - y⟫` using `x - y = (x - T x) + (T x - y)`, and rewrite
-- `⟪y - T x, x - T x⟫` as the negative of the same cross term.
lemma tx_norm_sq_le_inner_on_fixedPoints_iff_inner_yTx_xTx_nonpos_on_fixedPoints
    (T : D → E) :
    tx_norm_sq_le_inner_on_fixedPoints T ↔ inner_yTx_xTx_nonpos_on_fixedPoints T := by
  constructor
  · intro hTx x y hy
    let a : E := (x : E) - T x
    let b : E := T x - (y : E)
    have hdecomp : a + b = (x : E) - (y : E) := by
      -- Use the same decomposition as in the `(i) ↔ (iii)` step.
      simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hinner : ⟪(x : E) - (y : E), b⟫ = ⟪a, b⟫ + ‖b‖ ^ 2 := by
      -- Clause (iii) differs from `0 ≤ ⟪a, b⟫` only by the `‖b‖^2` term.
      calc
        ⟪(x : E) - (y : E), b⟫ = ⟪a + b, b⟫ := by rw [hdecomp]
        _ = ⟪a, b⟫ + ⟪b, b⟫ := by rw [inner_add_left]
        _ = ⟪a, b⟫ + ‖b‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have hsign : ⟪(y : E) - T x, (x : E) - T x⟫ = -⟪a, b⟫ := by
      -- Clause (iv) is the nonpositivity of the same cross term with the opposite sign.
      calc
        ⟪(y : E) - T x, (x : E) - T x⟫ = ⟪-b, a⟫ := by simp [a, b]
        _ = -⟪b, a⟫ := by rw [inner_neg_left]
        _ = -⟪a, b⟫ := by rw [real_inner_comm]
    have hTx' : ‖b‖ ^ 2 ≤ ⟪(x : E) - (y : E), b⟫ := by
      simpa [b] using hTx x y hy
    -- Both clauses reduce to the sign of `⟪a, b⟫`.
    nlinarith [hTx', hinner, hsign]
  · intro hInner x y hy
    let a : E := (x : E) - T x
    let b : E := T x - (y : E)
    have hdecomp : a + b = (x : E) - (y : E) := by
      -- Use the same decomposition as in the forward direction.
      simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hinner : ⟪(x : E) - (y : E), b⟫ = ⟪a, b⟫ + ‖b‖ ^ 2 := by
      -- Clause (iii) still differs from `0 ≤ ⟪a, b⟫` only by `‖b‖^2`.
      calc
        ⟪(x : E) - (y : E), b⟫ = ⟪a + b, b⟫ := by rw [hdecomp]
        _ = ⟪a, b⟫ + ⟪b, b⟫ := by rw [inner_add_left]
        _ = ⟪a, b⟫ + ‖b‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have hsign : ⟪(y : E) - T x, (x : E) - T x⟫ = -⟪a, b⟫ := by
      -- Clause (iv) is the same scalar inequality with the sign flipped.
      calc
        ⟪(y : E) - T x, (x : E) - T x⟫ = ⟪-b, a⟫ := by simp [a, b]
        _ = -⟪b, a⟫ := by rw [inner_neg_left]
        _ = -⟪a, b⟫ := by rw [real_inner_comm]
    have hInner' : ⟪(y : E) - T x, (x : E) - T x⟫ ≤ 0 := by
      simpa using hInner x y hy
    -- Reversing the sign change recovers clause (iii).
    nlinarith [hInner', hinner, hsign]

/-- Helper for Proposition 4.2: clause (iv) is equivalent to clause (v) by expanding
`y - T x = (y - x) + (x - T x)`. -/
-- Proof sketch: expand the left inner product in clause (iv), identify the self-inner-product
-- with `‖x - T x‖^2`, and rewrite `T x - x = - (x - T x)`.
lemma inner_yTx_xTx_nonpos_on_fixedPoints_iff_displacement_norm_sq_le_inner_on_fixedPoints
    (T : D → E) :
    inner_yTx_xTx_nonpos_on_fixedPoints T ↔
      displacement_norm_sq_le_inner_on_fixedPoints T := by
  constructor
  · intro hInner x y hy
    let a : E := (x : E) - T x
    have hsplit : (y : E) - T x = ((y : E) - (x : E)) + a := by
      -- This is the source-proof decomposition for clause (iv).
      dsimp [a]
      abel_nf
    have hrewrite :
        ⟪(y : E) - T x, (x : E) - T x⟫ =
          ⟪(y : E) - (x : E), a⟫ + ‖a‖ ^ 2 := by
      -- Expanding clause (iv) isolates the displacement norm term.
      calc
        ⟪(y : E) - T x, (x : E) - T x⟫ = ⟪((y : E) - (x : E)) + a, a⟫ := by
          rw [hsplit]
        _ = ⟪(y : E) - (x : E), a⟫ + ⟪a, a⟫ := by rw [inner_add_left]
        _ = ⟪(y : E) - (x : E), a⟫ + ‖a‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have hsign : ⟪(y : E) - (x : E), T x - (x : E)⟫ = -⟪(y : E) - (x : E), a⟫ := by
      -- The target clause uses `T x - x`, which is the negative of `a`.
      calc
        ⟪(y : E) - (x : E), T x - (x : E)⟫ = ⟪(y : E) - (x : E), -a⟫ := by
          simp [a]
        _ = -⟪(y : E) - (x : E), a⟫ := by rw [inner_neg_right]
    have hInner' : ⟪(y : E) - T x, (x : E) - T x⟫ ≤ 0 := by
      simpa using hInner x y hy
    have ha : ‖a‖ ^ 2 ≤ ⟪(y : E) - (x : E), T x - (x : E)⟫ := by
      -- Rearranging the expanded clause (iv) yields exactly clause (v) in `a`-coordinates.
      nlinarith [hInner', hrewrite, hsign]
    simpa [a, norm_sub_rev] using ha
  · intro hDisp x y hy
    let a : E := (x : E) - T x
    have hsplit : (y : E) - T x = ((y : E) - (x : E)) + a := by
      -- Use the same decomposition as in the forward direction.
      dsimp [a]
      abel_nf
    have hrewrite :
        ⟪(y : E) - T x, (x : E) - T x⟫ =
          ⟪(y : E) - (x : E), a⟫ + ‖a‖ ^ 2 := by
      -- Expanding clause (iv) isolates the same displacement norm term.
      calc
        ⟪(y : E) - T x, (x : E) - T x⟫ = ⟪((y : E) - (x : E)) + a, a⟫ := by
          rw [hsplit]
        _ = ⟪(y : E) - (x : E), a⟫ + ⟪a, a⟫ := by rw [inner_add_left]
        _ = ⟪(y : E) - (x : E), a⟫ + ‖a‖ ^ 2 := by rw [real_inner_self_eq_norm_sq]
    have hsign : ⟪(y : E) - (x : E), T x - (x : E)⟫ = -⟪(y : E) - (x : E), a⟫ := by
      -- Rewrite the clause (v) inner product back to `a`.
      calc
        ⟪(y : E) - (x : E), T x - (x : E)⟫ = ⟪(y : E) - (x : E), -a⟫ := by
          simp [a]
        _ = -⟪(y : E) - (x : E), a⟫ := by rw [inner_neg_right]
    have ha : ‖a‖ ^ 2 ≤ ⟪(y : E) - (x : E), T x - (x : E)⟫ := by
      simpa [a, norm_sub_rev] using hDisp x y hy
    -- Reversing the rearrangement recovers clause (iv).
    nlinarith [ha, hrewrite, hsign]

/-- Helper for Proposition 4.2: clause (ii) is equivalent to clause (iii) via the reflection
identity from Lemma 2.17. -/
-- Proof sketch: rewrite `((2T - Id) x) - y` as `2 • (T x - y) - (x - y)`, square the norm
-- inequality, and use `norm_sq_sub_norm_sq_reflection_eq_four_mul`.
lemma isQuasinonexpansiveOn_reflectedMap_iff_tx_norm_sq_le_inner_on_fixedPoints
    (T : D → E) :
    IsQuasinonexpansiveOn (fun x : D ↦ (2 : ℝ) • T x - (x : E)) ↔
      tx_norm_sq_le_inner_on_fixedPoints T := by
  constructor
  · intro hRef x y hy
    let u : E := (x : E) - (y : E)
    let v : E := T x - (y : E)
    have hyRef : ((2 : ℝ) • T y - (y : E)) = (y : E) :=
      (reflectedMap_eq_self_iff T).2 hy
    have hreflect : ((2 : ℝ) • T x - (x : E)) - (y : E) = (2 : ℝ) • v - u := by
      -- Center the reflected map at the fixed point `y`.
      dsimp [u, v]
      rw [two_smul, two_smul]
      abel_nf
    have hnorm : ‖(2 : ℝ) • v - u‖ ≤ ‖u‖ := by
      simpa [hreflect, u, v] using hRef x y hyRef
    have hsq : ‖(2 : ℝ) • v - u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hnorm
    have hgap :
        ‖u‖ ^ 2 - ‖(2 : ℝ) • v - u‖ ^ 2 = 4 * (⟪u, v⟫ - ‖v‖ ^ 2) := by
      -- The reflected norm gap is exactly the clause (iii) scalar gap.
      simpa using norm_sq_sub_norm_sq_reflection_eq_four_mul u v
    have huv : ‖v‖ ^ 2 ≤ ⟪u, v⟫ := by
      -- The nonexpansive estimate is exactly nonnegativity of the reflected norm gap.
      nlinarith [hsq, hgap]
    simpa [u, v] using huv
  · intro hTx x y hy
    let u : E := (x : E) - (y : E)
    let v : E := T x - (y : E)
    have hyT : T y = (y : E) :=
      (reflectedMap_eq_self_iff T).1 hy
    have hreflect : ((2 : ℝ) • T x - (x : E)) - (y : E) = (2 : ℝ) • v - u := by
      -- Center the reflected map at the same fixed point `y`.
      dsimp [u, v]
      rw [two_smul, two_smul]
      abel_nf
    have huv : ‖v‖ ^ 2 ≤ ⟪u, v⟫ := by
      simpa [u, v] using hTx x y hyT
    have hgap :
        ‖u‖ ^ 2 - ‖(2 : ℝ) • v - u‖ ^ 2 = 4 * (⟪u, v⟫ - ‖v‖ ^ 2) := by
      -- The same reflected norm identity converts clause (iii) back into the norm gap.
      simpa using norm_sq_sub_norm_sq_reflection_eq_four_mul u v
    have hsq : ‖(2 : ℝ) • v - u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
      -- The clause (iii) inequality makes the reflected norm gap nonnegative.
      nlinarith [huv, hgap]
    have hnorm : ‖(2 : ℝ) • v - u‖ ≤ ‖u‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
    simpa [hreflect, u, v] using hnorm

/-- Proposition 4.2: for a map `T : D → E`, firm quasinonexpansiveness, quasinonexpansiveness of
the reflected map `2T - Id`, and the three equivalent fixed-point inner-product inequalities
from (iii), (iv), and (v) are all equivalent. -/
-- Proof sketch: prove `(i) ↔ (iii)` by expanding `‖x - y‖ ^ 2`, prove `(iii) ↔ (iv)` and
-- `(iv) ↔ (v)` by rearranging inner products, and prove `(ii) ↔ (iii)` by expanding the square
-- of `‖(2T - Id) x - y‖`.
theorem firmly_quasinonexpansive_on_tfae (T : D → E) :
    [ IsFirmlyQuasinonexpansiveOn T,
      IsQuasinonexpansiveOn (fun x : D ↦ (2 : ℝ) • T x - (x : E)),
      tx_norm_sq_le_inner_on_fixedPoints T,
      inner_yTx_xTx_nonpos_on_fixedPoints T,
      displacement_norm_sq_le_inner_on_fixedPoints T ].TFAE := by
  -- Route correction: use clause (iii) as the hub so each source-proof rewrite is isolated once.
  tfae_have 1 ↔ 3 := by
    -- Expand `x - y = (x - T x) + (T x - y)` to compare clauses (i) and (iii).
    exact isFirmlyQuasinonexpansiveOn_iff_tx_norm_sq_le_inner_on_fixedPoints T
  tfae_have 3 ↔ 4 := by
    -- Rewrite clause (iv) as the sign change of the cross term from clause (iii).
    exact tx_norm_sq_le_inner_on_fixedPoints_iff_inner_yTx_xTx_nonpos_on_fixedPoints T
  tfae_have 4 ↔ 5 := by
    -- Expand `y - T x = (y - x) + (x - T x)` to compare clauses (iv) and (v).
    exact inner_yTx_xTx_nonpos_on_fixedPoints_iff_displacement_norm_sq_le_inner_on_fixedPoints T
  tfae_have 2 ↔ 3 := by
    -- Lemma 2.17 identifies the reflected norm gap with the clause (iii) scalar gap.
    exact isQuasinonexpansiveOn_reflectedMap_iff_tx_norm_sq_le_inner_on_fixedPoints T
  tfae_finish

end

/-! Source item: Chap04/Proposition_4_3 -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 4.3: rewrite the relaxed affine displacement from a fixed point as the
original displacement plus a scaled residual. -/
private lemma relaxed_sub_fixedPoint_eq_add_smul_residual {D : Set H} (T : D → H) (lam : ℝ)
    (x y : D) :
    ((1 - lam) • (x : H) + lam • T x) - (y : H) = ((x : H) - y) + lam • (T x - (x : H)) := by
  simp [sub_eq_add_neg, add_smul, add_assoc, add_left_comm, add_comm]

/-- Helper for Proposition 4.3: firm quasinonexpansiveness forces the cross term in the textbook
expansion to be at most the negative residual norm square. -/
private lemma inner_le_neg_residual_norm_sq_of_firmly_quasinonexpansive {D : Set H} {T : D → H}
    (hT : IsFirmlyQuasinonexpansiveOn T) (x y : D) (hy : T y = (y : H)) :
    inner ℝ ((x : H) - y) (T x - (x : H)) ≤ -‖T x - (x : H)‖ ^ 2 := by
  -- Expand the firm inequality at `x` and the fixed point `y`.
  have hineq := hT x y hy
  have hexpand :
      ‖T x - (y : H)‖ ^ 2 =
        ‖(x : H) - y‖ ^ 2 + 2 * inner ℝ ((x : H) - y) (T x - (x : H)) +
          ‖T x - (x : H)‖ ^ 2 := by
    -- Rewrite `T x - y` as `(x - y) + (T x - x)` and expand the squared norm.
    rw [show T x - (y : H) = ((x : H) - y) + (T x - (x : H)) by
      abel_nf]
    simpa using norm_add_sq_real ((x : H) - y) (T x - (x : H))
  have hres : ‖(x : H) - T x‖ ^ 2 = ‖T x - (x : H)‖ ^ 2 := by
    -- The two residuals differ only by sign.
    rw [norm_sub_rev]
  -- Cancelling the common `‖x - y‖^2` term yields the desired cross-term bound.
  nlinarith [hineq, hexpand, hres]

/-- Helper for Proposition 4.3: exact expansion of the relaxed affine displacement squared norm. -/
private lemma sq_norm_relaxed_sub_fixedPoint_eq {D : Set H} {T : D → H} (lam : ℝ) (x y : D) :
    ‖((1 - lam) • (x : H) + lam • T x) - (y : H)‖ ^ 2 =
      ‖(x : H) - y‖ ^ 2 +
        2 * lam * inner ℝ ((x : H) - y) (T x - (x : H)) +
        lam ^ 2 * ‖T x - (x : H)‖ ^ 2 := by
  -- Rewrite the relaxed displacement into the affine textbook form.
  rw [relaxed_sub_fixedPoint_eq_add_smul_residual]
  -- Expand `‖u + lam • v‖^2` and normalize the scalar terms.
  rw [norm_add_sq_real]
  rw [real_inner_smul_right]
  rw [show ‖lam • (T x - (x : H))‖ ^ 2 = lam ^ 2 * ‖T x - (x : H)‖ ^ 2 by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]]
  ring

/-- Proposition 4.3: if `T` is firmly quasinonexpansive on `D`, then every nonnegative
relaxation `x ↦ (1 - λ) • x + λ • T x` satisfies the estimate
`‖((1 - λ) • x + λ • T x) - y‖^2 ≤ ‖x - y‖^2 - λ (2 - λ) ‖T x - x‖^2`
at every fixed point `y` of `T` in `D`. -/
-- Proof sketch: expand `‖((1 - lam) • x + lam • T x) - y‖ ^ 2` as
-- `‖(x - y) + lam • (T x - x)‖ ^ 2`, use firm quasinonexpansiveness to bound the cross term by
-- `-‖T x - x‖ ^ 2`, and simplify the resulting quadratic polynomial in `lam`.
theorem sq_norm_relaxedMap_sub_fixedPoint_le {D : Set H} {T : D → H}
    (hT : IsFirmlyQuasinonexpansiveOn T) {lam : ℝ} (hlam : 0 ≤ lam) (x y : D)
    (hy : T y = (y : H)) :
    ‖((1 - lam) • (x : H) + lam • T x) - (y : H)‖ ^ 2 ≤
      ‖(x : H) - y‖ ^ 2 - lam * (2 - lam) * ‖T x - (x : H)‖ ^ 2 := by
  rw [sq_norm_relaxed_sub_fixedPoint_eq]
  have hinner :=
    inner_le_neg_residual_norm_sq_of_firmly_quasinonexpansive hT x y hy
  have hcross :
      2 * lam * inner ℝ ((x : H) - y) (T x - (x : H)) ≤
        -(2 * lam) * ‖T x - (x : H)‖ ^ 2 := by
    nlinarith
  nlinarith [hcross]

end

/-! Source item: Chap04/Proposition_4_4 -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The residual map `Id - T` associated to a partially defined operator. -/
def residualMap (D : Set H) (T : D → H) : D → H :=
  fun x ↦ (x : H) - T x

/-- The reflected map `2T - Id` associated to a partially defined operator. -/
def reflectedMap (D : Set H) (T : D → H) : D → H :=
  fun x ↦ (2 : ℝ) • T x - x

/-- Helper for Proposition 4.4: a convex combination of `a` and `b` can be rewritten as
`b - α • (b - a)`. -/
private lemma segment_combination_eq_sub_smul (a b : H) (α : ℝ) :
    α • a + (1 - α) • b = b - α • (b - a) := by
  -- Rewrite the coefficient `(1 - α)` and then collect the additive terms.
  calc
    α • a + (1 - α) • b = α • a + (b - α • b) := by
      rw [sub_smul, one_smul]
    _ = b + (α • a - α • b) := by
      abel_nf
    _ = b - α • (b - a) := by
      rw [smul_sub]
      abel_nf

/-- Helper for Proposition 4.4: the reflected norm gap equals four times the firm
inner-product defect. -/
private lemma reflection_norm_gap_eq_four_mul (a b : H) :
    ‖a‖ ^ 2 - ‖(2 : ℝ) • b - a‖ ^ 2 = 4 * (inner ℝ a b - ‖b‖ ^ 2) := by
  have htwo : (2 : ℝ) • b = b + b := by
    simpa using (two_smul ℝ b)
  rw [htwo]
  have hsub : ‖a‖ ^ 2 - ‖(b + b) - a‖ ^ 2 = 2 * inner ℝ (b + b) a - ‖b + b‖ ^ 2 := by
    -- First isolate the reflected norm term using the standard `‖u - v‖²` identity.
    nlinarith [norm_sub_sq_real (b + b) a]
  have hnorm : ‖b + b‖ ^ 2 = 4 * ‖b‖ ^ 2 := by
    -- Then expand the doubled point `b + b`.
    rw [norm_add_sq_real, real_inner_self_eq_norm_sq]
    ring
  -- Assemble the two expansions and commute the inner product once.
  rw [hsub, hnorm, inner_add_left, real_inner_comm b a]
  ring

/-- Helper for Proposition 4.4: expanding `‖x - α • y‖² - ‖x‖²` factors the defect by `α`. -/
private lemma norm_sub_smul_defect_eq_factorized (x y : H) (α : ℝ) :
    ‖x - α • y‖ * ‖x - α • y‖ - ‖x‖ * ‖x‖ =
      α * (α * (‖y‖ * ‖y‖) - 2 * inner ℝ x y) := by
  -- Rewrite the norm defect using the standard real inner-product expansion.
  calc
    ‖x - α • y‖ * ‖x - α • y‖ - ‖x‖ * ‖x‖
        = (‖x‖ * ‖x‖ - 2 * inner ℝ x (α • y) + ‖α • y‖ * ‖α • y‖) - ‖x‖ * ‖x‖ := by
            rw [norm_sub_mul_self_real]
    _ = -2 * inner ℝ x (α • y) + ‖α • y‖ * ‖α • y‖ := by ring
    _ = -2 * (α * inner ℝ x y) + ‖α • y‖ * ‖α • y‖ := by
          rw [real_inner_smul_right]
    _ = -2 * (α * inner ℝ x y) + (|α| * ‖y‖) * (|α| * ‖y‖) := by
          rw [norm_smul, Real.norm_eq_abs]
    _ = -2 * (α * inner ℝ x y) + (α * α) * (‖y‖ * ‖y‖) := by
          rw [show (|α| * ‖y‖) * (|α| * ‖y‖) = (|α| * |α|) * (‖y‖ * ‖y‖) by ring,
            abs_mul_abs_self]
    _ = α * (α * (‖y‖ * ‖y‖) - 2 * inner ℝ x y) := by ring

/-- Helper for Proposition 4.4: if `‖x‖ ≤ ‖x - α • y‖` on `[0,1]`, then `inner ℝ x y ≤ 0`. -/
private lemma inner_nonpos_of_unit_interval_sub_smul_norm_lower_bound (x y : H)
    (h : ∀ α : Set.Icc (0 : ℝ) 1, ‖x‖ ≤ ‖x - (α : ℝ) • y‖) :
    inner ℝ x y ≤ 0 := by
  by_contra hxy
  have hxy_pos : 0 < inner ℝ x y := lt_of_not_ge hxy
  let β : ℝ := inner ℝ x y / (‖y‖ * ‖y‖ + 1)
  let α : ℝ := min 1 β
  have hden : 0 < ‖y‖ * ‖y‖ + 1 := by
    positivity
  have hβ_pos : 0 < β := by
    exact div_pos hxy_pos hden
  have hα_pos : 0 < α := by
    dsimp [α]
    exact (lt_min_iff.mpr ⟨zero_lt_one, hβ_pos⟩)
  have hα_mem : α ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨le_of_lt hα_pos, ?_⟩
    dsimp [α]
    exact min_le_left _ _
  -- Evaluate the interval hypothesis at a small positive scalar.
  have hα_norm : ‖x‖ ≤ ‖x - α • y‖ := h ⟨α, hα_mem⟩
  have hα_sq : ‖x‖ * ‖x‖ ≤ ‖x - α • y‖ * ‖x - α • y‖ := by
    nlinarith [hα_norm, norm_nonneg x, norm_nonneg (x - α • y)]
  have hdef_nonneg : 0 ≤ ‖x - α • y‖ * ‖x - α • y‖ - ‖x‖ * ‖x‖ := by
    nlinarith
  -- The special choice of `α` makes the quadratic defect strictly negative.
  have hβ_eq : β * (‖y‖ * ‖y‖ + 1) = inner ℝ x y := by
    simp [β, hden.ne']
  have hnorm_sq_nonneg : 0 ≤ ‖y‖ * ‖y‖ := by
    positivity
  have hβ_lt : β * (‖y‖ * ‖y‖) < inner ℝ x y := by
    nlinarith [hβ_eq, hβ_pos]
  have hα_le_β : α ≤ β := by
    dsimp [α]
    exact min_le_right _ _
  have hα_lt : α * (‖y‖ * ‖y‖) < inner ℝ x y := by
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hα_le_β hnorm_sq_nonneg) hβ_lt
  have hfactor_neg : α * (α * (‖y‖ * ‖y‖) - 2 * inner ℝ x y) < 0 := by
    have : α * (‖y‖ * ‖y‖) - 2 * inner ℝ x y < 0 := by
      nlinarith [hα_lt, hxy_pos]
    exact mul_neg_of_pos_of_neg hα_pos this
  rw [norm_sub_smul_defect_eq_factorized] at hdef_nonneg
  linarith

/-- Helper for Proposition 4.4: firm nonexpansiveness of the residual map is equivalent to the
firm nonexpansiveness of `T` itself. -/
lemma firmlyNonexpansiveOn_residualMap_iff (D : Set H) (T : D → H) :
    FirmlyNonexpansiveOn D (residualMap D T) ↔ FirmlyNonexpansiveOn D T := by
  rw [firmlyNonexpansiveOn_iff]
  constructor
  · intro h x y
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hxy : ‖residualMap D T x - residualMap D T y‖ ^ 2 ≤
        inner ℝ ((x : H) - y) (residualMap D T x - residualMap D T y) := h x y
    have hres : residualMap D T x - residualMap D T y = a - b := by
      change (((x : H) - T x) - (y - T y)) = a - b
      dsimp [a, b]
      abel_nf
    have hinner : inner ℝ a (a - b) = ‖a‖ ^ 2 - inner ℝ a b := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
    -- Expanding the residual inequality leaves exactly the firm inequality for `T`.
    rw [hres] at hxy
    nlinarith [norm_sub_sq_real a b, hinner]
  · intro h x y
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hxy : ‖b‖ ^ 2 ≤ inner ℝ a b := h x y
    have hres : residualMap D T x - residualMap D T y = a - b := by
      change (((x : H) - T x) - (y - T y)) = a - b
      dsimp [a, b]
      abel_nf
    have hinner : inner ℝ a (a - b) = ‖a‖ ^ 2 - inner ℝ a b := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
    -- The same quadratic identity runs backwards to recover firm nonexpansiveness of `Id - T`.
    rw [hres]
    nlinarith [norm_sub_sq_real a b, hinner]

/-- Helper for Proposition 4.4: nonexpansiveness of the reflected map is equivalent to firm
nonexpansiveness of `T`. -/
lemma reflectedMap_nonexpansive_iff_firmlyNonexpansiveOn (D : Set H) (T : D → H) :
    (∀ x y : D, ‖reflectedMap D T x - reflectedMap D T y‖ ≤ ‖(x : H) - y‖) ↔
      FirmlyNonexpansiveOn D T := by
  rw [firmlyNonexpansiveOn_iff]
  constructor
  · intro h x y
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hxy : ‖reflectedMap D T x - reflectedMap D T y‖ ≤ ‖(x : H) - y‖ := h x y
    have hreflect : reflectedMap D T x - reflectedMap D T y = (2 : ℝ) • b - a := by
      calc
        reflectedMap D T x - reflectedMap D T y
            = ((2 : ℝ) • T x - (2 : ℝ) • T y) - ((x : H) - y) := by
                simp [reflectedMap]
                abel_nf
        _ = (2 : ℝ) • (T x - T y) - ((x : H) - y) := by rw [smul_sub]
        _ = (2 : ℝ) • b - a := by dsimp [a, b]
    have hsq : ‖(2 : ℝ) • b - a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
      rw [← hreflect]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hxy
    -- Lemma 2.17 turns the reflected norm gap into the firm inner-product inequality.
    nlinarith [reflection_norm_gap_eq_four_mul a b, hsq]
  · intro h x y
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hxy : ‖b‖ ^ 2 ≤ inner ℝ a b := h x y
    have hreflect : reflectedMap D T x - reflectedMap D T y = (2 : ℝ) • b - a := by
      calc
        reflectedMap D T x - reflectedMap D T y
            = ((2 : ℝ) • T x - (2 : ℝ) • T y) - ((x : H) - y) := by
                simp [reflectedMap]
                abel_nf
        _ = (2 : ℝ) • (T x - T y) - ((x : H) - y) := by rw [smul_sub]
        _ = (2 : ℝ) • b - a := by dsimp [a, b]
    have hsq : ‖(2 : ℝ) • b - a‖ ^ 2 ≤ ‖a‖ ^ 2 := by
      nlinarith [reflection_norm_gap_eq_four_mul a b, hxy]
    -- Squared norm control gives the original nonexpansive estimate because norms are nonnegative.
    rw [hreflect]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

/-- Helper for Proposition 4.4: the residual cross-term condition is equivalent to firm
nonexpansiveness of `T`. -/
private lemma residual_cross_nonneg_iff_firmlyNonexpansiveOn (D : Set H) (T : D → H) :
    (∀ x y : D, 0 ≤ inner ℝ (T x - T y) (residualMap D T x - residualMap D T y)) ↔
      FirmlyNonexpansiveOn D T := by
  rw [firmlyNonexpansiveOn_iff]
  constructor
  · intro h x y
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hxy : 0 ≤ inner ℝ (T x - T y) (residualMap D T x - residualMap D T y) := h x y
    have hres : residualMap D T x - residualMap D T y = a - b := by
      change (((x : H) - T x) - (y - T y)) = a - b
      dsimp [a, b]
      abel_nf
    have hinner : inner ℝ b (a - b) = inner ℝ a b - ‖b‖ ^ 2 := by
      rw [inner_sub_right, real_inner_comm b a, real_inner_self_eq_norm_sq]
    -- Expanding the residual inner product shows that clause (v) is exactly clause (iv).
    rw [hres] at hxy
    nlinarith [hinner]
  · intro h x y
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hxy : ‖b‖ ^ 2 ≤ inner ℝ a b := h x y
    have hres : residualMap D T x - residualMap D T y = a - b := by
      change (((x : H) - T x) - (y - T y)) = a - b
      dsimp [a, b]
      abel_nf
    have hinner : inner ℝ b (a - b) = inner ℝ a b - ‖b‖ ^ 2 := by
      rw [inner_sub_right, real_inner_comm b a, real_inner_self_eq_norm_sq]
    -- The same identity turns the firm inequality back into the residual cross-term condition.
    rw [hres]
    nlinarith [hinner, hxy]

/-- Helper for Proposition 4.4: the residual cross-term sign condition is equivalent to the norm
lower bound along every segment joining `T x - T y` to `(x - y)`. -/
private lemma segment_norm_lower_bound_iff_residual_cross_nonneg (D : Set H) (T : D → H) :
    (∀ x y : D, 0 ≤ inner ℝ (T x - T y) (residualMap D T x - residualMap D T y)) ↔
      ∀ (x y : D) (α : ℝ), α ∈ Set.Icc (0 : ℝ) 1 →
        ‖T x - T y‖ ≤ ‖α • ((x : H) - y) + (1 - α) • (T x - T y)‖ := by
  constructor
  · intro h x y α hα
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hxy : 0 ≤ inner ℝ b (residualMap D T x - residualMap D T y) := by
      simpa [b] using h x y
    have hres : residualMap D T x - residualMap D T y = a - b := by
      change (((x : H) - T x) - (y - T y)) = a - b
      dsimp [a, b]
      abel_nf
    have hnonpos : inner ℝ b (b - a) ≤ 0 := by
      rw [hres] at hxy
      have hsum : inner ℝ b (a - b) + inner ℝ b (b - a) = 0 := by
        rw [← inner_add_right]
        abel_nf
        simp
      nlinarith
    have hβ : ‖b‖ ≤ ‖b - α • (b - a)‖ := by
      have hα_nonneg : 0 ≤ α := hα.1
      have hterm_nonneg : 0 ≤ α * (‖b - a‖ * ‖b - a‖) - 2 * inner ℝ b (b - a) := by
        have hnorm_nonneg : 0 ≤ ‖b - a‖ * ‖b - a‖ := by positivity
        nlinarith [hnonpos, hα_nonneg, hnorm_nonneg]
      have hfactor_nonneg : 0 ≤ α * (α * (‖b - a‖ * ‖b - a‖) - 2 * inner ℝ b (b - a)) := by
        exact mul_nonneg hα_nonneg hterm_nonneg
      have hsq : ‖b‖ * ‖b‖ ≤ ‖b - α • (b - a)‖ * ‖b - α • (b - a)‖ := by
        nlinarith [norm_sub_smul_defect_eq_factorized b (b - a) α, hfactor_nonneg]
      have hsq' : ‖b‖ ^ 2 ≤ ‖b - α • (b - a)‖ ^ 2 := by
        simpa [sq] using hsq
      exact le_of_sq_le_sq hsq' (norm_nonneg _)
    -- Rewrite the convex combination into `b - α • (b - a)`.
    simpa [a, b, segment_combination_eq_sub_smul] using hβ
  · intro h x y
    let a : H := (x : H) - y
    let b : H := T x - T y
    have hsegment :
        ∀ β : Set.Icc (0 : ℝ) 1, ‖b‖ ≤ ‖b - (β : ℝ) • (b - a)‖ := by
      intro β
      have hβ := h x y (β : ℝ) β.2
      simpa [a, b, segment_combination_eq_sub_smul] using hβ
    have hnonpos : inner ℝ b (b - a) ≤ 0 :=
      inner_nonpos_of_unit_interval_sub_smul_norm_lower_bound b (b - a) hsegment
    have hres : residualMap D T x - residualMap D T y = a - b := by
      change (((x : H) - T x) - (y - T y)) = a - b
      dsimp [a, b]
      abel_nf
    -- Rewriting `b - a = -(a - b)` recovers the residual cross-term formulation.
    rw [hres]
    have hsum : inner ℝ b (a - b) + inner ℝ b (b - a) = 0 := by
      rw [← inner_add_right]
      abel_nf
      simp
    nlinarith

-- Proof sketch: Rewrite each clause using the differences `x - y` and `T x - T y`, expand the
-- norms and inner products, and compare the resulting quadratic identities.
/-- Proposition 4.4: for an operator on a subset of a real Hilbert space, firm
nonexpansiveness, firm nonexpansiveness of `Id - T`, nonexpansiveness of `2T - Id`, and the
equivalent inequalities in (iv), (v), and (vi) form a TFAE list. -/
theorem firmlyNonexpansiveOn_tfae (D : Set H) (T : D → H) :
    List.TFAE
      [ FirmlyNonexpansiveOn D T,
        FirmlyNonexpansiveOn D (residualMap D T),
        ∀ x y : D, ‖reflectedMap D T x - reflectedMap D T y‖ ≤ ‖(x : H) - y‖,
        ∀ x y : D, ‖T x - T y‖ ^ 2 ≤ inner ℝ ((x : H) - y) (T x - T y),
        ∀ x y : D, 0 ≤ inner ℝ (T x - T y) (residualMap D T x - residualMap D T y),
        ∀ (x y : D) (α : ℝ), α ∈ Set.Icc (0 : ℝ) 1 →
          ‖T x - T y‖ ≤ ‖α • ((x : H) - y) + (1 - α) • (T x - T y)‖ ] := by
  -- Clause (iv) is the common scalar inequality, so we connect each clause to it.
  tfae_have 1 ↔ 4 := firmlyNonexpansiveOn_iff D T
  tfae_have 1 ↔ 2 := (firmlyNonexpansiveOn_residualMap_iff D T).symm
  tfae_have 1 ↔ 3 := (reflectedMap_nonexpansive_iff_firmlyNonexpansiveOn D T).symm
  tfae_have 1 ↔ 5 := (residual_cross_nonneg_iff_firmlyNonexpansiveOn D T).symm
  -- The last equivalence is the interval-norm characterization from Lemma 2.13.
  tfae_have 5 ↔ 6 := segment_norm_lower_bound_iff_residual_cross_nonneg D T
  tfae_finish

/-! Source item: Chap04/Proposition_4_8 -/
universe v


variable {ι : Type u} {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 4.8: rewrite the exchanged cross terms as diagonal terms minus the
pairwise correction inner product. -/
-- Proof step: expand the pairwise correction by bilinearity and simplify the resulting scalar
-- identity.
private lemma pairwise_inner_exchange_eq_diag_sub_pairwise
    (x u : ι → H) (i j : ι) :
    ⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ =
      ⟪x i, u i⟫_ℝ + ⟪x j, u j⟫_ℝ - ⟪x i - x j, u i - u j⟫_ℝ := by
  have h_expand :
      ⟪x i - x j, u i - u j⟫_ℝ =
        ⟪x i, u i⟫_ℝ - ⟪x i, u j⟫_ℝ - ⟪x j, u i⟫_ℝ + ⟪x j, u j⟫_ℝ := by
    rw [inner_sub_left, inner_sub_right, inner_sub_right]
    ring
  nlinarith [h_expand]

/-- Helper for Proposition 4.8: doubling the inner product of two weighted affine combinations
produces the symmetric double sum of exchanged cross terms. -/
-- Proof step: expand the weighted sums by bilinearity, then commute the second double sum so the
-- exchanged cross term appears pointwise.
private lemma two_mul_weighted_inner_eq_sum_exchange
    (s : Finset ι) (x u : ι → H) (α : ι → ℝ) :
    2 * ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ =
      ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ) := by
  have h_single :
      ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ =
        ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u j⟫_ℝ := by
    -- First expand both weighted sums inside the real inner product.
    simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    ring_nf
  calc
    2 * ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ
        = (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u j⟫_ℝ) +
            (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u j⟫_ℝ) := by
              rw [h_single]
              ring
    _ = (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u j⟫_ℝ) +
          (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x j, u i⟫_ℝ) := by
            congr 1
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro j hj
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [mul_comm (α j) (α i), real_inner_comm]
    _ = ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ) := by
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl ?_
          intro j hj
          ring

/-- Helper for Proposition 4.8: the diagonal double sum collapses to twice the weighted diagonal
sum when the weights add up to `1`. -/
-- Proof step: separate the two diagonal contributions, then use the weight-sum hypothesis on each
-- of the two inner sums.
private lemma weighted_double_sum_diag_eq_two_mul
    (s : Finset ι) (x u : ι → H) (α : ι → ℝ)
    (hα : ∑ i ∈ s, α i = 1) :
    ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u i⟫_ℝ + ⟪x j, u j⟫_ℝ) =
      2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ := by
  calc
    ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u i⟫_ℝ + ⟪x j, u j⟫_ℝ)
        = (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i, u i⟫_ℝ) +
            (∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x j, u j⟫_ℝ) := by
              simp_rw [mul_add, Finset.sum_add_distrib]
    _ = (∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ) + (∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ) := by
          congr 1
          · refine Finset.sum_congr rfl ?_
            intro i hi
            calc
              ∑ j ∈ s, α i * α j * ⟪x i, u i⟫_ℝ
                  = α i * ∑ j ∈ s, α j * ⟪x i, u i⟫_ℝ := by
                      simpa [mul_assoc] using
                        (Finset.mul_sum s (fun j ↦ α j * ⟪x i, u i⟫_ℝ) (α i)).symm
              _ = α i * ((∑ j ∈ s, α j) * ⟪x i, u i⟫_ℝ) := by rw [Finset.sum_mul]
              _ = α i * ⟪x i, u i⟫_ℝ := by rw [hα, one_mul]
          · rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro j hj
            calc
              ∑ i ∈ s, α i * α j * ⟪x j, u j⟫_ℝ
                  = (∑ i ∈ s, α i) * (α j * ⟪x j, u j⟫_ℝ) := by
                      simpa [mul_assoc] using
                        (Finset.sum_mul s (fun i ↦ α i) (α j * ⟪x j, u j⟫_ℝ)).symm
              _ = α j * ⟪x j, u j⟫_ℝ := by rw [hα, one_mul]
    _ = 2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ := by ring

/-- Helper for Proposition 4.8: the weighted affine inner product splits into the weighted diagonal
sum minus the half pairwise correction term. -/
-- Proof step: expand the doubled affine-combination inner product, rewrite the exchanged terms by
-- the previous helper, and use the weight sum `1` to collapse the diagonal double sum.
private theorem weighted_affine_inner_eq_sum_inner_add_half_pairwise
    (s : Finset ι) (x u : ι → H) (α : ι → ℝ) (hα : ∑ i ∈ s, α i = 1) :
    ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ +
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i - x j, u i - u j⟫_ℝ =
      ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ := by
  have h_two :
      2 * ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ +
          ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i - x j, u i - u j⟫_ℝ =
        2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ := by
    calc
      2 * ⟪∑ i ∈ s, α i • x i, ∑ j ∈ s, α j • u j⟫_ℝ +
          ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i - x j, u i - u j⟫_ℝ
          = (∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ)) +
              ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪x i - x j, u i - u j⟫_ℝ := by
              rw [two_mul_weighted_inner_eq_sum_exchange]
      _ = ∑ i ∈ s, ∑ j ∈ s, α i * α j *
            ((⟪x i, u j⟫_ℝ + ⟪x j, u i⟫_ℝ) + ⟪x i - x j, u i - u j⟫_ℝ) := by
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [← Finset.sum_add_distrib]
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
      _ = ∑ i ∈ s, ∑ j ∈ s, α i * α j * (⟪x i, u i⟫_ℝ + ⟪x j, u j⟫_ℝ) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              refine Finset.sum_congr rfl ?_
              intro j hj
              rw [pairwise_inner_exchange_eq_diag_sub_pairwise]
              ring
      _ = 2 * ∑ i ∈ s, α i * ⟪x i, u i⟫_ℝ :=
            weighted_double_sum_diag_eq_two_mul s x u α hα
  -- Divide the doubled identity by `2` to recover the stated weighted decomposition.
  linarith

/-- Helper for Proposition 4.8: a weighted sum of centered vectors can be rewritten as the weighted
sum minus the center when the coefficients add up to `1`. -/
-- Proof step: distribute the scalar through subtraction and collapse the constant weighted sum with
-- the hypothesis `∑ αᵢ = 1`.
private lemma weighted_sub_eq_sub_of_sum_eq_one
    (s : Finset ι) (α : ι → ℝ) (f : ι → H) (c : H)
    (hα : ∑ i ∈ s, α i = 1) :
    ∑ i ∈ s, α i • (f i - c) = (∑ i ∈ s, α i • f i) - c := by
  calc
    ∑ i ∈ s, α i • (f i - c) = ∑ i ∈ s, (α i • f i - α i • c) := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [smul_sub]
    _ = (∑ i ∈ s, α i • f i) - ∑ i ∈ s, α i • c := by
      rw [Finset.sum_sub_distrib]
    _ = (∑ i ∈ s, α i • f i) - (∑ i ∈ s, α i) • c := by
      rw [← Finset.sum_smul]
    _ = (∑ i ∈ s, α i • f i) - c := by
      rw [hα, one_smul]

/-- Helper for Proposition 4.8: firm nonexpansiveness makes the residual cross term nonnegative. -/
-- Proof step: rewrite the residual difference as `(x - y) - (T x - T y)` and subtract the firm
-- inequality from the resulting inner product expansion.
private lemma firmly_nonexpansiveOn_residual_inner_nonneg
    {T : H → H} {D : Set H} (hT : FirmlyNonexpansiveOn D (fun z : D ↦ T z))
    {x y : H} (hx : x ∈ D) (hy : y ∈ D) :
    0 ≤ ⟪T x - T y, (x - T x) - (y - T y)⟫_ℝ := by
  have hfirm : ‖T x - T y‖ ^ (2 : ℕ) ≤ ⟪T x - T y, x - y⟫_ℝ :=
    by
      simpa [real_inner_comm] using hT ⟨x, hx⟩ ⟨y, hy⟩
  have hres :
      (x - T x) - (y - T y) = (x - y) - (T x - T y) := by
    abel_nf
  -- After expanding the residual term, the target is exactly the firm defect.
  rw [hres, inner_sub_right, real_inner_self_eq_norm_sq]
  linarith

/-- Helper for Proposition 4.8: the inner product of the average and half-difference of `a` and
`b` is one quarter of the corresponding squared-norm gap. -/
-- Proof step: expand `⟪a + b, a - b⟫_ℝ` and observe that the mixed terms cancel by symmetry of the
-- real inner product.
private lemma average_pairing_eq_quarter_norm_gap (a b : H) :
    ⟪(1 / 2 : ℝ) • (a + b), (1 / 2 : ℝ) • (a - b)⟫_ℝ =
      (1 / 4 : ℝ) * (‖a‖ ^ (2 : ℕ) - ‖b‖ ^ (2 : ℕ)) := by
  have h_expand : ⟪a + b, a - b⟫_ℝ = ‖a‖ ^ (2 : ℕ) - ‖b‖ ^ (2 : ℕ) := by
    rw [inner_sub_right, inner_add_left, inner_add_left, real_inner_self_eq_norm_sq,
      real_inner_self_eq_norm_sq, real_inner_comm b a]
    ring
  -- Scaling both arguments by `1/2` contributes the expected quarter factor.
  rw [real_inner_smul_left, real_inner_smul_right, h_expand]
  ring

/-- Helper for Proposition 4.8: scaling a vector by `1/2` scales its squared norm by `1/4`. -/
-- Proof step: rewrite the norm of a scalar multiple and simplify the resulting real identity.
private lemma half_smul_norm_sq (a : H) :
    ‖(1 / 2 : ℝ) • a‖ ^ (2 : ℕ) = (1 / 4 : ℝ) * ‖a‖ ^ (2 : ℕ) := by
  rw [norm_smul, Real.norm_of_nonneg (by norm_num)]
  nlinarith [norm_nonneg a]

/-- Proposition 4.8 (1): Zarantonello's weighted identity for the family
`i ↦ (T (x i), x i - T (x i))` at the affine combination `y = ∑ i ∈ s, α i • x i`. -/
-- Proof sketch: apply Lemma 2.14 to the families `i ↦ T (x i) - T y` and
-- `i ↦ (x i - T (x i)) - (y - T y)`, then use `hy` and `hα_sum` to rewrite the barycenters.
theorem zarantonello_weighted_firm_identity
    (s : Finset ι) (T : H → H) (x : ι → H) (α : ι → ℝ) (y : H)
    (hy : y = ∑ i ∈ s, α i • x i) (hα_sum : ∑ i ∈ s, α i = 1) :
    ‖T y - ∑ i ∈ s, α i • T (x i)‖ ^ (2 : ℕ) +
      ∑ i ∈ s, α i * ⟪T y - T (x i), (y - T y) - (x i - T (x i))⟫_ℝ =
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
        α i * α j * ⟪T (x i) - T (x j), (x i - T (x i)) - (x j - T (x j))⟫_ℝ := by
  let u : ι → H := fun i ↦ T (x i) - T y
  let v : ι → H := fun i ↦ (x i - T (x i)) - (y - T y)
  have hcore :
      ⟪∑ i ∈ s, α i • u i, ∑ j ∈ s, α j • v j⟫_ℝ +
          (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪u i - u j, v i - v j⟫_ℝ =
        ∑ i ∈ s, α i * ⟪u i, v i⟫_ℝ :=
    weighted_affine_inner_eq_sum_inner_add_half_pairwise s u v α hα_sum
  have hu_sum :
      ∑ i ∈ s, α i • u i = (∑ i ∈ s, α i • T (x i)) - T y := by
    -- Rewrite the centered image family using the weight sum `1`.
    simpa [u] using weighted_sub_eq_sub_of_sum_eq_one s α (fun i ↦ T (x i)) (T y) hα_sum
  have hv_sum :
      ∑ i ∈ s, α i • v i = T y - ∑ i ∈ s, α i • T (x i) := by
    -- Rewrite the centered residual family and then use the barycenter identity for `y`.
    calc
      ∑ i ∈ s, α i • v i
          = (∑ i ∈ s, α i • (x i - T (x i))) - (y - T y) := by
              simpa [v] using
                weighted_sub_eq_sub_of_sum_eq_one s α
                  (fun i ↦ x i - T (x i)) (y - T y) hα_sum
      _ = ((∑ i ∈ s, α i • x i) - ∑ i ∈ s, α i • T (x i)) - (y - T y) := by
            have hsplit :
                ∑ i ∈ s, α i • (x i - T (x i)) =
                  (∑ i ∈ s, α i • x i) - ∑ i ∈ s, α i • T (x i) := by
              calc
                ∑ i ∈ s, α i • (x i - T (x i))
                    = ∑ i ∈ s, (α i • x i - α i • T (x i)) := by
                        refine Finset.sum_congr rfl ?_
                        intro i hi
                        rw [smul_sub]
                _ = (∑ i ∈ s, α i • x i) - ∑ i ∈ s, α i • T (x i) := by
                      rw [Finset.sum_sub_distrib]
            rw [hsplit]
      _ = T y - ∑ i ∈ s, α i • T (x i) := by
            rw [hy]
            abel_nf
  have hpairwise :
      ∑ i ∈ s, ∑ j ∈ s, α i * α j * ⟪u i - u j, v i - v j⟫_ℝ =
        ∑ i ∈ s, ∑ j ∈ s,
          α i * α j * ⟪T (x i) - T (x j), (x i - T (x i)) - (x j - T (x j))⟫_ℝ := by
    -- The pairwise differences lose the centered basepoint `y`.
    refine Finset.sum_congr rfl ?_
    intro i hi
    refine Finset.sum_congr rfl ?_
    intro j hj
    have huij : u i - u j = T (x i) - T (x j) := by
      dsimp [u]
      abel_nf
    have hvij : v i - v j = (x i - T (x i)) - (x j - T (x j)) := by
      dsimp [v]
      abel_nf
    rw [huij, hvij]
  have hdiag :
      ∑ i ∈ s, α i * ⟪u i, v i⟫_ℝ =
        ∑ i ∈ s, α i * ⟪T y - T (x i), (y - T y) - (x i - T (x i))⟫_ℝ := by
    -- Each diagonal term is unchanged because both arguments are simultaneously negated.
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hinner :
        ⟪u i, v i⟫_ℝ = ⟪T y - T (x i), (y - T y) - (x i - T (x i))⟫_ℝ := by
      dsimp [u, v]
      have hterm : T (x i) - T y = -(T y - T (x i)) := by
        abel_nf
      have hres : (x i - T (x i)) - (y - T y) = -((y - T y) - (x i - T (x i))) := by
        abel_nf
      rw [hterm, hres, inner_neg_left, inner_neg_right]
      ring
    rw [hinner]
  rw [hu_sum, hv_sum, hpairwise, hdiag] at hcore
  have hinner :
      ⟪(∑ i ∈ s, α i • T (x i)) - T y, T y - ∑ i ∈ s, α i • T (x i)⟫_ℝ =
        -‖T y - ∑ i ∈ s, α i • T (x i)‖ ^ (2 : ℕ) := by
    have hneg :
        T y - ∑ i ∈ s, α i • T (x i) =
          -((∑ i ∈ s, α i • T (x i)) - T y) := by
      abel_nf
    -- The two centered barycenters are negatives of one another.
    rw [hneg, inner_neg_right, real_inner_self_eq_norm_sq, norm_neg, norm_sub_rev]
  rw [hinner] at hcore
  -- Move the negative squared norm to the other side to obtain the displayed identity.
  linarith

/-- Proposition 4.8 (2): if `T` is firmly nonexpansive on a convex set containing the weighted
family and the barycenter `y` of nonnegative weights summing to `1`, in the canonical
restricted-map sense, then
Zarantonello's identity yields the stated upper bound. -/
-- Proof sketch: use `Convex.sum_mem` and the nonnegativity of the weights to place the barycenter in
-- `D`, apply part (1), and estimate the correction term by firm nonexpansiveness.
theorem zarantonello_weighted_firm_inequality
    (s : Finset ι) (D : Set H) (hD : Convex ℝ D) (T : H → H) (x : ι → H) (α : ι → ℝ) (y : H)
    (hy : y = ∑ i ∈ s, α i • x i) (hα_nonneg : ∀ i ∈ s, 0 ≤ α i)
    (hα_sum : ∑ i ∈ s, α i = 1) (hx : ∀ i ∈ s, x i ∈ D)
    (hT : FirmlyNonexpansiveOn D (fun z : D ↦ T z)) :
    ‖T y - ∑ i ∈ s, α i • T (x i)‖ ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
        α i * α j * ⟪T (x i) - T (x j), (x i - T (x i)) - (x j - T (x j))⟫_ℝ := by
  have hy_mem : y ∈ D := by
    -- Nonnegative coefficients summing to `1` keep the barycenter inside the convex set.
    rw [hy]
    exact hD.sum_mem hα_nonneg hα_sum hx
  have hcorrection_nonneg :
      0 ≤ ∑ i ∈ s, α i * ⟪T y - T (x i), (y - T y) - (x i - T (x i))⟫_ℝ := by
    -- Each correction term is nonnegative by firm nonexpansiveness, and each weight is nonnegative.
    refine Finset.sum_nonneg ?_
    intro i hi
    exact mul_nonneg (hα_nonneg i hi)
      (firmly_nonexpansiveOn_residual_inner_nonneg hT hy_mem (hx i hi))
  have hidentity :=
    zarantonello_weighted_firm_identity s T x α y hy hα_sum
  -- Drop the nonnegative correction sum from the exact identity.
  linarith

/-- Proposition 4.8 (3): the weighted identity from part (1) can be rewritten as a difference of
squared norms for `T` and the identity map. -/
-- Proof sketch: apply part (1) to the averaged map `fun z ↦ (z + T z) / 2` and simplify the
-- resulting inner products into differences of squared norms.
theorem zarantonello_weighted_nonexpansive_identity
    (s : Finset ι) (T : H → H) (x : ι → H) (α : ι → ℝ) (y : H)
    (hy : y = ∑ i ∈ s, α i • x i) (hα_sum : ∑ i ∈ s, α i = 1) :
    ‖T y - ∑ i ∈ s, α i • T (x i)‖ ^ (2 : ℕ) +
      ∑ i ∈ s, α i * (‖y - x i‖ ^ (2 : ℕ) - ‖T y - T (x i)‖ ^ (2 : ℕ)) =
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
        α i * α j * (‖x i - x j‖ ^ (2 : ℕ) - ‖T (x i) - T (x j)‖ ^ (2 : ℕ)) := by
  let S : H → H := fun z ↦ (1 / 2 : ℝ) • z + (1 / 2 : ℝ) • T z
  have hidentity := zarantonello_weighted_firm_identity s S x α y hy hα_sum
  have hsumS :
      ∑ i ∈ s, α i • S (x i) =
        (1 / 2 : ℝ) • (∑ i ∈ s, α i • x i) + (1 / 2 : ℝ) • (∑ i ∈ s, α i • T (x i)) := by
    -- Expand the weighted average map into the two weighted component sums.
    calc
      ∑ i ∈ s, α i • S (x i)
          = ∑ i ∈ s, ((1 / 2 : ℝ) • (α i • x i) + (1 / 2 : ℝ) • (α i • T (x i))) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              dsimp [S]
              rw [smul_add]
              simp [smul_smul, mul_comm]
      _ = (∑ i ∈ s, (1 / 2 : ℝ) • (α i • x i)) +
            ∑ i ∈ s, (1 / 2 : ℝ) • (α i • T (x i)) := by
              rw [Finset.sum_add_distrib]
      _ = (1 / 2 : ℝ) • (∑ i ∈ s, α i • x i) + (1 / 2 : ℝ) • (∑ i ∈ s, α i • T (x i)) := by
              rw [← Finset.smul_sum, ← Finset.smul_sum]
  have hleft :
      S y - ∑ i ∈ s, α i • S (x i) =
        (1 / 2 : ℝ) • (T y - ∑ i ∈ s, α i • T (x i)) := by
    -- The `x`-part cancels because `y` is the weighted barycenter.
    rw [hsumS, hy]
    dsimp [S]
    rw [← smul_add, ← smul_add, ← smul_sub]
    congr 1
    abel_nf
  have hnorm :
      ‖S y - ∑ i ∈ s, α i • S (x i)‖ ^ (2 : ℕ) =
        (1 / 4 : ℝ) * ‖T y - ∑ i ∈ s, α i • T (x i)‖ ^ (2 : ℕ) := by
    rw [hleft, half_smul_norm_sq]
  have hcorrection :
      ∑ i ∈ s, α i * ⟪S y - S (x i), (y - S y) - (x i - S (x i))⟫_ℝ =
        (1 / 4 : ℝ) * ∑ i ∈ s,
          α i * (‖y - x i‖ ^ (2 : ℕ) - ‖T y - T (x i)‖ ^ (2 : ℕ)) := by
    -- Each correction term for `S` is one quarter of the corresponding norm gap.
    have hresidual (z : H) : z - S z = (1 / 2 : ℝ) • (z - T z) := by
      dsimp [S]
      nth_rewrite 1 [show z = (1 : ℝ) • z by rw [one_smul]]
      have hone : (1 : ℝ) = (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
        norm_num
      rw [hone, add_smul]
      norm_num
      simpa [sub_eq_add_neg] using (smul_sub (1 / 2 : ℝ) z (T z)).symm
    calc
      ∑ i ∈ s, α i * ⟪S y - S (x i), (y - S y) - (x i - S (x i))⟫_ℝ
          = ∑ i ∈ s,
              α i * ((1 / 4 : ℝ) *
                (‖y - x i‖ ^ (2 : ℕ) - ‖T y - T (x i)‖ ^ (2 : ℕ))) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  have havg :
                      S y - S (x i) =
                        (1 / 2 : ℝ) • ((y - x i) + (T y - T (x i))) := by
                    dsimp [S]
                    rw [← smul_add, ← smul_add, ← smul_sub]
                    congr 1
                    abel_nf
                  have hres :
                      (y - S y) - (x i - S (x i)) =
                        (1 / 2 : ℝ) • ((y - x i) - (T y - T (x i))) := by
                    rw [hresidual, hresidual, ← smul_sub]
                    congr 1
                    abel_nf
                  rw [havg, hres, average_pairing_eq_quarter_norm_gap]
      _ = (1 / 4 : ℝ) * ∑ i ∈ s,
            α i * (‖y - x i‖ ^ (2 : ℕ) - ‖T y - T (x i)‖ ^ (2 : ℕ)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
  have hpairwise_sum :
      ∑ i ∈ s, ∑ j ∈ s,
          α i * α j * ⟪S (x i) - S (x j), (x i - S (x i)) - (x j - S (x j))⟫_ℝ =
        (1 / 4 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
          α i * α j * (‖x i - x j‖ ^ (2 : ℕ) - ‖T (x i) - T (x j)‖ ^ (2 : ℕ)) := by
    have hresidual (z : H) : z - S z = (1 / 2 : ℝ) • (z - T z) := by
      dsimp [S]
      nth_rewrite 1 [show z = (1 : ℝ) • z by rw [one_smul]]
      have hone : (1 : ℝ) = (1 / 2 : ℝ) + (1 / 2 : ℝ) := by
        norm_num
      rw [hone, add_smul]
      norm_num
      simpa [sub_eq_add_neg] using (smul_sub (1 / 2 : ℝ) z (T z)).symm
    calc
      ∑ i ∈ s, ∑ j ∈ s,
          α i * α j * ⟪S (x i) - S (x j), (x i - S (x i)) - (x j - S (x j))⟫_ℝ
          = ∑ i ∈ s, ∑ j ∈ s,
              α i * α j * ((1 / 4 : ℝ) *
                (‖x i - x j‖ ^ (2 : ℕ) - ‖T (x i) - T (x j)‖ ^ (2 : ℕ))) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  have havg :
                      S (x i) - S (x j) =
                        (1 / 2 : ℝ) • ((x i - x j) + (T (x i) - T (x j))) := by
                    dsimp [S]
                    rw [← smul_add, ← smul_add, ← smul_sub]
                    congr 1
                    abel_nf
                  have hres :
                      (x i - S (x i)) - (x j - S (x j)) =
                        (1 / 2 : ℝ) • ((x i - x j) - (T (x i) - T (x j))) := by
                    rw [hresidual, hresidual, ← smul_sub]
                    congr 1
                    abel_nf
                  rw [havg, hres, average_pairing_eq_quarter_norm_gap]
      _ = (1 / 4 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
            α i * α j * (‖x i - x j‖ ^ (2 : ℕ) - ‖T (x i) - T (x j)‖ ^ (2 : ℕ)) := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl ?_
              intro j hj
              ring
  have hpairwise :
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
          α i * α j * ⟪S (x i) - S (x j), (x i - S (x i)) - (x j - S (x j))⟫_ℝ =
        (1 / 8 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
          α i * α j * (‖x i - x j‖ ^ (2 : ℕ) - ‖T (x i) - T (x j)‖ ^ (2 : ℕ)) := by
    -- Combine the quarter factor from the pairwise rewrite with the outer prefactor `1/2`.
    rw [hpairwise_sum]
    ring
  rw [hnorm, hcorrection, hpairwise] at hidentity
  -- Clearing the quarter factor recovers the announced norm-difference identity.
  linarith

/-- Proposition 4.8 (4): if `T` is nonexpansive on a convex set containing the weighted family and
the barycenter `y` of nonnegative weights summing to `1`, then part (3) yields the corresponding
upper bound. -/
-- Proof sketch: use `Convex.sum_mem` to place the barycenter in `D`, apply part
-- (3), and estimate each squared-norm difference by the nonexpansive bound.
theorem zarantonello_weighted_nonexpansive_inequality
    (s : Finset ι) (D : Set H) (hD : Convex ℝ D) (T : H → H) (x : ι → H) (α : ι → ℝ) (y : H)
    (hy : y = ∑ i ∈ s, α i • x i) (hα_nonneg : ∀ i ∈ s, 0 ≤ α i)
    (hα_sum : ∑ i ∈ s, α i = 1) (hx : ∀ i ∈ s, x i ∈ D) (hT : LipschitzOnWith 1 T D) :
    ‖T y - ∑ i ∈ s, α i • T (x i)‖ ^ (2 : ℕ) ≤
      (1 / 2 : ℝ) * ∑ i ∈ s, ∑ j ∈ s,
        α i * α j * (‖x i - x j‖ ^ (2 : ℕ) - ‖T (x i) - T (x j)‖ ^ (2 : ℕ)) := by
  have hy_mem : y ∈ D := by
    -- Nonnegative coefficients summing to `1` keep the barycenter inside the convex set.
    rw [hy]
    exact hD.sum_mem hα_nonneg hα_sum hx
  have hcorrection_nonneg :
      0 ≤ ∑ i ∈ s, α i * (‖y - x i‖ ^ (2 : ℕ) - ‖T y - T (x i)‖ ^ (2 : ℕ)) := by
    -- Each gap is nonnegative because `T` is `1`-Lipschitz on `D`.
    refine Finset.sum_nonneg ?_
    intro i hi
    have hdist' : dist (T y) (T (x i)) ≤ dist y (x i) := by
      simpa [edist_dist] using hT hy_mem (hx i hi)
    have hdist : ‖T y - T (x i)‖ ≤ ‖y - x i‖ := by
      simpa [dist_eq_norm] using hdist'
    have hsq :
        ‖T y - T (x i)‖ ^ (2 : ℕ) ≤ ‖y - x i‖ ^ (2 : ℕ) :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hdist
    have hgap : 0 ≤ ‖y - x i‖ ^ (2 : ℕ) - ‖T y - T (x i)‖ ^ (2 : ℕ) := by
      linarith
    exact mul_nonneg (hα_nonneg i hi) hgap
  have hidentity :=
    zarantonello_weighted_nonexpansive_identity s T x α y hy hα_sum
  -- Drop the nonnegative correction sum from the exact norm-gap identity.
  linarith

/-! Source item: Chap04/Corollary_4_5 -/


variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: use the polarization identity
-- `‖(2 • T - id) u‖ ^ 2 = ‖u‖ ^ 2 + 4 * ‖T u‖ ^ 2 - 4 * ⟪u, T u⟫_ℝ` to identify clauses
-- (i), (ii), and (iii); transfer (ii) across adjoints using `‖T.adjoint‖ = ‖T‖`; and rewrite
-- clause (iii) as positivity of `T + T.adjoint - 2 • T.adjoint.comp T`.
/- Firm nonexpansiveness of a bounded linear operator is equivalent to the quadratic inequality
obtained by specializing at `y = 0`. -/
private lemma firmly_nonexpansive_iff_quadratic_at_zero (T : H →L[ℝ] H) :
    FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T x) ↔
      ∀ x : H, ‖T x‖ ^ (2 : ℕ) ≤ ⟪x, T x⟫_ℝ := by
  rw [firmlyNonexpansiveOn_univ_iff_norm_sq_le_inner]
  constructor
  · intro hT x
    -- Specializing the defining inequality at `y = 0` produces the quadratic bound.
    simpa [real_inner_comm] using hT x 0
  · intro hT x y
    -- Applying the quadratic bound to `x - y` recovers the difference inequality.
    simpa [map_sub, real_inner_comm] using hT (x - y)

/- The reflector norm bound `‖2T - Id‖ ≤ 1` is equivalent to the quadratic inequality from
clause (iii). -/
private lemma reflector_norm_le_iff_quadratic (T : H →L[ℝ] H) :
    ‖(2 : ℝ) • T - 1‖ ≤ 1 ↔ ∀ x : H, ‖T x‖ ^ (2 : ℕ) ≤ ⟪x, T x⟫_ℝ := by
  constructor
  · intro hnorm x
    -- Convert the operator norm bound to the pointwise reflector contraction.
    have hpointwise :
        ‖((2 : ℝ) • T - 1) x‖ ≤ ‖x‖ := by
      simpa using (ContinuousLinearMap.opNorm_le_iff (show 0 ≤ (1 : ℝ) by positivity)).mp hnorm x
    have hsq :
        ‖((2 : ℝ) • T - 1) x‖ ^ (2 : ℕ) ≤ ‖x‖ ^ (2 : ℕ) :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hpointwise
    have hreflect :
        ‖x‖ ^ (2 : ℕ) - ‖((2 : ℝ) • T - 1) x‖ ^ (2 : ℕ) =
          4 * (⟪x, T x⟫_ℝ - ‖T x‖ ^ (2 : ℕ)) := by
      -- Rewrite the reflector norm with Lemma 2.17 in the form used in the textbook proof.
      simpa using norm_sq_sub_norm_sq_reflection_eq_four_mul x (T x)
    nlinarith
  · intro hquad
    -- Conversely, turn the quadratic inequality back into a pointwise reflector contraction.
    rw [ContinuousLinearMap.opNorm_le_iff (show 0 ≤ (1 : ℝ) by positivity)]
    intro x
    have hreflect :
        ‖x‖ ^ (2 : ℕ) - ‖((2 : ℝ) • T - 1) x‖ ^ (2 : ℕ) =
          4 * (⟪x, T x⟫_ℝ - ‖T x‖ ^ (2 : ℕ)) := by
      simpa using norm_sq_sub_norm_sq_reflection_eq_four_mul x (T x)
    have hsq :
        ‖((2 : ℝ) • T - 1) x‖ ^ (2 : ℕ) ≤ ‖x‖ ^ (2 : ℕ) := by
      nlinarith [hquad x, hreflect]
    simpa using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq

variable [CompleteSpace H]

/- The reflector norm bound is invariant under taking adjoints. -/
private lemma adjoint_reflector_norm_le_iff (T : H →L[ℝ] H) :
    ‖(2 : ℝ) • T - 1‖ ≤ 1 ↔ ‖(2 : ℝ) • T.adjoint - 1‖ ≤ 1 := by
  have hid : (1 : H →L[ℝ] H).adjoint = 1 := by
    ext x
    refine ext_inner_right ℝ (fun y ↦ ?_)
    simp [ContinuousLinearMap.adjoint_inner_left]
  have hadj : ((2 : ℝ) • T - 1).adjoint = (2 : ℝ) • T.adjoint - 1 := by
    ext x
    refine ext_inner_right ℝ (fun y ↦ ?_)
    -- The adjoint commutes with the affine reflector construction.
    simp [hid]
  have hnorm :
      ‖(2 : ℝ) • T.adjoint - 1‖ = ‖(2 : ℝ) • T - 1‖ := by
    calc
      ‖(2 : ℝ) • T.adjoint - 1‖ = ‖((2 : ℝ) • T - 1).adjoint‖ := by rw [hadj]
      _ = ‖(2 : ℝ) • T - 1‖ := ContinuousLinearMap.adjoint.norm_map _
  rw [hnorm]

/- Positivity of `T + T† - 2 T†T` is equivalent to the same quadratic inequality as clause (iii). -/
private lemma positive_operator_iff_quadratic (T : H →L[ℝ] H) :
    (T + T.adjoint - (2 : ℝ) • (T.adjoint.comp T)).IsPositive ↔
      ∀ x : H, ‖T x‖ ^ (2 : ℕ) ≤ ⟪x, T x⟫_ℝ := by
  let A : H →L[ℝ] H := T + T.adjoint - (2 : ℝ) • (T.adjoint.comp T)
  have hcomp_symm :
      ∀ x y : H, ⟪(T.adjoint.comp T) x, y⟫_ℝ = ⟪x, (T.adjoint.comp T) y⟫_ℝ := by
    intro x y
    calc
      ⟪(T.adjoint.comp T) x, y⟫_ℝ = ⟪T x, T y⟫_ℝ := by
        simpa [ContinuousLinearMap.comp_apply] using
          (ContinuousLinearMap.adjoint_inner_left T y (T x))
      _ = ⟪x, (T.adjoint.comp T) y⟫_ℝ := by
        simpa [ContinuousLinearMap.comp_apply] using
          (ContinuousLinearMap.adjoint_inner_right T x (T y)).symm
  have hA_symm : A.IsSymmetric := by
    intro x y
    -- Expanding both sides shows that the adjoint terms pair up symmetrically.
    calc
      ⟪A x, y⟫_ℝ
          = ⟪T x, y⟫_ℝ + ⟪T.adjoint x, y⟫_ℝ - 2 * ⟪(T.adjoint.comp T) x, y⟫_ℝ := by
              simp [A, inner_add_left, inner_sub_left, real_inner_smul_left]
      _ = ⟪x, T.adjoint y⟫_ℝ + ⟪x, T y⟫_ℝ - 2 * ⟪x, (T.adjoint.comp T) y⟫_ℝ := by
            rw [ContinuousLinearMap.adjoint_inner_right, ContinuousLinearMap.adjoint_inner_left,
              hcomp_symm x y]
      _ = ⟪x, A y⟫_ℝ := by
            simp [A, inner_add_right, inner_sub_right, real_inner_smul_right]
            ring
  have hA_apply :
      ∀ x : H, ⟪A x, x⟫_ℝ = 2 * (⟪x, T x⟫_ℝ - ‖T x‖ ^ (2 : ℕ)) := by
    intro x
    have hcomp :
        ⟪(T.adjoint.comp T) x, x⟫_ℝ = ‖T x‖ ^ (2 : ℕ) := by
      calc
        ⟪(T.adjoint.comp T) x, x⟫_ℝ = ⟪T x, T x⟫_ℝ := by
          simpa [ContinuousLinearMap.comp_apply] using
            (ContinuousLinearMap.adjoint_inner_left T x (T x))
        _ = ‖T x‖ ^ (2 : ℕ) := real_inner_self_eq_norm_sq _
    -- This is the quadratic-form computation behind clause (v).
    calc
      ⟪A x, x⟫_ℝ
          = ⟪T x, x⟫_ℝ + ⟪T.adjoint x, x⟫_ℝ - 2 * ⟪(T.adjoint.comp T) x, x⟫_ℝ := by
              simp [A, inner_add_left, inner_sub_left, real_inner_smul_left]
      _ = ⟪x, T x⟫_ℝ + ⟪x, T x⟫_ℝ - 2 * ‖T x‖ ^ (2 : ℕ) := by
            rw [real_inner_comm, ContinuousLinearMap.adjoint_inner_left, hcomp]
      _ = 2 * (⟪x, T x⟫_ℝ - ‖T x‖ ^ (2 : ℕ)) := by ring
  constructor
  · intro hpos x
    rcases (ContinuousLinearMap.isPositive_iff A).mp hpos with ⟨_, hnonneg⟩
    -- Positivity of `A` is exactly nonnegativity of the same quadratic form.
    have hnonnegx : 0 ≤ ⟪A x, x⟫_ℝ := hnonneg x
    rw [hA_apply x] at hnonnegx
    nlinarith
  · intro hquad
    -- The quadratic inequality supplies the nonnegativity half of positivity.
    refine (ContinuousLinearMap.isPositive_iff A).mpr ?_
    refine ⟨hA_symm, ?_⟩
    intro x
    rw [hA_apply x]
    nlinarith [hquad x]

/-- For a bounded linear operator on a real Hilbert space, firm nonexpansiveness, the norm
bound `‖2T - Id‖ ≤ 1`, the pointwise inequality `‖T x‖² ≤ ⟪x, T x⟫`, firm nonexpansiveness of
the adjoint, and positivity of `T + T† - 2 T†T` are equivalent. -/
theorem tfae_firmly_nonexpansive_adjoint_norm_quadratic (T : H →L[ℝ] H) :
    List.TFAE
      [ FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T x),
        ‖(2 : ℝ) • T - 1‖ ≤ 1,
        ∀ x : H, ‖T x‖ ^ (2 : ℕ) ≤ ⟪x, T x⟫_ℝ,
        FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T.adjoint x),
        (T + T.adjoint - (2 : ℝ) • (T.adjoint.comp T)).IsPositive ] := by
  -- Follow the textbook implication graph by using the quadratic inequality as the common bridge.
  tfae_have 1 ↔ 3 := firmly_nonexpansive_iff_quadratic_at_zero T
  tfae_have 2 ↔ 3 := reflector_norm_le_iff_quadratic T
  tfae_have 2 ↔ 4 := by
    -- Transfer the reflector characterization across adjoints, then reuse the previous bridges.
    calc
      ‖(2 : ℝ) • T - 1‖ ≤ 1 ↔ ‖(2 : ℝ) • T.adjoint - 1‖ ≤ 1 :=
        adjoint_reflector_norm_le_iff T
      _ ↔ FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T.adjoint x) :=
        (reflector_norm_le_iff_quadratic T.adjoint).trans
          (firmly_nonexpansive_iff_quadratic_at_zero T.adjoint).symm
  tfae_have 3 ↔ 5 := (positive_operator_iff_quadratic T).symm
  tfae_finish

/-! Source item: Chap04/Definition_4_10 -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Definition 4.10: a map `T : D → H` on a real Hilbert space is `β`-cocoercive, or
`β`-inverse strongly monotone, when `β > 0` and
`⟪x - y, T x - T y⟫ ≥ β ‖T x - T y‖²` for all `x, y ∈ D`. -/
def CocoerciveOn (β : ℝ) (D : Set H) (T : D → H) : Prop :=
  0 < β ∧
    ∀ x y : D, β * ‖T x - T y‖ ^ 2 ≤ inner ℝ ((x : H) - y) (T x - T y)

/-- A `β`-cocoercive map has positive cocoercivity parameter. -/
theorem CocoerciveOn.pos {β : ℝ} {D : Set H} {T : D → H} (hT : CocoerciveOn β D T) :
    0 < β :=
  hT.1

/-- A `β`-cocoercive map satisfies the textbook lower bound
`β ‖T x - T y‖² ≤ ⟪x - y, T x - T y⟫` at every pair of points in its domain. -/
theorem CocoerciveOn.ineq {β : ℝ} {D : Set H} {T : D → H} (hT : CocoerciveOn β D T)
    (x y : D) :
    β * ‖T x - T y‖ ^ 2 ≤ inner ℝ ((x : H) - y) (T x - T y) :=
  hT.2 x y

/-- Cocoercivity on the full space, in the pointwise form used by the dynamics
literature: `β ‖A y - A x‖² ≤ ⟪A y - A x, y - x⟫` for all `x, y`. -/
theorem CocoerciveOn.pointwise_iff {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → H) (theta : ℝ) (htheta : 0 < theta) :
    CocoerciveOn theta Set.univ (fun x : Set.univ => A x) ↔
      ∀ x y : H, theta * ‖A y - A x‖ ^ 2 ≤ @inner ℝ H _ (A y - A x) (y - x) := by
  rw [CocoerciveOn]
  constructor
  · rintro ⟨_, hC⟩ x y
    have hxy := hC ⟨y, Set.mem_univ y⟩ ⟨x, Set.mem_univ x⟩
    simpa only [real_inner_comm] using hxy
  · intro hPaper
    refine ⟨htheta, ?_⟩
    intro u v
    have huv := hPaper (v : H) (u : H)
    simpa only [real_inner_comm] using huv

/-! Source item: Chap04/Proposition_4_11 -/

variable {H : Type u} [NormedAddCommGroup H]

/-- On a subtype domain, `LipschitzWith 1` is exactly the pairwise nonexpansive norm inequality. -/
private lemma lipschitzWith_one_iff_pairwise_norm_sub_le {D : Set H} {T : D → H} :
    LipschitzWith 1 T ↔ ∀ x y : D, ‖T x - T y‖ ≤ ‖(x : H) - y‖ := by
  constructor
  · intro hT x y
    simpa [Subtype.dist_eq, dist_eq_norm] using hT.dist_le_mul x y
  · intro hT
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa [Subtype.dist_eq, dist_eq_norm] using hT x y

/-- Comparing squared norms is equivalent to comparing norms. -/
private lemma norm_sq_le_norm_sq_iff {a b : H} : ‖a‖ ^ 2 ≤ ‖b‖ ^ 2 ↔ ‖a‖ ≤ ‖b‖ := by
  constructor
  · intro h
    have h' := sq_le_sq.mp h
    simpa [abs_of_nonneg (norm_nonneg a), abs_of_nonneg (norm_nonneg b)] using h'
  · intro h
    exact sq_le_sq.mpr <| by
      simpa [abs_of_nonneg (norm_nonneg a), abs_of_nonneg (norm_nonneg b)] using h

section

variable [InnerProductSpace ℝ H]

/-- The residual `1 / 2`-cocoercivity inequality is equivalent to the squared nonexpansive
estimate after expanding the quadratic terms. -/
private lemma residual_quadratic_expansion {D : Set H} (T : D → H) (x y : D) :
    ((1 / 2 : ℝ) * ‖residualMap D T x - residualMap D T y‖ ^ 2 ≤
        inner ℝ ((x : H) - y) (residualMap D T x - residualMap D T y)) ↔
      ‖T x - T y‖ ^ 2 ≤ ‖((x : H) - y)‖ ^ 2 := by
  let u : H := (x : H) - y
  let v : H := T x - T y
  have h_residual : residualMap D T x - residualMap D T y = u - v := by
    change (((x : H) - T x) - (y - T y)) = u - v
    simp [u, v, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  rw [h_residual]
  have h_expand : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * inner ℝ u v + ‖v‖ ^ 2 := by
    simpa using norm_sub_sq_real u v
  have h_inner : inner ℝ u (u - v) = ‖u‖ ^ 2 - inner ℝ u v := by
    rw [inner_sub_right, real_inner_self_eq_norm_sq]
  constructor <;> intro h <;> nlinarith [h, h_expand, h_inner]

/-- The residual map is `1 / 2`-cocoercive exactly when the map is pairwise nonexpansive in
norm. -/
private lemma residualMap_cocoerciveOn_half_iff_pairwise_norm_sub_le {D : Set H} {T : D → H} :
    CocoerciveOn (1 / 2 : ℝ) D (residualMap D T) ↔
      ∀ x y : D, ‖T x - T y‖ ≤ ‖(x : H) - y‖ := by
  constructor
  · intro h x y
    have hsq :
        ‖T x - T y‖ ^ 2 ≤ ‖((x : H) - y)‖ ^ 2 := by
      exact (residual_quadratic_expansion T x y).mp (h.ineq x y)
    exact (norm_sq_le_norm_sq_iff).mp hsq
  · intro h
    refine ⟨by norm_num, ?_⟩
    intro x y
    have hsq :
        ‖T x - T y‖ ^ 2 ≤ ‖((x : H) - y)‖ ^ 2 := by
      exact (norm_sq_le_norm_sq_iff).mpr (h x y)
    exact (residual_quadratic_expansion T x y).mpr hsq

/-- Proposition 4.11: a map on a subset of a real inner product space is nonexpansive exactly
when its residual map `Id - T` is `1 / 2`-cocoercive. -/
theorem lipschitzWith_one_iff_residualMap_cocoerciveOn_half {D : Set H} (T : D → H) :
    LipschitzWith 1 T ↔ CocoerciveOn (1 / 2 : ℝ) D (residualMap D T) := by
  rw [lipschitzWith_one_iff_pairwise_norm_sub_le,
    residualMap_cocoerciveOn_half_iff_pairwise_norm_sub_le]

end

/-! Source item: Chap04/Proposition_4_12 -/
universe w


noncomputable section

section

variable {ι : Type v} {H : Type u}
variable [Fintype ι] [NormedAddCommGroup H]

/-- Helper for Proposition 4.12: the weighted finite-family Jensen/Cauchy estimate controlling the
squared norm of a sum by the inverse-weighted sum of squared norms. -/
-- Proof step: first bound `‖∑ zᵢ‖` by `∑ ‖zᵢ‖`, then apply the scalar weighted
-- Cauchy-Schwarz inequality to the nonnegative family `‖zᵢ‖`.
private lemma norm_sum_sq_le_weighted_sum_inv
    (α : ι → ℝ) (z : ι → H) (hαpos : ∀ i, 0 < α i) (hαsum : ∑ i, α i = 1) :
    ‖∑ i, z i‖ ^ (2 : ℕ) ≤ ∑ i, (1 / α i) * ‖z i‖ ^ (2 : ℕ) := by
  have hnorm :
      ‖∑ i, z i‖ ≤ ∑ i, ‖z i‖ := by
    simpa using (norm_sum_le (Finset.univ) z)
  have hsq_norm :
      ‖∑ i, z i‖ ^ (2 : ℕ) ≤ (∑ i, ‖z i‖) ^ (2 : ℕ) := by
    exact sq_le_sq.mpr <| by
      simpa [abs_of_nonneg (norm_nonneg _),
        abs_of_nonneg (Finset.sum_nonneg (fun i hi ↦ norm_nonneg (z i)))] using hnorm
  have hscalar :
      (∑ i, ‖z i‖) ^ (2 : ℕ) / ∑ i, α i ≤ ∑ i, ‖z i‖ ^ (2 : ℕ) / α i := by
    simpa using
      (Finset.sq_sum_div_le_sum_sq_div
        Finset.univ (fun i ↦ ‖z i‖) (fun i hi ↦ hαpos i))
  have hweighted :
      (∑ i, ‖z i‖) ^ (2 : ℕ) ≤ ∑ i, ‖z i‖ ^ (2 : ℕ) / α i := by
    simpa [hαsum] using hscalar
  exact hsq_norm.trans <| by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hweighted

end

section

variable {ι : Type v} {H : Type u} {K : ι → Type w}
variable [Fintype ι]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [∀ i, NormedAddCommGroup (K i)] [∀ i, InnerProductSpace ℝ (K i)]
variable [∀ i, CompleteSpace (K i)]

/-- The operator obtained by summing the adjoint composites `Lᵢ* ∘ Tᵢ ∘ Lᵢ` over a finite family. -/
def adjointCompositeFamilySum (L : ∀ i, H →L[ℝ] K i) (T : ∀ i, K i → K i) : H → H :=
  fun x ↦ ∑ i, (L i).adjoint (T i (L i x))

/-- Helper for Proposition 4.12: the adjoint satisfies the squared operator-norm estimate needed
to replace `‖Lᵢ* z‖²` by `‖Lᵢ‖² ‖z‖²`. -/
-- Proof step: apply the standard operator norm bound to `A.adjoint`, then square the inequality
-- and rewrite `‖A.adjoint‖ = ‖A‖`.
private lemma adjoint_norm_sq_le_opNorm_sq {G : Type*}
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (A : H →L[ℝ] G) (z : G) :
    ‖A.adjoint z‖ ^ (2 : ℕ) ≤ ‖A‖ ^ (2 : ℕ) * ‖z‖ ^ (2 : ℕ) := by
  have hnorm : ‖A.adjoint z‖ ≤ ‖A‖ * ‖z‖ := by
    simpa using (ContinuousLinearMap.le_opNorm A.adjoint z)
  nlinarith [hnorm, norm_nonneg (A.adjoint z), norm_nonneg A, norm_nonneg z]

/-- Helper for Proposition 4.12: summing the component cocoercivity inequalities yields the lower
bound on the full adjoint composite sum. -/
-- Proof step: move each `Lᵢ` across the inner product by the adjoint identity, apply the
-- cocoercivity of `Tᵢ`, and convert the resulting `‖Tᵢ(Lᵢx) - Tᵢ(Lᵢy)‖²` term into the adjoint
-- expression using the operator norm bound for `Lᵢ*`.
private lemma componentwise_cocoercive_lower_bound
    (L : ∀ i, H →L[ℝ] K i) (βi : ι → ℝ) (T : ∀ i, K i → K i) (hL : ∀ i, L i ≠ 0)
    (hT : ∀ i, CocoerciveOn (βi i) Set.univ (fun x : Set.univ ↦ T i x)) (x y : H) :
    ∑ i,
        (βi i / ‖L i‖ ^ (2 : ℕ)) *
          ‖(L i).adjoint (T i (L i x) - T i (L i y))‖ ^ (2 : ℕ) ≤
      ⟪x - y, adjointCompositeFamilySum L T x - adjointCompositeFamilySum L T y⟫_ℝ := by
  have hsummand :
      ∀ i,
        (βi i / ‖L i‖ ^ (2 : ℕ)) *
            ‖(L i).adjoint (T i (L i x) - T i (L i y))‖ ^ (2 : ℕ) ≤
          ⟪x - y, (L i).adjoint (T i (L i x) - T i (L i y))⟫_ℝ := by
    intro i
    let u : K i := T i (L i x) - T i (L i y)
    have hβi_pos : 0 < βi i := (hT i).pos
    have hLi_pos : 0 < ‖L i‖ := norm_pos_iff.mpr (hL i)
    have hLi_sq_pos : 0 < ‖L i‖ ^ (2 : ℕ) := by positivity
    have hnorm_sq :
        ‖(L i).adjoint u‖ ^ (2 : ℕ) ≤ ‖L i‖ ^ (2 : ℕ) * ‖u‖ ^ (2 : ℕ) :=
      adjoint_norm_sq_le_opNorm_sq (L i) u
    have hscaled :
        (βi i / ‖L i‖ ^ (2 : ℕ)) * ‖(L i).adjoint u‖ ^ (2 : ℕ) ≤
          βi i * ‖u‖ ^ (2 : ℕ) := by
      have hfactor_nonneg : 0 ≤ βi i / ‖L i‖ ^ (2 : ℕ) := by
        exact div_nonneg (le_of_lt hβi_pos) (le_of_lt hLi_sq_pos)
      calc
        (βi i / ‖L i‖ ^ (2 : ℕ)) * ‖(L i).adjoint u‖ ^ (2 : ℕ) ≤
            (βi i / ‖L i‖ ^ (2 : ℕ)) * (‖L i‖ ^ (2 : ℕ) * ‖u‖ ^ (2 : ℕ)) := by
              exact mul_le_mul_of_nonneg_left hnorm_sq hfactor_nonneg
        _ = βi i * ‖u‖ ^ (2 : ℕ) := by
              field_simp [hLi_sq_pos.ne']
    have hcoco :
        βi i * ‖u‖ ^ (2 : ℕ) ≤ ⟪L i x - L i y, u⟫_ℝ := by
      simpa [u, map_sub] using
        (hT i).ineq ⟨L i x, Set.mem_univ (L i x)⟩ ⟨L i y, Set.mem_univ (L i y)⟩
    have hadjoint :
        ⟪L i x - L i y, u⟫_ℝ = ⟪x - y, (L i).adjoint u⟫_ℝ := by
      calc
        ⟪L i x - L i y, u⟫_ℝ = ⟪L i (x - y), u⟫_ℝ := by rw [map_sub]
        _ = ⟪x - y, (L i).adjoint u⟫_ℝ := by
              simpa using (ContinuousLinearMap.adjoint_inner_right (L i) (x - y) u).symm
    exact hscaled.trans <| hcoco.trans_eq hadjoint
  calc
    ∑ i,
        (βi i / ‖L i‖ ^ (2 : ℕ)) *
          ‖(L i).adjoint (T i (L i x) - T i (L i y))‖ ^ (2 : ℕ)
        ≤ ∑ i, ⟪x - y, (L i).adjoint (T i (L i x) - T i (L i y))⟫_ℝ := by
            exact Finset.sum_le_sum (fun i hi ↦ hsummand i)
    _ = ⟪x - y, ∑ i, (L i).adjoint (T i (L i x) - T i (L i y))⟫_ℝ := by
          rw [inner_sum]
    _ = ⟪x - y, adjointCompositeFamilySum L T x - adjointCompositeFamilySum L T y⟫_ℝ := by
          simp [adjointCompositeFamilySum, Finset.sum_sub_distrib, map_sub]

-- Proof sketch: expand the inner product against the finite sum, move each summand across the
-- adjoint, apply the `βᵢ`-cocoercivity hypotheses for the component maps `Tᵢ`, bound the adjoint
-- terms using `‖Lᵢ* z‖ ≤ ‖Lᵢ‖ ‖z‖`, and finish with the weighted Jensen/Cauchy-Schwarz estimate for
-- the coefficient `(∑ i, ‖Lᵢ‖² / βᵢ)⁻¹`.
/-- Proposition 4.12: if each `Tᵢ` is `βᵢ`-cocoercive, then the finite sum
`∑ i, Lᵢ* ∘ Tᵢ ∘ Lᵢ` is `(∑ i, ‖Lᵢ‖² / βᵢ)⁻¹`-cocoercive for a nonempty finite family. -/
theorem cocoerciveOn_univ_adjointCompositeFamilySum
    [Nonempty ι] (L : ∀ i, H →L[ℝ] K i) (βi : ι → ℝ) (T : ∀ i, K i → K i)
    (hL : ∀ i, L i ≠ 0)
    (hT : ∀ i, CocoerciveOn (βi i) Set.univ (fun x : Set.univ ↦ T i x)) :
    CocoerciveOn (1 / ∑ i, ‖L i‖ ^ (2 : ℕ) / βi i) Set.univ
      (fun x : Set.univ ↦ adjointCompositeFamilySum L T x) := by
  classical
  have hβi : ∀ i, 0 < βi i := fun i ↦ (hT i).pos
  let d : ℝ := ∑ i, ‖L i‖ ^ (2 : ℕ) / βi i
  let β : ℝ := 1 / d
  have hd_pos : 0 < d := by
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    have hi₀_pos : 0 < ‖L i₀‖ ^ (2 : ℕ) / βi i₀ := by
      have hLi₀_pos : 0 < ‖L i₀‖ := norm_pos_iff.mpr (hL i₀)
      have hLi₀_sq_pos : 0 < ‖L i₀‖ ^ (2 : ℕ) := by positivity
      exact div_pos hLi₀_sq_pos (hβi i₀)
    have hterm_nonneg : ∀ i, 0 ≤ ‖L i‖ ^ (2 : ℕ) / βi i := by
      intro i
      have hLi_sq_nonneg : 0 ≤ ‖L i‖ ^ (2 : ℕ) := by positivity
      exact div_nonneg hLi_sq_nonneg (le_of_lt (hβi i))
    have hi₀_le : ‖L i₀‖ ^ (2 : ℕ) / βi i₀ ≤ ∑ i, ‖L i‖ ^ (2 : ℕ) / βi i := by
      simpa using
        (Finset.single_le_sum
          (fun j hj ↦ hterm_nonneg j)
          (show i₀ ∈ (Finset.univ : Finset ι) by simp))
    simpa [d] using lt_of_lt_of_le hi₀_pos hi₀_le
  have hβ_pos : 0 < β := by
    simpa [β] using inv_pos.mpr hd_pos
  refine ⟨by simpa [β, d] using hβ_pos, ?_⟩
  intro x y
  let α : ι → ℝ := fun i ↦ β * ‖L i‖ ^ (2 : ℕ) / βi i
  let z : ι → H := fun i ↦ (L i).adjoint (T i (L i x) - T i (L i y))
  have hαpos : ∀ i, 0 < α i := by
    intro i
    have hLi_pos : 0 < ‖L i‖ := norm_pos_iff.mpr (hL i)
    have hLi_sq_pos : 0 < ‖L i‖ ^ (2 : ℕ) := by positivity
    dsimp [α]
    exact div_pos (mul_pos hβ_pos hLi_sq_pos) (hβi i)
  have hαsum : ∑ i, α i = 1 := by
    -- The normalization matches the textbook coefficients `αᵢ = β ‖Lᵢ‖² / βᵢ`.
    calc
      ∑ i, α i = β * ∑ i, ‖L i‖ ^ (2 : ℕ) / βi i := by
        simp [α, Finset.mul_sum, mul_assoc, mul_comm, div_eq_mul_inv]
      _ = 1 := by
        have hd_ne : d ≠ 0 := hd_pos.ne'
        simp [β, d, hd_ne]
  have hzsum :
      ∑ i, z i = adjointCompositeFamilySum L T x - adjointCompositeFamilySum L T y := by
    -- The adjoint composite sum difference is the sum of the component differences.
    simp [adjointCompositeFamilySum, z, Finset.sum_sub_distrib, map_sub]
  have hcoef :
      ∀ i, β * (1 / α i) = βi i / ‖L i‖ ^ (2 : ℕ) := by
    intro i
    have hLi_pos : 0 < ‖L i‖ := norm_pos_iff.mpr (hL i)
    have hLi_sq_pos : 0 < ‖L i‖ ^ (2 : ℕ) := by positivity
    have hαi_pos : 0 < α i := hαpos i
    dsimp [α]
    field_simp [hαi_pos.ne', hβ_pos.ne', hLi_sq_pos.ne', (hβi i).ne']
  have hweighted :
      β * ‖adjointCompositeFamilySum L T x - adjointCompositeFamilySum L T y‖ ^ (2 : ℕ) ≤
        ∑ i, (βi i / ‖L i‖ ^ (2 : ℕ)) * ‖z i‖ ^ (2 : ℕ) := by
    have hnorm :
        ‖∑ i, z i‖ ^ (2 : ℕ) ≤ ∑ i, (1 / α i) * ‖z i‖ ^ (2 : ℕ) :=
      norm_sum_sq_le_weighted_sum_inv α z hαpos hαsum
    have hβ_nonneg : 0 ≤ β := le_of_lt hβ_pos
    calc
      β * ‖adjointCompositeFamilySum L T x - adjointCompositeFamilySum L T y‖ ^ (2 : ℕ)
          = β * ‖∑ i, z i‖ ^ (2 : ℕ) := by rw [← hzsum]
      _ ≤ β * ∑ i, (1 / α i) * ‖z i‖ ^ (2 : ℕ) := by
            exact mul_le_mul_of_nonneg_left hnorm hβ_nonneg
      _ = ∑ i, (βi i / ‖L i‖ ^ (2 : ℕ)) * ‖z i‖ ^ (2 : ℕ) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl ?_
            intro i hi
            calc
              β * ((1 / α i) * ‖z i‖ ^ (2 : ℕ))
                  = (β * (1 / α i)) * ‖z i‖ ^ (2 : ℕ) := by ring
              _ = (βi i / ‖L i‖ ^ (2 : ℕ)) * ‖z i‖ ^ (2 : ℕ) := by
                    rw [hcoef i]
  -- Route correction: finish with the weighted scalar Cauchy step, not by ad hoc expansion of
  -- the full squared norm of the operator sum.
  exact hweighted.trans <|
    componentwise_cocoercive_lower_bound L βi T hL hT x y

end

end

/-! Source item: Chap04/Corollary_4_13 -/


section

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

-- Rewrite the compressed inner product on `H` as the corresponding inner product on `K`.
private lemma inner_sub_adjoint_apply_eq (L : H →L[ℝ] K) (x y : H) (z : K) :
    inner ℝ (x - y) (L.adjoint z) = inner ℝ (L x - L y) z := by
  rw [adjoint_inner_right, map_sub]

-- If `‖L‖ ≤ 1`, then applying `L.adjoint` preserves the squared contraction bound.
private lemma norm_sq_adjoint_apply_le_of_norm_le_one
    (L : H →L[ℝ] K) (hL : ‖L‖ ≤ 1) (z : K) :
    ‖L.adjoint z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
  have hNorm : ‖L.adjoint z‖ ≤ ‖z‖ := by
    calc
      ‖L.adjoint z‖ ≤ ‖L.adjoint‖ * ‖z‖ := le_opNorm _ _
      _ = ‖L‖ * ‖z‖ := by simp [adjoint.norm_map]
      _ ≤ 1 * ‖z‖ := by gcongr
      _ = ‖z‖ := by ring
  nlinarith [hNorm, norm_nonneg (L.adjoint z), norm_nonneg z]

-- Proof sketch: apply the Hilbert-space firm nonexpansiveness inequality for `T` to `L x` and
-- `L y`, rewrite the resulting inner product using the adjoint identity for `L`, and use
-- `‖L.adjoint z‖ ≤ ‖L‖ * ‖z‖ ≤ ‖z‖` from `‖L‖ ≤ 1`.
/-- Corollary 4.13: if `T` is firmly nonexpansive on the real Hilbert space `K` in the standard
inner-product form and `L : H →L[ℝ] K` has operator norm at most `1`, then the compressed map
`L.adjoint ∘ T ∘ L` is firmly nonexpansive on `H`. -/
theorem adjoint_comp_firmlyNonexpansive_of_norm_le_one
    (T : K → K)
    (hT : FirmlyNonexpansiveOn (Set.univ : Set K) (fun x : Set.univ ↦ T x))
    (L : H →L[ℝ] K) (hL : ‖L‖ ≤ 1) :
    FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ (L.adjoint ∘ T ∘ L) x) := by
  intro x y
  set z : K := T (L x) - T (L y)
  have hTxy : ‖z‖ ^ 2 ≤ ⟪z, L x - L y⟫_ℝ := by
    have hT' : ‖T (L x) - T (L y)‖ ^ 2 ≤ ⟪T (L x) - T (L y), L x - L y⟫_ℝ :=
      by
        simpa [real_inner_comm] using hT ⟨L x, by simp⟩ ⟨L y, by simp⟩
    simpa [z, map_sub] using hT'
  calc
    ‖(L.adjoint ∘ T ∘ L) x - (L.adjoint ∘ T ∘ L) y‖ ^ 2 = ‖L.adjoint z‖ ^ 2 := by
      simp [Function.comp, z, map_sub]
    _ ≤ ‖z‖ ^ 2 := norm_sq_adjoint_apply_le_of_norm_le_one L hL z
    _ ≤ ⟪z, L x - L y⟫_ℝ := hTxy
    _ = ⟪L x - L y, z⟫_ℝ := by rw [real_inner_comm]
    _ = ⟪(x : H) - y, L.adjoint z⟫_ℝ := by
      symm
      exact inner_sub_adjoint_apply_eq L (x : H) (y : H) z
    _ = ⟪(x : H) - y, (L.adjoint ∘ T ∘ L) x - (L.adjoint ∘ T ∘ L) y⟫_ℝ := by
      simp [Function.comp, z, map_sub]

end

/-! Source item: Chap04/Example_4_14 -/


section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Example 4.14: if `T : H → H` is firmly nonexpansive, then for every closed linear subspace
`V` the compressed operator `P_V ∘ T ∘ P_V` is firmly nonexpansive. -/
theorem orthogonal_projection_compression_firmly_nonexpansive
    (V : ClosedSubmodule ℝ H) {T : H → H}
    (hT : FirmlyNonexpansiveOn Set.univ (fun x : Set.univ ↦ T x)) :
    FirmlyNonexpansiveOn Set.univ
      (fun x : Set.univ ↦ (V.starProjection ∘ T ∘ V.starProjection) x) := by
  have hV : IsSelfAdjoint V.starProjection := isSelfAdjoint_starProjection (V : Submodule ℝ H)
  have h :=
    adjoint_comp_firmlyNonexpansive_of_norm_le_one T hT V.starProjection
      V.starProjection_norm_le
  simpa [Function.comp, hV.adjoint_eq] using h

end

/-! Source item: Chap04/Remark_4_15_1 -/

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

section

/-- Helper for Remark 4.15.1: cocoercivity and Cauchy--Schwarz give the textbook product bound. -/
private lemma cocoercive_norm_product_bound
    {D : Set H} {β : ℝ} {T : D → H} (hT : CocoerciveOn β D T) :
    ∀ x y : D, β * ‖T x - T y‖ ^ 2 ≤ ‖(x : H) - y‖ * ‖T x - T y‖ := by
  intro x y
  -- Bound the inner product from above by the product of the norms.
  exact (hT.ineq x y).trans (real_inner_le_norm ((x : H) - y) (T x - T y))

/-- The cocoercivity inequality yields the textbook pointwise `1 / β`-Lipschitz estimate. -/
-- Proof sketch: combine cocoercivity with the Cauchy--Schwarz inequality to get
-- `β * ‖T x - T y‖^2 ≤ ‖T x - T y‖ * ‖x - y‖`; if `T x = T y` the claim is immediate, and
-- otherwise divide by `‖T x - T y‖`.
private theorem norm_sub_le_inv_mul_norm_sub_of_cocoercive
    {D : Set H} {β : ℝ} {T : D → H} (hT : CocoerciveOn β D T) :
    ∀ x y : D, ‖T x - T y‖ ≤ β⁻¹ * ‖(x : H) - y‖ := by
  intro x y
  -- First convert cocoercivity into the textbook norm product inequality.
  have hbound : β * ‖T x - T y‖ ^ 2 ≤ ‖(x : H) - y‖ * ‖T x - T y‖ :=
    cocoercive_norm_product_bound hT x y
  by_cases hxy : T x = T y
  · -- In the degenerate case the left-hand norm is zero.
    have hnonneg : 0 ≤ β⁻¹ * ‖(x : H) - y‖ := by
      exact mul_nonneg (inv_nonneg.mpr hT.pos.le) (norm_nonneg _)
    simpa [hxy] using hnonneg
  · -- Otherwise the common norm factor is positive, so we cancel it.
    have hn_pos : 0 < ‖T x - T y‖ := by
      refine norm_pos_iff.mpr ?_
      exact sub_ne_zero.mpr hxy
    have hmul : β * ‖T x - T y‖ ≤ ‖(x : H) - y‖ := by
      exact le_of_mul_le_mul_right (by simpa [pow_two, mul_assoc] using hbound) hn_pos
    have hdiv : ‖T x - T y‖ ≤ ‖(x : H) - y‖ / β := by
      rw [le_div_iff₀ hT.pos]
      simpa [mul_comm] using hmul
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv

/-- Remark 4.15.1: a `β`-cocoercive map on a subset of a real Hilbert space is Lipschitz with
constant `1 / β`. -/
-- Proof sketch: first derive the textbook norm inequality from cocoercivity and Cauchy--Schwarz,
-- then apply `LipschitzWith.of_dist_le'` and rewrite distances in the subtype domain as norms in
-- `H`.
theorem lipschitzWith_of_cocoercive
    {D : Set H} {β : ℝ} {T : D → H} (hT : CocoerciveOn β D T) :
    LipschitzWith (Real.toNNReal (1 / β)) T := by
  -- Convert the pointwise norm estimate into the metric Lipschitz condition.
  refine LipschitzWith.of_dist_le' ?_
  intro x y
  -- Distances in the subtype domain are ambient distances, hence ambient norms.
  simpa [Subtype.dist_eq, dist_eq_norm, Real.toNNReal_of_nonneg (one_div_nonneg.mpr hT.pos.le),
    one_div, mul_comm, mul_left_comm, mul_assoc] using
    norm_sub_le_inv_mul_norm_sub_of_cocoercive hT x y

end

/-! Source item: Chap04/Remark_4_15_2 -/

noncomputable section

local notation "R3" => EuclideanSpace ℝ (Fin 3)

/-- The matrix from the remark, whose rows are the cyclic first-difference coefficients on `ℝ^3`.
-/
def cyclic_difference_matrix : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, -1, 0; 0, 1, -1; -1, 0, 1]

/-- The linear operator on `ℝ^3` defined by the matrix of cyclic first differences. -/
def cyclic_difference_operator : R3 →ₗ[ℝ] R3 :=
  cyclic_difference_matrix.toEuclideanLin

/-- The cyclic difference operator sends `(ξ₁, ξ₂, ξ₃)` to
`(ξ₁ - ξ₂, ξ₂ - ξ₃, ξ₃ - ξ₁)`. -/
-- Proof sketch: expand `cyclic_difference_operator`, evaluate the matrix-vector product row by
-- row, and transport back along `EuclideanSpace.equiv`.
theorem cyclic_difference_operator_apply (x : R3) :
    cyclic_difference_operator x =
      (EuclideanSpace.equiv (Fin 3) ℝ).symm ![x 0 - x 1, x 1 - x 2, x 2 - x 0] := by
  -- Compute the three coordinates of the matrix-vector product explicitly.
  ext i
  fin_cases i
  · simp [cyclic_difference_operator, cyclic_difference_matrix, dotProduct, Fin.sum_univ_three,
      sub_eq_add_neg]
  · simp [cyclic_difference_operator, cyclic_difference_matrix, dotProduct, Fin.sum_univ_three,
      sub_eq_add_neg]
  · simp [cyclic_difference_operator, cyclic_difference_matrix, dotProduct, Fin.sum_univ_three,
      sub_eq_add_neg, add_comm]

/-- The squared norm of `Bx` equals twice the inner product `⟪Bx, x⟫` for the cyclic difference
operator `B`. -/
-- Proof sketch: use `cyclic_difference_operator_apply`, expand both sides in coordinates, and
-- simplify the quadratic expressions.
theorem cyclic_difference_operator_norm_sq_eq_two_inner (x : R3) :
    ‖cyclic_difference_operator x‖ ^ (2 : ℕ) =
      2 * inner ℝ (cyclic_difference_operator x) x := by
  -- Rewrite `Bx` in coordinates and compare the two quadratic polynomials.
  rw [cyclic_difference_operator_apply]
  rw [show inner ℝ ((EuclideanSpace.equiv (Fin 3) ℝ).symm
      ![x 0 - x 1, x 1 - x 2, x 2 - x 0]) x =
      x 0 * (x 0 - x 1) + x 1 * (x 1 - x 2) + x 2 * (x 2 - x 0) by
      simpa [dotProduct, Fin.sum_univ_three] using
        (EuclideanSpace.inner_eq_star_dotProduct
          ((EuclideanSpace.equiv (Fin 3) ℝ).symm ![x 0 - x 1, x 1 - x 2, x 2 - x 0]) x)]
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  ring_nf

/-- The squared norm of `Bx` is `3 ‖x‖²` minus the square of the coordinate sum for the cyclic
difference operator `B`. -/
-- Proof sketch: use `cyclic_difference_operator_apply`, expand the coordinate formulas for
-- `‖Bx‖²`, `‖x‖²`, and `(∑ i, x i)^2`, and compare the resulting polynomials.
theorem cyclic_difference_operator_norm_sq_eq_three_norm_sq_sub_sum_sq (x : R3) :
    ‖cyclic_difference_operator x‖ ^ (2 : ℕ) =
      3 * ‖x‖ ^ (2 : ℕ) - (∑ i : Fin 3, x i) ^ (2 : ℕ) := by
  -- Expand both sides to the same coordinate polynomial and finish algebraically.
  rw [cyclic_difference_operator_apply]
  simp [EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_three]
  ring_nf

/-- Helper for Remark 4.15.2: the cyclic difference operator has norm at most `√3` times the
norm of its argument. -/
-- Square the desired estimate, use the quadratic identity, and drop the nonnegative square term.
private lemma cyclic_difference_operator_norm_le_sqrt_three (z : R3) :
    ‖cyclic_difference_operator z‖ ≤ (NNReal.sqrt 3 : ℝ) * ‖z‖ := by
  have hsquare : ‖cyclic_difference_operator z‖ ^ (2 : ℕ) ≤
      ((NNReal.sqrt 3 : ℝ) * ‖z‖) ^ (2 : ℕ) := by
    have hsqrt : ((NNReal.sqrt 3 : ℝ) ^ (2 : ℕ)) = 3 := by
      norm_num [NNReal.sq_sqrt]
    calc
      ‖cyclic_difference_operator z‖ ^ (2 : ℕ)
          = 3 * ‖z‖ ^ (2 : ℕ) - (∑ i : Fin 3, z i) ^ (2 : ℕ) :=
            cyclic_difference_operator_norm_sq_eq_three_norm_sq_sub_sum_sq z
      _ ≤ 3 * ‖z‖ ^ (2 : ℕ) := by
        nlinarith [sq_nonneg (∑ i : Fin 3, z i)]
      _ = ((NNReal.sqrt 3 : ℝ) * ‖z‖) ^ (2 : ℕ) := by
        rw [mul_pow, hsqrt]
  exact le_of_sq_le_sq hsquare (by positivity)

/-- The cyclic difference operator is `1 / 2`-cocoercive on `ℝ^3`. -/
theorem cyclic_difference_operator_cocoerciveOn :
    CocoerciveOn (1 / 2 : ℝ) Set.univ (fun x : Set.univ ↦ cyclic_difference_operator x) := by
  refine ⟨by norm_num, ?_⟩
  intro x y
  have h_identity := cyclic_difference_operator_norm_sq_eq_two_inner ((x : R3) - y)
  have h_eq :
      (1 / 2 : ℝ) * ‖cyclic_difference_operator ((x : R3) - y)‖ ^ (2 : ℕ) =
        inner ℝ (cyclic_difference_operator ((x : R3) - y)) ((x : R3) - y) := by
    nlinarith [h_identity]
  simpa [real_inner_comm] using le_of_eq h_eq

/-- The cyclic difference operator is `√3`-Lipschitz on `ℝ^3`. -/
theorem cyclic_difference_operator_lipschitzWith :
    LipschitzWith (NNReal.sqrt 3) cyclic_difference_operator := by
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  rw [dist_eq_norm, dist_eq_norm, ← cyclic_difference_operator.map_sub]
  exact cyclic_difference_operator_norm_le_sqrt_three (x - y)

/-- Remark 4.15.2: the cyclic difference operator associated to
`B = [[1, -1, 0], [0, 1, -1], [-1, 0, 1]]` is `1 / 2`-cocoercive on `ℝ^3` and is
`√3`-Lipschitz continuous. -/
-- Proof sketch: apply
-- `cyclic_difference_operator_norm_sq_eq_two_inner` and
-- `cyclic_difference_operator_norm_sq_eq_three_norm_sq_sub_sum_sq` to `x - y`; the first identity
-- gives the `1 / 2`-cocoercivity inequality, and the second gives the `√3` Lipschitz bound from
-- the nonnegativity of `(∑ i, (x - y) i)^2`.
theorem cyclic_difference_operator_cocoercive_and_lipschitz :
    CocoerciveOn (1 / 2 : ℝ) Set.univ (fun x : Set.univ ↦ cyclic_difference_operator x) ∧
    LipschitzWith (NNReal.sqrt 3) cyclic_difference_operator := by
  exact ⟨cyclic_difference_operator_cocoerciveOn, cyclic_difference_operator_lipschitzWith⟩

end

/-! Source item: Chap04/Proposition_4_16 -/


variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

section

variable {C : Set 𝓗} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" =>
  projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)

private theorem projectionPoint_mem_and_inner_sub_right_nonpos (x : 𝓗) :
    P x ∈ C ∧ ∀ z ∈ C, ⟪z - P x, x - P x⟫_ℝ ≤ 0 := by
  exact
    (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex).mp rfl

-- Proof sketch: let `P := projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty
-- hC_closed hC_convex)`. Use the variational characterization of metric projections onto nonempty
-- closed convex sets for `P x` tested against `P y` and for `P y` tested against `P x`; adding the
-- two inequalities and rearranging gives the stated bound.
/-- Proposition 4.16: the metric projection onto a nonempty closed convex subset of a real Hilbert
space is firmly nonexpansive: for all `x` and `y`, the canonical projection map
`P := projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)`
satisfies `‖P x - P y‖^2 ≤ ⟪P x - P y, x - y⟫_ℝ`. -/
theorem norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
    (x y : 𝓗) :
    ‖P x - P y‖ ^ (2 : ℕ) ≤ ⟪P x - P y, x - y⟫_ℝ := by
  let p := P x
  let q := P y
  have hp : p ∈ C ∧ ∀ z ∈ C, ⟪z - p, x - p⟫_ℝ ≤ 0 :=
    projectionPoint_mem_and_inner_sub_right_nonpos hC_nonempty hC_closed hC_convex x
  have hq : q ∈ C ∧ ∀ z ∈ C, ⟪z - q, y - q⟫_ℝ ≤ 0 :=
    projectionPoint_mem_and_inner_sub_right_nonpos hC_nonempty hC_closed hC_convex y
  -- Testing each variational inequality at the other projection point gives the two sign controls
  -- from the textbook proof.
  have hxp : 0 ≤ ⟪p - q, x - p⟫_ℝ := by
    have hqp : ⟪q - p, x - p⟫_ℝ ≤ 0 := hp.2 q hq.1
    have hneg :
        ⟪q - p, x - p⟫_ℝ = -⟪p - q, x - p⟫_ℝ := by
      rw [show q - p = -(p - q) by abel_nf, inner_neg_left]
    linarith [hqp, hneg]
  have hyq : ⟪p - q, y - q⟫_ℝ ≤ 0 := by
    simpa using hq.2 p hp.1
  -- Expand `⟪p - q, x - y⟫` into the two cross terms plus `‖p - q‖²`.
  have hsplit :
      ⟪p - q, x - y⟫_ℝ =
        ⟪p - q, x - p⟫_ℝ + ‖p - q‖ ^ (2 : ℕ) - ⟪p - q, y - q⟫_ℝ := by
    have hdecomp : x - y = (x - p) + (p - q) - (y - q) := by
      abel_nf
    calc
      ⟪p - q, x - y⟫_ℝ = ⟪p - q, (x - p) + (p - q) - (y - q)⟫_ℝ := by
        rw [hdecomp]
      _ = ⟪p - q, (x - p) + (p - q)⟫_ℝ - ⟪p - q, y - q⟫_ℝ := by
        rw [inner_sub_right]
      _ = ⟪p - q, x - p⟫_ℝ + ⟪p - q, p - q⟫_ℝ - ⟪p - q, y - q⟫_ℝ := by
        rw [inner_add_right]
      _ = ⟪p - q, x - p⟫_ℝ + ‖p - q‖ ^ (2 : ℕ) - ⟪p - q, y - q⟫_ℝ := by
        rw [real_inner_self_eq_norm_sq]
  -- The two sign controls show that the expanded right-hand side dominates `‖p - q‖²`.
  have hfinal : ‖p - q‖ ^ (2 : ℕ) ≤ ⟪p - q, x - y⟫_ℝ := by
    rw [hsplit]
    linarith
  simpa [p, q] using hfinal

end

/-! Source item: Chap04/Example_4_17 -/


section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem firmlyNonexpansiveOn_univ_iff {T : H → H} :
    FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T x) ↔
      ∀ x y : H, ‖T x - T y‖ ^ (2 : ℕ) ≤ ⟪T x - T y, x - y⟫_ℝ := by
  exact firmlyNonexpansiveOn_univ_iff_norm_sq_le_inner

private theorem firmlyNonexpansiveOn_univ_iff_reflectedMap_nonexpansive {T : H → H} :
    FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T x) ↔
      ∀ x y : H, ‖((2 : ℝ) • T x - x) - ((2 : ℝ) • T y - y)‖ ≤ ‖x - y‖ := by
  rw [firmlyNonexpansiveOn_univ_iff]
  constructor
  · intro hT x y
    have hsq :
        ‖((2 : ℝ) • T x - x) - ((2 : ℝ) • T y - y)‖ ^ (2 : ℕ) ≤ ‖x - y‖ ^ (2 : ℕ) := by
      have hnorm :
          ‖((2 : ℝ) • T x - x) - ((2 : ℝ) • T y - y)‖ ^ (2 : ℕ) =
            4 * ‖T x - T y‖ ^ (2 : ℕ) - 4 * ⟪T x - T y, x - y⟫_ℝ + ‖x - y‖ ^ (2 : ℕ) := by
        have hrewrite :
            ((2 : ℝ) • T x - x) - ((2 : ℝ) • T y - y) =
              (2 : ℝ) • (T x - T y) - (x - y) := by
          simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        rw [hrewrite, norm_sub_sq_real]
        rw [show ‖(2 : ℝ) • (T x - T y)‖ ^ (2 : ℕ) = 4 * ‖T x - T y‖ ^ (2 : ℕ) by
          rw [norm_smul]
          norm_num
          ring]
        rw [show ⟪(2 : ℝ) • (T x - T y), x - y⟫_ℝ = 2 * ⟪T x - T y, x - y⟫_ℝ by
          rw [real_inner_smul_left]]
        ring
      rw [hnorm]
      nlinarith [hT x y]
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
  · intro hR x y
    have hsq :
        ‖((2 : ℝ) • T x - x) - ((2 : ℝ) • T y - y)‖ ^ (2 : ℕ) ≤ ‖x - y‖ ^ (2 : ℕ) := by
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hR x y)
    have hnorm :
        ‖((2 : ℝ) • T x - x) - ((2 : ℝ) • T y - y)‖ ^ (2 : ℕ) =
          4 * ‖T x - T y‖ ^ (2 : ℕ) - 4 * ⟪T x - T y, x - y⟫_ℝ + ‖x - y‖ ^ (2 : ℕ) := by
      have hrewrite :
          ((2 : ℝ) • T x - x) - ((2 : ℝ) • T y - y) =
            (2 : ℝ) • (T x - T y) - (x - y) := by
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      rw [hrewrite, norm_sub_sq_real]
      rw [show ‖(2 : ℝ) • (T x - T y)‖ ^ (2 : ℕ) = 4 * ‖T x - T y‖ ^ (2 : ℕ) by
        rw [norm_smul]
        norm_num
        ring]
      rw [show ⟪(2 : ℝ) • (T x - T y), x - y⟫_ℝ = 2 * ⟪T x - T y, x - y⟫_ℝ by
        rw [real_inner_smul_left]]
      ring
    rw [hnorm] at hsq
    nlinarith

private theorem firmlyNonexpansiveOn_univ_iff_lipschitzWith_one_reflectedMap {T : H → H} :
    FirmlyNonexpansiveOn (Set.univ : Set H) (fun x : Set.univ ↦ T x) ↔
      LipschitzWith 1 (fun x ↦ (2 : ℝ) • T x - x) := by
  constructor
  · intro hT
    have hR :=
      firmlyNonexpansiveOn_univ_iff_reflectedMap_nonexpansive.1 hT
    refine LipschitzWith.of_dist_le_mul ?_
    intro x y
    simpa [dist_eq_norm, one_mul] using hR x y
  · intro hR
    refine firmlyNonexpansiveOn_univ_iff_reflectedMap_nonexpansive.2 ?_
    intro x y
    simpa [dist_eq_norm, one_mul] using hR.dist_le_mul x y

/-- The soft thresholder at level `ρ`, as in formula (4.16). -/
noncomputable def softThresholder (ρ : ℝ) : H → H :=
  fun x ↦ if ρ < ‖x‖ then (1 - ρ / ‖x‖) • x else 0

/-- The soft thresholder acts by radial shrinkage outside the radius-`ρ` ball and vanishes
inside. -/
-- Proof sketch: unfold `softThresholder`.
theorem softThresholder_apply (ρ : ℝ) (x : H) :
    softThresholder ρ x = if ρ < ‖x‖ then (1 - ρ / ‖x‖) • x else 0 := by
  -- The definition is already in the required form.
  rfl

/-- The hard thresholder at level `ρ` and relaxation parameter `α`, as in formula (4.17). -/
noncomputable def hardThresholder (ρ α : ℝ) : H → H :=
  fun x ↦ if ρ < ‖x‖ then α • x else 0

/-- The hard thresholder scales vectors outside the radius-`ρ` ball and vanishes inside. -/
-- Proof sketch: unfold `hardThresholder`.
theorem hardThresholder_apply (ρ α : ℝ) (x : H) :
    hardThresholder ρ α x = if ρ < ‖x‖ then α • x else 0 := by
  -- The definition is already in the required form.
  rfl

/-- The operator `T₃` from formula (4.18). -/
noncomputable def reflectedSoftThresholder (ρ : ℝ) : H → H :=
  fun x ↦ if ρ < ‖x‖ then (1 - 2 * ρ / ‖x‖) • x else -x

/-- The operator `T₃` reflects vectors in the closed ball and applies the outer radial formula
outside it. -/
-- Proof sketch: unfold `reflectedSoftThresholder`.
theorem reflectedSoftThresholder_apply (ρ : ℝ) (x : H) :
    reflectedSoftThresholder ρ x =
      if ρ < ‖x‖ then (1 - 2 * ρ / ‖x‖) • x else -x := by
  -- The definition is already in the required form.
  rfl

private theorem closedBall_zero_nonempty {E : Type u} [NormedAddCommGroup E] (ρ : ℝ) (hρ : 0 < ρ) :
    (Metric.closedBall (0 : E) ρ : Set E).Nonempty := by
  -- The origin itself lies in the ball because its norm is `0`.
  refine ⟨0, ?_⟩
  simpa [Metric.mem_closedBall, dist_eq_norm] using hρ.le

section

variable [CompleteSpace H]

private theorem projectionPoint_closedBall_zero_eq_radial_clip (ρ : ℝ) (hρ : 0 < ρ) (x : H) :
    projectionPoint (Metric.closedBall (0 : H) ρ)
        (isChebyshev_of_nonempty_isClosed_convex
          (closedBall_zero_nonempty ρ hρ)
          (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : H) ρ))
          (convex_closedBall (0 : H) ρ)) x =
      if ρ < ‖x‖ then (ρ / ‖x‖) • x else x := by
  let C : Set H := Metric.closedBall (0 : H) ρ
  have hC_nonempty : C.Nonempty := closedBall_zero_nonempty ρ hρ
  have hC_closed : IsClosed C := Metric.isClosed_closedBall
  have hC_convex : Convex ℝ C := convex_closedBall (0 : H) ρ
  by_cases hx : ρ < ‖x‖
  · have hnormx_pos : 0 < ‖x‖ := lt_trans hρ hx
    have hnormx : ‖x‖ ≠ 0 := hnormx_pos.ne'
    have hp_norm : ‖(ρ / ‖x‖) • x‖ = ρ := by
      calc
        ‖(ρ / ‖x‖) • x‖ = |ρ / ‖x‖| * ‖x‖ := norm_smul _ _
        _ = (ρ / ‖x‖) * ‖x‖ := by
          rw [abs_of_pos (div_pos hρ hnormx_pos)]
        _ = ρ := by
          rw [div_eq_mul_inv, mul_assoc, inv_mul_cancel₀ hnormx, mul_one]
    have hp_inner : ⟪(ρ / ‖x‖) • x, x⟫_ℝ = ρ * ‖x‖ := by
      calc
        ⟪(ρ / ‖x‖) • x, x⟫_ℝ = (ρ / ‖x‖) * ⟪x, x⟫_ℝ := by
          rw [real_inner_smul_left]
        _ = (ρ / ‖x‖) * ‖x‖ ^ 2 := by
          rw [real_inner_self_eq_norm_sq]
        _ = ρ * ‖x‖ := by
          rw [pow_two, div_eq_mul_inv]
          ring_nf
          field_simp [hnormx]
    -- The radial candidate satisfies the projection characterization.
    have hproj :
        (ρ / ‖x‖) • x =
          projectionPoint C
            (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x := by
      refine
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex).mpr ?_
      refine ⟨?_, ?_⟩
      · -- The candidate lies on the sphere of radius `ρ`, hence in the closed ball.
        show dist ((ρ / ‖x‖) • x) 0 ≤ ρ
        simp [dist_eq_norm, hp_norm]
      · intro y hy
        have hy_norm : ‖y‖ ≤ ρ := by
          simpa [C, Metric.mem_closedBall, dist_eq_norm] using hy
        have hy_inner : ⟪y, x⟫_ℝ ≤ ρ * ‖x‖ := by
          calc
            ⟪y, x⟫_ℝ ≤ ‖y‖ * ‖x‖ := real_inner_le_norm y x
            _ ≤ ρ * ‖x‖ := by
              gcongr
        have hcoef_nonneg : 0 ≤ 1 - ρ / ‖x‖ := by
          have hdiv_lt : ρ / ‖x‖ < 1 := by
            exact (div_lt_one hnormx_pos).2 hx
          linarith
        -- Route correction: use the variational inequality directly on the radial candidate instead
        -- of unfolding the metric infimum definition.
        calc
          ⟪y - (ρ / ‖x‖) • x, x - (ρ / ‖x‖) • x⟫_ℝ
              = (1 - ρ / ‖x‖) * ⟪y - (ρ / ‖x‖) • x, x⟫_ℝ := by
                rw [show x - (ρ / ‖x‖) • x = (1 - ρ / ‖x‖) • x by
                  calc
                    x - (ρ / ‖x‖) • x = (1 : ℝ) • x - (ρ / ‖x‖) • x := by rw [one_smul]
                    _ = (1 - ρ / ‖x‖) • x := by rw [sub_smul], real_inner_smul_right]
          _ ≤ 0 := by
            refine mul_nonpos_of_nonneg_of_nonpos hcoef_nonneg ?_
            calc
              ⟪y - (ρ / ‖x‖) • x, x⟫_ℝ = ⟪y, x⟫_ℝ - ⟪(ρ / ‖x‖) • x, x⟫_ℝ := by
                rw [inner_sub_left]
              _ ≤ 0 := by
                linarith [hy_inner, hp_inner]
    simpa [C, hx] using hproj.symm
  · have hx_mem : x ∈ C := by
      simpa [C, Metric.mem_closedBall, dist_eq_norm] using le_of_not_gt hx
    -- Points already in the closed ball are fixed by the projector.
    have hproj :
        x =
          projectionPoint C
            (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x := by
      refine
        (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
          hC_nonempty hC_closed hC_convex).mpr ?_
      refine ⟨hx_mem, ?_⟩
      intro y hy
      simp
    simpa [C, hx] using hproj.symm

/-- The soft thresholder is the residual of projection onto the centered closed ball. -/
theorem softThresholder_eq_sub_projection_closedBall (ρ : ℝ) (hρ : 0 < ρ) (x : H) :
    softThresholder ρ x =
      x -
        projectionPoint (Metric.closedBall (0 : H) ρ)
          (isChebyshev_of_nonempty_isClosed_convex
            (closedBall_zero_nonempty ρ hρ)
            (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : H) ρ))
            (convex_closedBall (0 : H) ρ)) x := by
  -- Split according to the textbook radial threshold.
  rw [softThresholder_apply, projectionPoint_closedBall_zero_eq_radial_clip ρ hρ x]
  by_cases hx : ρ < ‖x‖
  · -- Outside the ball, `x - P x` is exactly the residual radial factor.
    simp [hx]
    have hsub : x - (ρ / ‖x‖) • x = (1 - ρ / ‖x‖) • x := by
      calc
        x - (ρ / ‖x‖) • x = (1 : ℝ) • x - (ρ / ‖x‖) • x := by rw [one_smul]
        _ = (1 - ρ / ‖x‖) • x := by rw [sub_smul]
    simpa using hsub.symm
  · -- Inside the ball, the projector fixes `x`, so the residual vanishes.
    simp [hx]

end

/-- Helper for Example 4.17: the reflected soft thresholder is the reflector `2T - Id` of the
soft thresholder. -/
theorem reflectedSoftThresholder_eq_reflectedMap_softThresholder (ρ : ℝ) (x : H) :
    reflectedSoftThresholder ρ x = (2 : ℝ) • softThresholder ρ x - x := by
  rw [reflectedSoftThresholder_apply, softThresholder_apply]
  by_cases hx : ρ < ‖x‖
  · rw [if_pos hx, if_pos hx]
    have hout :
        (2 : ℝ) • ((1 - ρ / ‖x‖) • x) - x = (1 - 2 * ρ / ‖x‖) • x := by
      calc
        (2 : ℝ) • ((1 - ρ / ‖x‖) • x) - x = (2 * (1 - ρ / ‖x‖)) • x - x := by
          rw [smul_smul]
        _ = (2 - 2 * ρ / ‖x‖) • x - x := by ring_nf
        _ = (1 - 2 * ρ / ‖x‖) • x := by
          calc
            (2 - 2 * ρ / ‖x‖) • x - x = (2 - 2 * ρ / ‖x‖) • x - (1 : ℝ) • x := by
              rw [one_smul]
            _ = ((2 - 2 * ρ / ‖x‖) - 1) • x := by rw [← sub_smul]
            _ = (1 - 2 * ρ / ‖x‖) • x := by ring_nf
    simpa using hout.symm
  · rw [if_neg hx, if_neg hx]
    simp

private theorem hardThresholder_fixed_iff_eq_zero (ρ α : ℝ) (hα1 : α < 1) (y : H) :
    hardThresholder ρ α y = y ↔ y = 0 := by
  constructor
  · intro hy
    by_cases hyρ : ρ < ‖y‖
    · -- On the outer branch the fixed-point equation forces `(α - 1) • y = 0`.
      have hscale : (α - 1) • y = 0 := by
        calc
          (α - 1) • y = α • y - y := by
            rw [sub_smul, one_smul]
          _ = hardThresholder ρ α y - y := by
            rw [hardThresholder_apply, if_pos hyρ]
          _ = 0 := by
            rw [hy, sub_self]
      have hαne : α - 1 ≠ 0 := sub_ne_zero.mpr hα1.ne
      rcases smul_eq_zero.mp hscale with hzero | hyzero
      · exact False.elim (hαne hzero)
      · exact hyzero
    · -- On the inner branch the operator value is `0`.
      rw [hardThresholder_apply, if_neg hyρ] at hy
      simpa using hy.symm
  · intro hy
    -- The origin is trivially fixed.
    rw [hy, hardThresholder_apply]
    simp

private theorem norm_hardThresholder_le_norm (ρ α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (x : H) :
    ‖hardThresholder ρ α x‖ ≤ ‖x‖ := by
  by_cases hx : ρ < ‖x‖
  · -- Outside the ball, the operator just scales by a factor in `[0,1]`.
    rw [hardThresholder_apply, if_pos hx]
    calc
      ‖α • x‖ = α * ‖x‖ := by
        rw [norm_smul, Real.norm_of_nonneg hα0]
      _ ≤ ‖x‖ := by
        nlinarith [norm_nonneg x]
  · -- Inside the ball, the operator vanishes.
    rw [hardThresholder_apply, if_neg hx]
    simp

-- Proof sketch: identify `softThresholder ρ` with `Id - P_{closedBall 0 ρ}` and combine the
-- projector example with the firm-nonexpansive projector criterion.
/-- Example 4.17 (1): for positive level `ρ`, the soft thresholder is firmly nonexpansive. -/
theorem softThresholder_firmlyNonexpansive [CompleteSpace H] (ρ : ℝ) (hρ : 0 < ρ) :
    FirmlyNonexpansiveOn (Set.univ : Set H)
      (fun x : Set.univ ↦ (softThresholder ρ : H → H) x) := by
  rw [firmlyNonexpansiveOn_univ_iff]
  intro x y
  let C : Set H := Metric.closedBall (0 : H) ρ
  let P : H → H :=
    fun z ↦
      projectionPoint C
        (isChebyshev_of_nonempty_isClosed_convex
          (closedBall_zero_nonempty ρ hρ)
          (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : H) ρ))
          (convex_closedBall (0 : H) ρ)) z
  let a := P x - P y
  let b := x - y
  have hproj : ‖a‖ ^ (2 : ℕ) ≤ ⟪a, b⟫_ℝ := by
    simpa [a, b, P, C] using
      norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
        (closedBall_zero_nonempty ρ hρ)
        (Metric.isClosed_closedBall : IsClosed (Metric.closedBall (0 : H) ρ))
        (convex_closedBall (0 : H) ρ) x y
  have hresid_diff : (x - P x) - (y - P y) = b - a := by
    dsimp [a, b]
    abel_nf
  have hinner :
      ⟪b - a, b⟫_ℝ = ‖b‖ ^ (2 : ℕ) - ⟪a, b⟫_ℝ := by
    calc
      ⟪b - a, b⟫_ℝ = ⟪b, b⟫_ℝ - ⟪a, b⟫_ℝ := by
        rw [inner_sub_left]
      _ = ‖b‖ ^ (2 : ℕ) - ⟪a, b⟫_ℝ := by
        rw [real_inner_self_eq_norm_sq]
  have hnorm :
      ‖b - a‖ ^ (2 : ℕ) = ‖b‖ ^ (2 : ℕ) - 2 * ⟪b, a⟫_ℝ + ‖a‖ ^ (2 : ℕ) := by
    simpa using norm_sub_sq_real b a
  have hfinal : ‖b - a‖ ^ (2 : ℕ) ≤ ⟪b - a, b⟫_ℝ := by
    have hnorm' :
        ‖b - a‖ ^ (2 : ℕ) = ‖b‖ ^ (2 : ℕ) - 2 * ⟪a, b⟫_ℝ + ‖a‖ ^ (2 : ℕ) := by
      simpa [real_inner_comm] using hnorm
    rw [hnorm', hinner]
    nlinarith [hproj]
  -- The residual map `x - P x` is exactly the soft thresholder.
  simpa [hresid_diff, a, b, P, C,
    softThresholder_eq_sub_projection_closedBall ρ hρ x,
    softThresholder_eq_sub_projection_closedBall ρ hρ y] using hfinal

-- Proof sketch: show that the only fixed point is `0`, then use `‖hardThresholder ρ α x‖ ≤ ‖x‖`
-- for `0 < α < 1` to verify the defining inequality relative to fixed points.
/-- Example 4.17 (2): for `0 < α < 1`, the hard thresholder is quasinonexpansive. -/
theorem hardThresholder_quasinonexpansive (ρ α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    QuasinonexpansiveOn (Set.univ : Set H) (hardThresholder ρ α : H → H) := by
  rw [quasinonexpansiveOn_iff]
  intro x _ y hy
  rcases hy with ⟨_, hyfix⟩
  have hy_zero : y = 0 := by
    rw [Function.mem_fixedPoints_iff] at hyfix
    exact (hardThresholder_fixed_iff_eq_zero ρ α hα1 y).mp hyfix
  -- The unique fixed point is `0`, so the norm estimate closes the proof.
  simpa [hy_zero] using
    norm_hardThresholder_le_norm ρ α hα0.le hα1.le x

-- Proof sketch: compare points on opposite sides of the sphere `‖x‖ = ρ`; the jump
-- discontinuity of `hardThresholder ρ α` prevents any `1`-Lipschitz bound when `0 < α < 1`.
/-- Example 4.17 (3): for `0 < α < 1`, the hard thresholder is not nonexpansive. -/
theorem hardThresholder_not_nonexpansive [Nontrivial H]
    (ρ α : ℝ) (hρ : 0 < ρ) (hα0 : 0 < α) (hα1 : α < 1) :
    ¬ LipschitzWith 1 (hardThresholder ρ α : H → H) := by
  intro hLip
  obtain ⟨u, hu⟩ := exists_norm_eq H hρ.le
  let v : H := (1 + α / 2) • u
  have hcoef_pos : 0 < 1 + α / 2 := by
    nlinarith [hα0]
  have hv_branch : ρ < ‖v‖ := by
    dsimp [v]
    rw [norm_smul, Real.norm_of_nonneg hcoef_pos.le, hu]
    nlinarith [hρ, hα0]
  have hu_branch : ¬ ρ < ‖u‖ := by
    rw [hu]
    exact lt_irrefl ρ
  have hTu : hardThresholder ρ α u = 0 := by
    rw [hardThresholder_apply, if_neg hu_branch]
  have hTv : hardThresholder ρ α v = α • v := by
    rw [hardThresholder_apply, if_pos hv_branch]
  have hdist := hLip.dist_le_mul u v
  -- The chosen radial pair crosses the threshold, so the operator jump is too large.
  rw [NNReal.coe_one, one_mul, hTu, hTv, dist_eq_norm, dist_eq_norm] at hdist
  dsimp [v] at hdist ⊢
  rw [zero_sub, norm_neg, norm_smul, Real.norm_of_nonneg hα0.le, norm_smul,
    Real.norm_of_nonneg hcoef_pos.le, hu] at hdist
  have hvu : v - u = (α / 2) • u := by
    calc
      v - u = (1 + α / 2) • u - (1 : ℝ) • u := by
        dsimp [v]
        rw [one_smul]
      _ = ((1 + α / 2) - 1) • u := by rw [← sub_smul]
      _ = (α / 2) • u := by ring_nf
  have huv : u - v = -((α / 2) • u) := by
    rw [show u - v = -(v - u) by abel_nf, hvu]
  rw [huv, norm_neg, norm_smul, Real.norm_of_nonneg (by nlinarith [hα0]), hu] at hdist
  ring_nf at hdist
  nlinarith [hρ, hα0, hα1, hdist]

-- Proof sketch: choose a nonzero vector inside the radius-`ρ` ball and compare it with a fixed
-- point on the sphere of radius `2ρ`; the quasinonexpansive inequality fails when `α = 1`.
/-- Example 4.17 (4): at `α = 1`, the hard thresholder is not quasinonexpansive. -/
theorem hardThresholder_not_quasinonexpansive_at_one [Nontrivial H] (ρ : ℝ) (hρ : 0 < ρ) :
    ¬ QuasinonexpansiveOn (Set.univ : Set H) (hardThresholder ρ 1 : H → H) := by
  intro hQ
  rw [quasinonexpansiveOn_iff] at hQ
  obtain ⟨x, hx⟩ := exists_norm_eq H (show 0 ≤ ρ / 2 by positivity)
  let y : H := (4 : ℝ) • x
  have hx_branch : ¬ ρ < ‖x‖ := by
    rw [hx]
    nlinarith [hρ]
  have hy_branch : ρ < ‖y‖ := by
    dsimp [y]
    rw [norm_smul, Real.norm_of_nonneg (by positivity), hx]
    nlinarith [hρ]
  have hTx : hardThresholder ρ 1 x = 0 := by
    rw [hardThresholder_apply, if_neg hx_branch]
  have hTy : hardThresholder ρ 1 y = y := by
    rw [hardThresholder_apply, if_pos hy_branch]
    simp [y]
  have hineq :=
    hQ x (by simp) y (show y ∈ (Set.univ : Set H) ∩ Function.fixedPoints (hardThresholder ρ 1) by
        refine ⟨by simp, ?_⟩
        rw [Function.mem_fixedPoints_iff]
        exact hTy)
  -- The inside-ball point and the fixed point at radius `2ρ` violate quasinonexpansiveness.
  rw [hTx] at hineq
  dsimp [y] at hineq ⊢
  rw [zero_sub, norm_neg, norm_smul, Real.norm_of_nonneg (by positivity), hx] at hineq
  have hxy : x - y = (-3 : ℝ) • x := by
    calc
      x - y = (1 : ℝ) • x - (4 : ℝ) • x := by
        dsimp [y]
        rw [one_smul]
      _ = ((1 : ℝ) - 4) • x := by rw [← sub_smul]
      _ = (-3 : ℝ) • x := by norm_num
  rw [hxy, norm_smul, hx] at hineq
  norm_num at hineq
  nlinarith [hρ]

-- Proof sketch: rewrite `reflectedSoftThresholder ρ` as `2 * softThresholder ρ - Id` and invoke
-- the reflected-map characterization of firm nonexpansiveness.
/-- Example 4.17 (5): for positive level `ρ`, the operator `T₃` is nonexpansive. -/
theorem reflectedSoftThresholder_nonexpansive [CompleteSpace H] (ρ : ℝ) (hρ : 0 < ρ) :
    LipschitzWith 1 (reflectedSoftThresholder ρ : H → H) := by
  have hsoft :
      LipschitzWith 1 (fun x : H ↦ (2 : ℝ) • softThresholder ρ x - x) :=
    (firmlyNonexpansiveOn_univ_iff_lipschitzWith_one_reflectedMap).mp
      (softThresholder_firmlyNonexpansive ρ hρ)
  convert hsoft using 1
  funext x
  exact reflectedSoftThresholder_eq_reflectedMap_softThresholder ρ x

-- Proof sketch: test the firm inequality on antipodal points with norm `ρ`; the inequality from
-- firm nonexpansiveness fails on this boundary configuration.
/-- Example 4.17 (6): for positive level `ρ`, the operator `T₃` is not firmly nonexpansive. -/
theorem reflectedSoftThresholder_not_firmlyNonexpansive [Nontrivial H] (ρ : ℝ) (hρ : 0 < ρ) :
    ¬ FirmlyNonexpansiveOn (Set.univ : Set H)
      (fun x : Set.univ ↦ (reflectedSoftThresholder ρ : H → H) x) := by
  intro hFirm
  rw [firmlyNonexpansiveOn_univ_iff] at hFirm
  obtain ⟨u, hu⟩ := exists_norm_eq H hρ.le
  have hu_branch : ¬ ρ < ‖u‖ := by
    rw [hu]
    exact lt_irrefl ρ
  have hv_branch : ¬ ρ < ‖-u‖ := by
    rw [norm_neg, hu]
    exact lt_irrefl ρ
  have hTu : reflectedSoftThresholder ρ u = -u := by
    rw [reflectedSoftThresholder_apply, if_neg hu_branch]
  have hTv : reflectedSoftThresholder ρ (-u) = u := by
    rw [reflectedSoftThresholder_apply, if_neg hv_branch]
    simp
  have hineq := hFirm u (-u)
  -- On antipodal boundary points the firm inequality becomes impossible.
  rw [hTu, hTv] at hineq
  have hleft : -u - u = (-2 : ℝ) • u := by
    calc
      -u - u = (-u) + (-u) := by simp [sub_eq_add_neg]
      _ = (-1 : ℝ) • u + (-1 : ℝ) • u := by simp
      _ = (-2 : ℝ) • u := by
        rw [← add_smul]
        norm_num
  have hright : u - (-u) = (2 : ℝ) • u := by
    calc
      u - (-u) = u + u := by simp
      _ = (2 : ℝ) • u := by rw [two_smul]
  rw [hleft, hright, norm_smul, real_inner_smul_left, real_inner_smul_right,
    real_inner_self_eq_norm_sq, hu, pow_two] at hineq
  norm_num at hineq
  nlinarith [hρ]

end

/-! Source item: Chap04/Corollary_4_18 -/


section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable {C : Set 𝓗}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

/-- The canonical metric projection onto `C`, viewed as a map on the subtype `Set.univ`. -/
local notation "P" =>
  fun x : Set.univ ↦
    projectionPoint C
      (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) (x : 𝓗)

/-- Corollary 4.18: if `P` is the canonical metric projection onto a nonempty closed convex subset
`C` of a real Hilbert space, then its residual map `Id - P` is firmly nonexpansive and its
reflector `2P - Id` is nonexpansive. -/
theorem metricProjection_residual_firmlyNonexpansive_and_reflection_nonexpansive
    : FirmlyNonexpansiveOn (Set.univ : Set 𝓗) (residualMap (Set.univ : Set 𝓗) P) ∧
      LipschitzWith 1 (reflectedMap (Set.univ : Set 𝓗) P) := by
  have hP : FirmlyNonexpansiveOn (Set.univ : Set 𝓗) (fun x : Set.univ ↦ P x) := by
    rw [firmlyNonexpansiveOn_iff]
    intro x y
    rw [real_inner_comm]
    exact
      norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex (x : 𝓗) (y : 𝓗)
  have hresidual :
      FirmlyNonexpansiveOn (Set.univ : Set 𝓗) (residualMap (Set.univ : Set 𝓗) P) := by
    exact (firmlyNonexpansiveOn_residualMap_iff (Set.univ : Set 𝓗) P).2 hP
  have hreflect :
      ∀ x y : Set.univ,
        ‖reflectedMap (Set.univ : Set 𝓗) P x - reflectedMap (Set.univ : Set 𝓗) P y‖ ≤
          ‖(x : 𝓗) - y‖ := by
    exact
      (reflectedMap_nonexpansive_iff_firmlyNonexpansiveOn (Set.univ : Set 𝓗) P).2 hP
  refine ⟨hresidual, ?_⟩
  -- Repackage the reflected-map pointwise inequality as a `1`-Lipschitz bound on `Set.univ`.
  refine LipschitzWith.of_dist_le_mul fun x y ↦ ?_
  simpa [Subtype.dist_eq, dist_eq_norm] using hreflect x y

end

/-! Source item: Chap04/Text_4_21_1 -/


section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]
variable {C : Set 𝓗}
variable (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C)

local notation "P" =>
  projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex)

-- Proof sketch: apply the projection characterization from
-- `eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex` to `P x`
-- with test point `P y`, and to `P y` with test point `P x`; adding the resulting inequalities and
-- rearranging yields the displayed firm nonexpansiveness inequality.
/-- Text 4.21.1 (1): the metric projection onto a nonempty closed convex subset of a real Hilbert
space is firmly nonexpansive. -/
theorem firmlyNonexpansive_projectionPoint_of_nonempty_isClosed_convex :
    FirmlyNonexpansive P := by
  rw [firmlyNonexpansive_iff_norm_sq_le_inner]
  intro x y
  exact
    norm_sq_projectionPoint_sub_le_inner_projectionPoint_sub_of_nonempty_isClosed_convex
      hC_nonempty hC_closed hC_convex x y

/-- Helper for Text 4.21.1: every point of `C` is fixed by the metric projection onto `C`. -/
private theorem projectionPoint_eq_self_of_mem_of_nonempty_isClosed_convex {x : 𝓗} (hx : x ∈ C) :
    P x = x := by
  -- The projection characterization is realized by `x` itself because the residual vanishes.
  have hxproj : x = P x := by
    exact
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex).mpr <| by
          refine ⟨hx, ?_⟩
          intro y hy
          simp
  simpa using hxproj.symm

-- Proof sketch: if `x ∈ C`, then the projection of `x` onto `C` is `x` itself because the
-- distance is `0`; conversely, every fixed point of `P` lies in `C` since projection points lie in
-- the target set.
/-- Text 4.21.1 (2): the fixed point set of the metric projection onto `C` is exactly `C`. -/
theorem fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex :
    Function.fixedPoints P = C := by
  ext x
  constructor
  · intro hx
    -- Fixed points belong to `C` because every projection point lies in the target set.
    rw [Function.mem_fixedPoints_iff] at hx
    simpa [hx] using
      projectionPoint_mem C
        (isChebyshev_of_nonempty_isClosed_convex hC_nonempty hC_closed hC_convex) x
  · intro hx
    -- Points already in `C` are fixed by the projection by the helper lemma above.
    rw [Function.mem_fixedPoints_iff]
    exact
      projectionPoint_eq_self_of_mem_of_nonempty_isClosed_convex
        hC_nonempty hC_closed hC_convex hx

-- Proof sketch: rewrite the fixed point set using
-- `fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex` and then use `hC_closed`.
/-- Text 4.21.1 (3): the fixed point set of the metric projection onto `C` is closed. -/
theorem isClosed_fixedPoints_projectionPoint_of_nonempty_isClosed_convex :
    IsClosed (Function.fixedPoints P) := by
  -- Identify the fixed-point set with `C` and inherit closedness from the hypothesis.
  simpa [fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex
    hC_nonempty hC_closed hC_convex] using hC_closed

-- Proof sketch: rewrite the fixed point set using
-- `fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex` and then use `hC_convex`.
/-- Text 4.21.1 (4): the fixed point set of the metric projection onto `C` is convex. -/
theorem convex_fixedPoints_projectionPoint_of_nonempty_isClosed_convex :
    Convex ℝ (Function.fixedPoints P) := by
  -- Identify the fixed-point set with `C` and inherit convexity from the hypothesis.
  simpa [fixedPoints_projectionPoint_eq_of_nonempty_isClosed_convex
    hC_nonempty hC_closed hC_convex] using hC_convex

end

/-! Source item: Chap04/Proposition_4_22 -/


/-- The restricted fixed points of an ambient self-map are exactly its fixed points in `D`. -/
private lemma image_fixedPointsWithin_restrict_eq_fixedPointSetOn
    {H : Type u} {D : Set H} {T : H → H} :
    Subtype.val '' fixedPointsWithin (fun x : D ↦ T x) = fixedPointSetOn D T := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_fixedPointSetOn_iff.mpr ⟨y.2, mem_fixedPointsWithin_iff _ |>.mp hy⟩
  · intro hx
    rcases mem_fixedPointSetOn_iff.mp hx with ⟨hxD, hfix⟩
    exact ⟨⟨x, hxD⟩, mem_fixedPointsWithin_iff _ |>.mpr hfix, rfl⟩

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 4.22: subtracting a point on the segment from `u` rewrites as the
corresponding affine combination of the endpoint residuals. -/
private lemma sub_lineMap_eq_affine_combination_sub (u x y : H) (α : ℝ) :
    u - AffineMap.lineMap x y α = α • (u - y) + (1 - α) • (u - x) := by
  -- Rewrite the difference as a difference of two line maps with the same parameter.
  calc
    u - AffineMap.lineMap x y α = AffineMap.lineMap u u α - AffineMap.lineMap x y α := by
      rw [AffineMap.lineMap_same_apply]
    _ = AffineMap.lineMap (u - x) (u - y) α := by
      simpa using AffineMap.lineMap_vsub_lineMap u u x y α
    _ = α • (u - y) + (1 - α) • (u - x) := by
      -- The vector-valued line map is the usual affine combination of its endpoints.
      simpa [add_comm, add_left_comm, add_assoc] using
        (AffineMap.lineMap_apply_module (u - x) (u - y) α)

/-- Helper for Proposition 4.22: the Corollary 2.15 squared-norm identity for the residual to a
line-map point. -/
private lemma norm_sq_sub_lineMap_add_weighted_norm_sub_sq (u x y : H) (α : ℝ) :
    ‖u - AffineMap.lineMap x y α‖ ^ 2 + α * (1 - α) * ‖x - y‖ ^ 2 =
      α * ‖u - y‖ ^ 2 + (1 - α) * ‖u - x‖ ^ 2 := by
  have hxy : (u - y) - (u - x) = x - y := by
    abel_nf
  have hres :=
    norm_sq_affine_combination_add_weighted_norm_sub_sq (u - y) (u - x) α
  rw [hxy] at hres
  rw [sub_lineMap_eq_affine_combination_sub]
  simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hres

/-- Helper for Proposition 4.22: the squared residual at a point of the segment joining two fixed
points is nonpositive, hence zero. -/
private lemma lineMap_residual_sq_le_zero_of_isQuasinonexpansiveOn
    {D : Set H} (hD_convex : Convex ℝ D) {T : D → H}
    (hT : IsQuasinonexpansiveOn T) {x y : D}
    (hx : x ∈ fixedPointsWithin T) (hy : y ∈ fixedPointsWithin T)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    let z : D := ⟨AffineMap.lineMap (x : H) y α, hD_convex.lineMap_mem x.2 y.2 hα⟩
    ‖T z - z‖ ^ 2 ≤ 0 := by
  dsimp
  let z : D := ⟨AffineMap.lineMap (x : H) y α, hD_convex.lineMap_mem x.2 y.2 hα⟩
  have hxfix : T x = (x : H) := mem_fixedPointsWithin_iff T |>.mp hx
  have hyfix : T y = (y : H) := mem_fixedPointsWithin_iff T |>.mp hy
  have hTx : ‖T z - x‖ ≤ ‖(z : H) - x‖ := by
    simpa [hxfix] using hT z x hxfix
  have hTy : ‖T z - y‖ ≤ ‖(z : H) - y‖ := by
    simpa [hyfix] using hT z y hyfix
  have hTx_sq : ‖T z - x‖ ^ 2 ≤ ‖(z : H) - x‖ ^ 2 := by
    exact sq_le_sq.mpr <| by
      simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using hTx
  have hTy_sq : ‖T z - y‖ ^ 2 ≤ ‖(z : H) - y‖ ^ 2 := by
    exact sq_le_sq.mpr <| by
      simpa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] using hTy
  have hcompare :
      ‖T z - z‖ ^ 2 + α * (1 - α) * ‖(x : H) - y‖ ^ 2 ≤
        α * ‖(z : H) - y‖ ^ 2 + (1 - α) * ‖(z : H) - x‖ ^ 2 := by
    rw [show ‖T z - z‖ ^ 2 + α * (1 - α) * ‖(x : H) - y‖ ^ 2 =
        α * ‖T z - y‖ ^ 2 + (1 - α) * ‖T z - x‖ ^ 2 by
        simpa [z] using norm_sq_sub_lineMap_add_weighted_norm_sub_sq (T z) (x : H) y α]
    nlinarith [hTy_sq, hTx_sq, hα.1, hα.2]
  have hzero :
      α * ‖(z : H) - y‖ ^ 2 + (1 - α) * ‖(z : H) - x‖ ^ 2 =
        α * (1 - α) * ‖(x : H) - y‖ ^ 2 := by
    have hz_eq := norm_sq_sub_lineMap_add_weighted_norm_sub_sq (z : H) (x : H) y α
    simpa [z] using hz_eq.symm
  nlinarith [hcompare, hzero]

/-- Helper for Proposition 4.22: every point of the segment joining two fixed points is again a
fixed point of the restricted map. -/
private lemma lineMap_mem_fixedPointsWithin_of_isQuasinonexpansiveOn
    {D : Set H} (hD_convex : Convex ℝ D) {T : D → H}
    (hT : IsQuasinonexpansiveOn T) {x y : D}
    (hx : x ∈ fixedPointsWithin T) (hy : y ∈ fixedPointsWithin T)
    {α : ℝ} (hα : α ∈ Set.Icc (0 : ℝ) 1) :
    (⟨AffineMap.lineMap (x : H) y α, hD_convex.lineMap_mem x.2 y.2 hα⟩ : D) ∈
      fixedPointsWithin T := by
  let z : D := ⟨AffineMap.lineMap (x : H) y α, hD_convex.lineMap_mem x.2 y.2 hα⟩
  have hsq : ‖T z - z‖ ^ 2 ≤ 0 := by
    simpa [z] using
      lineMap_residual_sq_le_zero_of_isQuasinonexpansiveOn hD_convex hT hx hy hα
  have hsq_eq : ‖T z - z‖ ^ 2 = 0 := le_antisymm hsq (sq_nonneg _)
  have hnorm_eq : ‖T z - z‖ = 0 := sq_eq_zero_iff.mp hsq_eq
  exact mem_fixedPointsWithin_iff T |>.mpr <| sub_eq_zero.mp (norm_eq_zero.mp hnorm_eq)

-- Proof sketch: if `x` and `y` are fixed points of `T : D → H`, the convexity of `D` puts every
-- segment point back in `D`. Applying quasinonexpansiveness relative to the fixed endpoints and
-- the Hilbert-space identity from Corollary 2.15 forces the residual there to vanish, so the
-- segment stays in the fixed-point set.
/-- Helper for Proposition 4.22: the ambient image of the fixed-point set of a quasinonexpansive
map on a convex domain is convex. -/
private lemma convex_image_fixedPointsWithin_of_isQuasinonexpansiveOn
    {D : Set H} (hD_convex : Convex ℝ D) {T : D → H}
    (hT : IsQuasinonexpansiveOn T) :
    Convex ℝ (Subtype.val '' fixedPointsWithin T : Set H) := by
  rw [convex_iff_add_mem]
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨x', hx', rfl⟩
  rcases hy with ⟨y', hy', rfl⟩
  have hb_one : b ≤ (1 : ℝ) := by
    linarith
  let z : D := ⟨AffineMap.lineMap (x' : H) y' b, hD_convex.lineMap_mem x'.2 y'.2 ⟨hb, hb_one⟩⟩
  have hz : z ∈ fixedPointsWithin T := by
    simpa [z] using
      lineMap_mem_fixedPointsWithin_of_isQuasinonexpansiveOn hD_convex hT hx' hy' ⟨hb, hb_one⟩
  refine ⟨z, hz, ?_⟩
  have ha_eq : a = 1 - b := by
    linarith
  rw [ha_eq]
  simp [z, AffineMap.lineMap_apply_module, add_comm]

/-- Proposition 4.22: if `D` is a nonempty convex subset of a real Hilbert space and `T`
is quasinonexpansive on `D`, then the fixed-point set of `T` in `D` is convex. -/
theorem convex_fixedPointSetOn_of_quasinonexpansiveOn
    {D : Set H} (hD : D.Nonempty) (hD_convex : Convex ℝ D) {T : H → H}
    (hT : QuasinonexpansiveOn D T) :
    Convex ℝ (fixedPointSetOn D T) := by
  let _ : D.Nonempty := hD
  let S : D → H := fun x ↦ T x
  have hS : IsQuasinonexpansiveOn S := by
    rw [isQuasinonexpansiveOn_iff]
    intro x y hy
    have hy' : (y : H) ∈ fixedPointSetOn D T := by
      exact mem_fixedPointSetOn_iff.mpr ⟨y.2, hy⟩
    simpa [S] using (quasinonexpansiveOn_iff.mp hT) x x.2 y hy'
  simpa [S, image_fixedPointsWithin_restrict_eq_fixedPointSetOn] using
    convex_image_fixedPointsWithin_of_isQuasinonexpansiveOn hD_convex hS

end

/-! Source item: Chap04/Proposition_4_23 -/


section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H} {T : H → H}

/- The residual half-space inequality is equivalent to the squared norm comparison that appears
in quasinonexpansiveness. -/
private lemma inner_sub_image_le_half_residual_sq_iff_norm_image_sub_sq_le (x y z : H) :
    ⟪z - y, x - y⟫_ℝ ≤ (1 / 2 : ℝ) * ‖y - x‖ ^ 2 ↔ ‖y - z‖ ^ 2 ≤ ‖x - z‖ ^ 2 := by
  let a : H := y - z
  let b : H := x - z
  have hxy : x - y = b - a := by
    simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have hyx : y - x = a - b := by
    simp [a, b, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  -- Rewrite the displayed inequality in terms of the canonical residual vectors `a` and `b`.
  have hinner :
      ⟪z - y, x - y⟫_ℝ = ‖a‖ ^ 2 - ⟪a, b⟫_ℝ := by
    rw [show z - y = -a by simp [a], hxy, inner_neg_left, inner_sub_right,
      real_inner_self_eq_norm_sq]
    ring
  have hnorm :
      ‖y - x‖ ^ 2 = ‖a‖ ^ 2 - 2 * ⟪a, b⟫_ℝ + ‖b‖ ^ 2 := by
    rw [hyx]
    simpa using norm_sub_sq_real a b
  have hyz : ‖y - z‖ ^ 2 = ‖a‖ ^ 2 := by
    simp [a]
  have hxz : ‖x - z‖ ^ 2 = ‖b‖ ^ 2 := by
    simp [b]
  constructor <;> intro h
  · -- After the quadratic expansions, the half-space inequality rearranges to the norm bound.
    nlinarith [h, hinner, hnorm, hyz, hxz]
  · -- The converse direction is the same real-algebra calculation in reverse.
    nlinarith [h, hinner, hnorm, hyz, hxz]

/- Each residual half-space section is closed when `D` is closed. -/
private lemma halfspace_section_isClosed (hD_closed : IsClosed D) (x : H) :
    IsClosed
      {y : H | y ∈ D ∧ ⟪y - T x, x - T x⟫_ℝ ≤ (1 / 2 : ℝ) * ‖T x - x‖ ^ 2} := by
  -- The defining scalar functional is continuous, so its sublevel set is closed.
  have hcont : Continuous fun y : H ↦ ⟪y - T x, x - T x⟫_ℝ := by
    fun_prop
  simpa [Set.setOf_and] using
    hD_closed.inter (isClosed_le hcont continuous_const)

-- Proof sketch: for `y ∈ D ∩ Function.fixedPoints T`, use quasinonexpansiveness and expand
-- `‖x - y‖^2 - ‖T x - y‖^2` to obtain the half-space inequality for every `x ∈ D`; conversely,
-- if `y` lies in every such half-space, substitute `x = y` and use `y ∈ D` to force `T y = y`.
/-- Proposition 4.23 (1): if `D` is nonempty and `T` is quasinonexpansive on `D`, then the fixed
point set of `T` in `D` is the intersection, over `x ∈ D`, of the half-spaces
`{y ∈ D | ⟪y - T x, x - T x⟫_ℝ ≤ (1 / 2) ‖T x - x‖^2}`. -/
theorem fixedPointSetOn_eq_iInter_halfspaces_of_quasinonexpansive
    (hD : D.Nonempty) (hT : QuasinonexpansiveOn D T) :
    fixedPointSetOn D T =
      ⋂ x ∈ D, {y : H | y ∈ D ∧ ⟪y - T x, x - T x⟫_ℝ ≤ (1 / 2 : ℝ) * ‖T x - x‖ ^ 2} := by
  rw [quasinonexpansiveOn_iff] at hT
  ext y
  constructor
  · intro hy
    rcases mem_fixedPointSetOn_iff.mp hy with ⟨hyD, _⟩
    refine Set.mem_iInter.2 fun x ↦ Set.mem_iInter.2 fun hx ↦ ?_
    refine ⟨hyD, ?_⟩
    -- Square the quasinonexpansive estimate and rewrite it via the quadratic helper.
    have hsq : ‖T x - y‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by
      have hle : ‖T x - y‖ ≤ ‖x - y‖ := hT x hx y hy
      exact sq_le_sq.mpr <| by
        simpa [abs_of_nonneg (norm_nonneg (T x - y)), abs_of_nonneg (norm_nonneg (x - y))] using
          hle
    exact
      (inner_sub_image_le_half_residual_sq_iff_norm_image_sub_sq_le x (T x) y).2 hsq
  · intro hy
    rcases hD with ⟨x0, hx0⟩
    have hyD : y ∈ D := by
      exact (Set.mem_iInter.1 (Set.mem_iInter.1 hy x0) hx0).1
    have hySection :
        ⟪y - T y, y - T y⟫_ℝ ≤ (1 / 2 : ℝ) * ‖T y - y‖ ^ 2 := by
      exact (Set.mem_iInter.1 (Set.mem_iInter.1 hy y) hyD).2
    -- Evaluating the section condition at `x = y` forces the residual norm to vanish.
    have hsq : ‖T y - y‖ ^ 2 ≤ ‖y - y‖ ^ 2 := by
      exact
        (inner_sub_image_le_half_residual_sq_iff_norm_image_sub_sq_le y (T y) y).1 hySection
    have hsq' : ‖T y - y‖ ^ 2 ≤ 0 := by
      simpa using hsq
    have hzero : ‖T y - y‖ = 0 := by
      nlinarith [sq_nonneg ‖T y - y‖, hsq']
    have hfix : T y = y := by
      exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
    exact mem_fixedPointSetOn_iff.mpr ⟨hyD, hfix⟩

-- Proof sketch: rewrite `fixedPointSetOn D T` using the characterization in
-- `fixedPointSetOn_eq_iInter_halfspaces_of_quasinonexpansive`; each half-space cut out by a
-- continuous affine functional is closed, and intersections of closed sets remain closed.
/-- Proposition 4.23 (2): if `T` is quasinonexpansive on a closed convex set `D`, then its fixed
point set in `D` is closed and convex. -/
theorem isClosed_and_convex_fixedPointSetOn_of_quasinonexpansive
    (hT : QuasinonexpansiveOn D T)
    (hD_closed : IsClosed D) (hD_convex : Convex ℝ D) :
    IsClosed (fixedPointSetOn D T) ∧ Convex ℝ (fixedPointSetOn D T) := by
  constructor
  · by_cases hDn : D.Nonempty
    · rw [fixedPointSetOn_eq_iInter_halfspaces_of_quasinonexpansive hDn hT]
      exact isClosed_iInter fun x ↦
        isClosed_iInter fun hx ↦ halfspace_section_isClosed hD_closed x
    · have hD_empty : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hDn
      simp [hD_empty, fixedPointSetOn]
  · by_cases hDn : D.Nonempty
    · exact convex_fixedPointSetOn_of_quasinonexpansiveOn hDn hD_convex hT
    · have hD_empty : D = ∅ := Set.not_nonempty_iff_eq_empty.mp hDn
      simpa [hD_empty, fixedPointSetOn] using (convex_empty : Convex ℝ (∅ : Set H))

end

/-! Source item: Chap04/Corollary_4_24 -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Corollary 4.24: if `D` is a nonempty closed convex subset of a real inner product space and
`T` is
nonexpansive on `D`, then the fixed point set `Fix T = {x ∈ D | T x = x}` is closed and convex. -/
theorem isClosed_and_convex_fixedPointSet_of_nonexpansiveOn
    {D : Set H} (_hD_nonempty : D.Nonempty) (hD_closed : IsClosed D) (hD_convex : Convex ℝ D)
    {T : H → H} (hT : LipschitzOnWith 1 T D) :
    IsClosed (fixedPointSetOn D T) ∧ Convex ℝ (fixedPointSetOn D T) := by
  exact
    isClosed_and_convex_fixedPointSetOn_of_quasinonexpansive
      (LipschitzOnWith.quasinonexpansiveOn hT) hD_closed hD_convex

end

/-! Source item: Chap04/Corollary_4_25 -/


section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {D : Set H} {T : H → H}

private lemma fixedPointSetOn_reflected_eq (D : Set H) (T : H → H) :
    fixedPointSetOn D (fun x ↦ (2 : ℝ) • T x - x) = fixedPointSetOn D T := by
  ext y
  rw [mem_fixedPointSetOn_iff, mem_fixedPointSetOn_iff]
  constructor
  · rintro ⟨hyD, hyfix⟩
    refine ⟨hyD, ?_⟩
    change (2 : ℝ) • T y - y = y at hyfix
    have hzero : (2 : ℝ) • (T y - y) = 0 := by
      calc
        (2 : ℝ) • (T y - y) = (2 : ℝ) • T y - (2 : ℝ) • y := by
          rw [smul_sub]
        _ = ((2 : ℝ) • T y - y) - y := by
          simp [two_smul, sub_eq_add_neg, add_assoc]
        _ = 0 := by
          rw [hyfix, sub_self]
    rcases smul_eq_zero.mp hzero with htwo | hsub
    · norm_num at htwo
    · exact sub_eq_zero.mp hsub
  · rintro ⟨hyD, hyfix⟩
    refine ⟨hyD, ?_⟩
    change (2 : ℝ) • T y - y = y
    rw [hyfix]
    simp [two_smul]

private lemma reflected_map_quasinonexpansiveOn (D : Set H) (T : H → H)
    (hT : FirmlyQuasinonexpansiveOn D T) :
    QuasinonexpansiveOn D (fun x ↦ (2 : ℝ) • T x - x) := by
  rw [firmlyQuasinonexpansiveOn_iff] at hT
  rw [quasinonexpansiveOn_iff]
  intro x hx y hy
  have hy' : y ∈ fixedPointSetOn D T := by
    simpa [fixedPointSetOn_reflected_eq D T] using hy
  have hfirm := hT x hx y hy'
  let a : H := T x - y
  let b : H := x - T x
  have hsquare : ‖a‖ ^ 2 ≤ ‖b + a‖ ^ 2 - ‖b‖ ^ 2 := by
    have hxy : ‖b + a‖ ^ 2 = ‖x - y‖ ^ 2 := by
      change ‖(x - T x) + (T x - y)‖ ^ 2 = ‖x - y‖ ^ 2
      abel_nf
    have hb : ‖b‖ ^ 2 = ‖T x - x‖ ^ 2 := by
      simp [b, norm_sub_rev]
    have ha : ‖a‖ ^ 2 = ‖T x - y‖ ^ 2 := by
      simp [a]
    nlinarith [hfirm, hxy, hb, ha]
  have hinner_nonneg : 0 ≤ ⟪b, a⟫_ℝ := by
    rw [norm_add_sq_real] at hsquare
    nlinarith
  have hsq : ‖a - b‖ ^ 2 ≤ ‖b + a‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_add_sq_real]
    nlinarith [hinner_nonneg, real_inner_comm b a]
  have hnorm : ‖a - b‖ ≤ ‖b + a‖ := by
    nlinarith [hsq, norm_nonneg (a - b), norm_nonneg (b + a)]
  simpa [a, b, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_smul] using hnorm

private lemma reflected_halfspace_iff_inner_nonpos (T : H → H) (x y : H) :
    ⟪y - ((2 : ℝ) • T x - x), x - ((2 : ℝ) • T x - x)⟫_ℝ
        ≤ (1 / 2 : ℝ) * ‖((2 : ℝ) • T x - x) - x‖ ^ 2 ↔
      ⟪y - T x, x - T x⟫_ℝ ≤ 0 := by
  let z : H := x - T x
  have hxR : x - ((2 : ℝ) • T x - x) = (2 : ℝ) • z := by
    simp [z, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_smul]
  have hyR : y - ((2 : ℝ) • T x - x) = (y - T x) + z := by
    simp [z, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_smul]
  have hRx : ((2 : ℝ) • T x - x) - x = (-2 : ℝ) • z := by
    simp [z, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, two_smul]
  rw [hyR, hxR, hRx]
  rw [inner_add_left, inner_smul_right, inner_smul_right, real_inner_self_eq_norm_sq]
  rw [norm_smul]
  simp only [Real.norm_eq_abs, abs_neg, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  ring_nf
  constructor
  · intro h
    nlinarith [sq_nonneg ‖z‖]
  · intro h
    nlinarith [sq_nonneg ‖z‖]

/-- Corollary 4.25: if `D` is a nonempty subset of a real Hilbert space and `T` is firmly
quasinonexpansive on `D`, then the fixed points of `T` in `D` are exactly the intersection of the
half-spaces `{y ∈ D | ⟪y - T x, x - T x⟫_ℝ ≤ 0}` over all `x ∈ D`. -/
theorem fixedPointSetOn_eq_iInter_inner_nonpos_of_firmlyQuasinonexpansive
    (hD : D.Nonempty) (hT : FirmlyQuasinonexpansiveOn D T) :
    fixedPointSetOn D T =
      ⋂ x ∈ D, {y : H | y ∈ D ∧ ⟪y - T x, x - T x⟫_ℝ ≤ 0} := by
  let R : H → H := fun x ↦ (2 : ℝ) • T x - x
  have hRqne : QuasinonexpansiveOn D R := by
    simpa [R] using reflected_map_quasinonexpansiveOn D T hT
  have hR :
      fixedPointSetOn D R =
        ⋂ x ∈ D, {y : H | y ∈ D ∧ ⟪y - R x, x - R x⟫_ℝ ≤ (1 / 2 : ℝ) * ‖R x - x‖ ^ 2} := by
    exact fixedPointSetOn_eq_iInter_halfspaces_of_quasinonexpansive hD hRqne
  have hHalf :
      (⋂ x ∈ D, {y : H | y ∈ D ∧ ⟪y - R x, x - R x⟫_ℝ ≤ (1 / 2 : ℝ) * ‖R x - x‖ ^ 2}) =
        ⋂ x ∈ D, {y : H | y ∈ D ∧ ⟪y - T x, x - T x⟫_ℝ ≤ 0} := by
    ext y
    simp only [mem_iInter, mem_setOf_eq]
    constructor
    · intro hy x hx
      exact ⟨(hy x hx).1, (reflected_halfspace_iff_inner_nonpos T x y).mp (hy x hx).2⟩
    · intro hy x hx
      exact ⟨(hy x hx).1, (reflected_halfspace_iff_inner_nonpos T x y).mpr (hy x hx).2⟩
  calc
    fixedPointSetOn D T = fixedPointSetOn D R := by
      rw [fixedPointSetOn_reflected_eq D T]
    _ = ⋂ x ∈ D, {y : H | y ∈ D ∧ ⟪y - R x, x - R x⟫_ℝ ≤ (1 / 2 : ℝ) * ‖R x - x‖ ^ 2} := hR
    _ = ⋂ x ∈ D, {y : H | y ∈ D ∧ ⟪y - T x, x - T x⟫_ℝ ≤ 0} := hHalf

end


/-! Source item: Bauschke-lean-project/BauschkeLean/Chap05/Example_5_18 -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Example 5.18: firmly nonexpansive self-maps are `1`-Lipschitz. -/
lemma lipschitzWith_one_of_firmlyNonexpansive {T : H → H} (hT : FirmlyNonexpansive T) :
    LipschitzWith 1 T := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro x y
  rw [dist_eq_norm, dist_eq_norm]
  by_cases hxy : T x = T y
  · simp [hxy]
  · have hfirm :
        ‖T x - T y‖ ^ 2 ≤ inner ℝ (T x - T y) (x - y) := by
        simpa using (firmlyNonexpansive_iff_norm_sq_le_inner.mp hT) x y
    have hmul :
        ‖T x - T y‖ * ‖T x - T y‖ ≤ ‖T x - T y‖ * ‖x - y‖ := by
      simpa [pow_two] using le_trans hfirm (real_inner_le_norm (T x - T y) (x - y))
    have hnorm_pos : 0 < ‖T x - T y‖ := by
      refine norm_pos_iff.mpr ?_
      exact sub_ne_zero.mpr hxy
    simpa using (le_of_mul_le_mul_left hmul hnorm_pos)

/-- Helper for Example 5.18: firm nonexpansiveness yields the one-step squared-distance decrease
against every fixed point. -/
lemma sq_dist_image_fixedPoint_add_sq_residual_le_of_firmlyNonexpansive
    {T : H → H} (hT : FirmlyNonexpansive T) {x z : H} (hz : T z = z) :
    ‖T x - z‖ ^ 2 + ‖T x - x‖ ^ 2 ≤ ‖x - z‖ ^ 2 := by
  have hfirm : ‖T x - z‖ ^ 2 ≤ inner ℝ (T x - z) (x - z) := by
    simpa [hz] using (firmlyNonexpansive_iff_norm_sq_le_inner.mp hT) x z
  have hcross_nonneg : 0 ≤ inner ℝ (T x - z) (x - T x) := by
    have hsplit :
        inner ℝ (T x - z) (x - z) =
          ‖T x - z‖ ^ 2 + inner ℝ (T x - z) (x - T x) := by
      calc
        inner ℝ (T x - z) (x - z) =
            inner ℝ (T x - z) ((T x - z) + (x - T x)) := by
              congr 2
              abel_nf
        _ = inner ℝ (T x - z) (T x - z) + inner ℝ (T x - z) (x - T x) := by
              rw [inner_add_right]
        _ = ‖T x - z‖ ^ 2 + inner ℝ (T x - z) (x - T x) := by
              rw [real_inner_self_eq_norm_sq]
    nlinarith [hfirm, hsplit]
  have hexpand :
      ‖x - z‖ ^ 2 =
        ‖x - T x‖ ^ 2 + 2 * inner ℝ (x - T x) (T x - z) + ‖T x - z‖ ^ 2 := by
    calc
      ‖x - z‖ ^ 2 = ‖(x - T x) + (T x - z)‖ ^ 2 := by
        congr 1
        abel_nf
      _ = ‖x - T x‖ ^ 2 + 2 * inner ℝ (x - T x) (T x - z) + ‖T x - z‖ ^ 2 := by
        simpa using norm_add_sq_real (x - T x) (T x - z)
  have hres : ‖x - T x‖ ^ 2 = ‖T x - x‖ ^ 2 := by
    rw [norm_sub_rev]
  have hcross_nonneg' : 0 ≤ inner ℝ (x - T x) (T x - z) := by
    simpa [real_inner_comm] using hcross_nonneg
  nlinarith [hcross_nonneg', hexpand, hres]

end

/-! Source item: Attouch_Asymptotic_behavior_of_Newton_like_inertial_dynamics_involving_the_sum_of_potential_and_nonpotential_terms_2021 items/lem_2 -/

/-- A weighted squared-norm estimate for the sum of two vectors. -/
theorem weighted_norm_add_sq_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (l₁ l₂ : ℝ) (hl₁ : 0 < l₁) (hl₂ : 0 < l₂) (u v : H) :
    l₁ * l₂ * ‖u + v‖ ^ 2 ≤ (l₁ + l₂) * (l₁ * ‖u‖ ^ 2 + l₂ * ‖v‖ ^ 2) := by
  have hsq : 0 ≤ ‖l₁ • u - l₂ • v‖ ^ 2 := sq_nonneg _
  rw [norm_sub_sq_real, norm_smul, norm_smul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hl₁, abs_of_pos hl₂] at hsq
  rw [real_inner_smul_left, real_inner_smul_right] at hsq
  rw [norm_add_sq_real]
  nlinarith

/-- Lemma A.1: the sum of two cocoercive maps has harmonic cocoercivity coefficient. -/
theorem cocoercive_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T₁ T₂ : H → H) (l₁ l₂ : ℝ) (hl₁ : 0 < l₁) (hl₂ : 0 < l₂)
    (hT₁ : CocoerciveOn l₁ Set.univ (fun x : Set.univ => T₁ x))
    (hT₂ : CocoerciveOn l₂ Set.univ (fun x : Set.univ => T₂ x)) :
    CocoerciveOn (l₁ * l₂ / (l₁ + l₂)) Set.univ (fun x : Set.univ => T₁ x + T₂ x) := by
  have hsum_pos : 0 < l₁ + l₂ := add_pos hl₁ hl₂
  have hcoef_pos : 0 < l₁ * l₂ / (l₁ + l₂) :=
    div_pos (mul_pos hl₁ hl₂) hsum_pos
  apply (CocoerciveOn.pointwise_iff (fun x => T₁ x + T₂ x) _ hcoef_pos).mpr
  intro x y
  let u := T₁ y - T₁ x
  let v := T₂ y - T₂ x
  let d := y - x
  have hu : l₁ * ‖u‖ ^ 2 ≤ inner ℝ u d := by
    simpa only [u, d] using (CocoerciveOn.pointwise_iff T₁ l₁ hl₁).mp hT₁ x y
  have hv : l₂ * ‖v‖ ^ 2 ≤ inner ℝ v d := by
    simpa only [v, d] using (CocoerciveOn.pointwise_iff T₂ l₂ hl₂).mp hT₂ x y
  have hsum_coco : l₁ * ‖u‖ ^ 2 + l₂ * ‖v‖ ^ 2 ≤ inner ℝ (u + v) d := by
    rw [inner_add_left]
    linarith
  have hweighted := weighted_norm_add_sq_le l₁ l₂ hl₁ hl₂ u v
  have hdiv : (l₁ * l₂ / (l₁ + l₂)) * ‖u + v‖ ^ 2 ≤
      l₁ * ‖u‖ ^ 2 + l₂ * ‖v‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hsum_pos).mpr
    nlinarith [hweighted]
  have hinc : (T₁ y + T₂ y) - (T₁ x + T₂ x) = u + v := by
    dsimp [u, v]
    abel
  rw [hinc]
  exact hdiv.trans hsum_coco

/-! Source item: Attouch_AitMansour_Mazgouri_Monotone_stability_2024 items/def_1 -/

/-- A single-valued map `A : H → H` is monotone if `⟪A u - A v, u - v⟫ ≥ 0` for all `u, v ∈ H`. -/
def IsMonotone {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (A : H → H) : Prop :=
  ∀ u v : H, 0 ≤ inner ℝ (A u - A v) (u - v)

/-- A map `A : H → H` is `m`-strongly monotone (`m > 0`) if
  `m ‖u - v‖² ≤ ⟪A u - A v, u - v⟫` for all `u, v ∈ H`. -/
def IsStronglyMonotone {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → H) (m : ℝ) : Prop :=
  0 < m ∧ ∀ u v : H, m * ‖u - v‖ ^ 2 ≤ inner ℝ (A u - A v) (u - v)

/-- If `A` is `m`-strongly monotone and `L`-Lipschitz continuous (in the real
  readback `LipschitzWith (Real.toNNReal L)` of the real constant `L`), then `m ≤ L`. -/
theorem stronglyMonotone_lipschitz_implies_m_le_L {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [Nontrivial H] (A : H → H) (m L : ℝ)
    (hsm : IsStronglyMonotone A m) (hlip : LipschitzWith (Real.toNNReal L) A) : m ≤ L := by
  by_cases hL : 0 ≤ L
  · obtain ⟨x, hx⟩ := exists_ne (0 : H)
    have hsmx : m * ‖x‖ ^ 2 ≤ inner ℝ (A x - A 0) x := by
      simpa using hsm.2 x 0
    have hlipx : ‖A x - A 0‖ ≤ L * ‖x‖ := by
      have h := hlip.dist_le_mul x 0
      simpa [dist_eq_norm, norm_sub_rev, Real.coe_toNNReal L hL] using h
    have hbound : m * ‖x‖ ^ 2 ≤ L * ‖x‖ ^ 2 := by
      calc
        m * ‖x‖ ^ 2 ≤ inner ℝ (A x - A 0) x := hsmx
        _ ≤ ‖A x - A 0‖ * ‖x‖ := real_inner_le_norm _ _
        _ ≤ (L * ‖x‖) * ‖x‖ := mul_le_mul_of_nonneg_right hlipx (norm_nonneg x)
        _ = L * ‖x‖ ^ 2 := by ring
    exact le_of_mul_le_mul_right hbound (pow_pos (norm_pos_iff.mpr hx) 2)
  · obtain ⟨x, hx⟩ := exists_ne (0 : H)
    have hzero : (Real.toNNReal L : ℝ) = 0 := by
      rw [Real.toNNReal_of_nonpos (le_of_lt (lt_of_not_ge hL))]
      norm_num
    have hsmx : m * ‖x‖ ^ 2 ≤ inner ℝ (A x - A 0) x := by
      simpa using hsm.2 x 0
    have hb : inner ℝ (A x - A 0) x ≤ 0 := by
      have h := hlip.dist_le_mul x 0
      have hlipx : ‖A x - A 0‖ ≤ 0 := by
        simpa [dist_eq_norm, norm_sub_rev, hzero] using h
      have hnorm0 : ‖A x - A 0‖ = 0 := le_antisymm hlipx (norm_nonneg _)
      simpa [hnorm0] using (real_inner_le_norm (A x - A 0) x)
    have hpos : 0 < m * ‖x‖ ^ 2 := mul_pos hsm.1 (pow_pos (norm_pos_iff.mpr hx) 2)
    linarith

/-- Every `β`-cocoercive operator is `1/β`-Lipschitz continuous (in the real
  readback `LipschitzWith (Real.toNNReal (1 / β))` of the real constant `1/β`). -/
theorem cocoercive_implies_lipschitz {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (A : H → H) (β : ℝ) (hc : CocoerciveOn β Set.univ (fun x : Set.univ => A x)) :
    LipschitzWith (Real.toNNReal (1 / β)) A := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro u v
  have hcoco : β * ‖A u - A v‖ ^ 2 ≤ inner ℝ (A u - A v) (u - v) :=
    (CocoerciveOn.pointwise_iff A β hc.1).mp hc v u
  have hprod : β * ‖A u - A v‖ ^ 2 ≤ ‖A u - A v‖ * ‖u - v‖ := by
    calc
      β * ‖A u - A v‖ ^ 2 ≤ inner ℝ (A u - A v) (u - v) := hcoco
      _ ≤ ‖A u - A v‖ * ‖u - v‖ := real_inner_le_norm _ _
  by_cases huv : A u = A v
  · rw [huv, dist_self]
    exact mul_nonneg (NNReal.coe_nonneg _) dist_nonneg
  · have hmul : β * ‖A u - A v‖ ≤ ‖u - v‖ := by
      apply le_of_mul_le_mul_right (a := ‖A u - A v‖) _ (norm_pos_iff.mpr (sub_ne_zero.mpr huv))
      simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hprod
    have hlip : ‖A u - A v‖ ≤ (1 / β) * ‖u - v‖ := by
      calc
        ‖A u - A v‖ ≤ ‖u - v‖ / β := (le_div_iff₀ hc.1).mpr (by simpa [mul_comm] using hmul)
        _ = (1 / β) * ‖u - v‖ := by ring
    rw [Real.coe_toNNReal (1 / β) (one_div_nonneg.mpr hc.1.le)]
    simpa [dist_eq_norm] using hlip

/-- Strong monotonicity controls the distance between two points by the difference of the
  operator values: the `μ`-strong-monotonicity inequality `μ ‖y - z‖² ≤ ⟪A y - A z, y - z⟫`
  (for any real `μ`, no positivity hypothesis needed) implies `μ ‖y - z‖ ≤ ‖A y - A z‖`. -/
theorem distance_le_grad_difference_of_strong_monotone
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (grad : E → E) (μ : ℝ) (y z : E)
    (hmono : μ * ‖y - z‖ ^ 2 ≤ inner ℝ (grad y - grad z) (y - z)) :
    μ * ‖y - z‖ ≤ ‖grad y - grad z‖ := by
  by_cases hyz : y = z
  · simp [hyz]
  have hnorm : 0 < ‖y - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyz)
  refine le_of_mul_le_mul_right ?_ hnorm
  calc
    (μ * ‖y - z‖) * ‖y - z‖ = μ * ‖y - z‖ ^ 2 := by ring
    _ ≤ inner ℝ (grad y - grad z) (y - z) := hmono
    _ ≤ ‖grad y - grad z‖ * ‖y - z‖ := real_inner_le_norm _ _

/-! Source item: Attouch_AitMansour_Mazgouri_Monotone_stability_2024 items/ext_thm_4 -/

/-- The first-order supporting-hyperplane estimate for a convex differentiable
  function: `f z + ⟪grad z, u - z⟫ ≤ f u`. -/
theorem convex_supporting_baillon_haddad {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → ℝ) (grad : H → H)
    (hconvex : ConvexOn ℝ Set.univ f) (hgrad : ∀ z, HasGradientAt f (grad z) z)
    (z u : H) :
    f z + inner ℝ (grad z) (u - z) ≤ f u := by
  let φ : ℝ → ℝ := f ∘ AffineMap.lineMap z u
  have hφconvex : ConvexOn ℝ Set.univ φ := by
    simpa [φ] using hconvex.comp_affineMap (AffineMap.lineMap z u)
  have hpath : HasDerivAt (fun t : ℝ ↦ z + t • (u - z)) (u - z) 0 := by
    convert (hasDerivAt_const (𝕜 := ℝ) 0 z).add
      ((hasDerivAt_id (𝕜 := ℝ) 0).smul_const (u - z)) using 1
    all_goals simp
  have houter : HasFDerivAt f (InnerProductSpace.toDual ℝ H (grad z))
      ((fun t : ℝ ↦ z + t • (u - z)) 0) := by
    simpa using (hgrad z).hasFDerivAt
  have hφderiv : HasDerivAt φ (inner ℝ (grad z) (u - z)) 0 := by
    simpa [φ, Function.comp_def, AffineMap.lineMap_apply, add_comm, one_smul, add_zero,
      InnerProductSpace.toDual_apply_apply] using
      HasFDerivAt.comp_hasDerivAt 0 houter hpath
  have hslope := hφconvex.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one hφderiv
  have : inner ℝ (grad z) (u - z) ≤ f u - f z := by
    simpa [φ, slope, Function.comp_def, AffineMap.lineMap_apply, zero_smul, one_smul,
      zero_add, add_zero] using hslope
  linarith

/-- The quadratic upper bound of a function with `L`-Lipschitz gradient:
  `f u ≤ f z + ⟪grad z, u - z⟫ + (L / 2) ‖u - z‖²`. -/
theorem smoothness_baillon_haddad {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] (f : H → ℝ) (grad : H → H) (L : NNReal)
    (hgrad : ∀ z, HasGradientAt f (grad z) z) (hlip : LipschitzWith L grad) (z u : H) :
    f u ≤ f z + inner ℝ (grad z) (u - z) + ((L : ℝ) / 2) * ‖u - z‖ ^ 2 := by
  let φ : ℝ → ℝ := fun t ↦ f (AffineMap.lineMap z u t)
  let ψ : ℝ → ℝ := fun t ↦ inner ℝ (grad (AffineMap.lineMap z u t)) (u - z)
  let ρ : ℝ → ℝ := fun t ↦ inner ℝ (grad (AffineMap.lineMap z u t) - grad z) (u - z)
  have hψ_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt φ (ψ t) t := by
    intro t _
    simpa [φ, ψ, InnerProductSpace.toDual_apply_apply, real_inner_comm] using
      (hgrad (AffineMap.lineMap z u t)).hasFDerivAt.comp_hasDerivAt t
        (AffineMap.hasDerivAt (AffineMap.lineMap z u))
  have hgradCont : ContinuousOn (fun t : ℝ ↦ grad (AffineMap.lineMap z u t)) (Set.Icc (0 : ℝ) 1) := by
    exact hlip.continuous.continuousOn.comp AffineMap.lineMap_continuous.continuousOn (fun _ _ ↦ Set.mem_univ _)
  have hψ_cont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1) := by
    simpa [ψ] using hgradCont.inner continuousOn_const
  have hψ_int : IntervalIntegrable ψ MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one hψ_cont
  have hFTC : ∫ t in 0..1, ψ t = f u - f z := by
    simpa [φ, ψ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using
      intervalIntegral.integral_eq_sub_of_hasDerivAt hψ_deriv hψ_int
  have hρ_eq : (fun t : ℝ ↦ ψ t - ψ 0) = ρ := by
    funext t
    simp [ψ, ρ, AffineMap.lineMap_apply_zero, inner_sub_left]
  have hconst_int : IntervalIntegrable (fun _ : ℝ ↦ ψ 0) MeasureTheory.volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc zero_le_one continuousOn_const
  have hρ_int : IntervalIntegrable ρ MeasureTheory.volume 0 1 := by
    have hρ_cont : ContinuousOn ρ (Set.Icc (0 : ℝ) 1) := by
      simpa [ρ] using (hgradCont.sub continuousOn_const).inner continuousOn_const
    exact ContinuousOn.intervalIntegrable_of_Icc zero_le_one hρ_cont
  have hrem : f u - f z - inner ℝ (grad z) (u - z) = ∫ t in 0..1, ρ t := by
    calc
      f u - f z - inner ℝ (grad z) (u - z) = (∫ t in 0..1, ψ t) - ψ 0 := by
        rw [← hFTC]
        simp [ψ, AffineMap.lineMap_apply_zero]
      _ = (∫ t in 0..1, ψ t) - ∫ t in 0..1, ψ 0 := by simp [intervalIntegral.integral_const]
      _ = ∫ t in 0..1, (ψ t - ψ 0) := by rw [intervalIntegral.integral_sub hψ_int hconst_int]
      _ = ∫ t in 0..1, ρ t := by rw [hρ_eq]
  have hbound_int : IntervalIntegrable (fun t : ℝ ↦ (L : ℝ) * ‖u - z‖ ^ 2 * t)
      MeasureTheory.volume 0 1 := by
    refine Continuous.intervalIntegrable ?_ 0 1
    continuity
  have hbound_mono : (∫ t in 0..1, |ρ t|) ≤ ∫ t in 0..1, (L : ℝ) * ‖u - z‖ ^ 2 * t := by
    refine intervalIntegral.integral_mono_on zero_le_one hρ_int.abs hbound_int ?_
    intro t ht
    have hnorm : ‖grad (AffineMap.lineMap z u t) - grad z‖ ≤ (L : ℝ) * ‖AffineMap.lineMap z u t - z‖ := by
      simpa [dist_eq_norm] using hlip.dist_le_mul (AffineMap.lineMap z u t) z
    have hline : ‖AffineMap.lineMap z u t - z‖ = t * ‖u - z‖ := by
      simpa [dist_eq_norm, norm_sub_rev, Real.norm_eq_abs, abs_of_nonneg ht.1, mul_comm] using
        dist_left_lineMap z u t
    calc
      |ρ t| ≤ ‖grad (AffineMap.lineMap z u t) - grad z‖ * ‖u - z‖ := by
        exact abs_real_inner_le_norm _ _
      _ ≤ ((L : ℝ) * ‖AffineMap.lineMap z u t - z‖) * ‖u - z‖ := by gcongr
      _ = (L : ℝ) * ‖u - z‖ ^ 2 * t := by rw [hline]; ring
  have hbound : f u - f z - inner ℝ (grad z) (u - z) ≤ ((L : ℝ) / 2) * ‖u - z‖ ^ 2 := by
    calc
      f u - f z - inner ℝ (grad z) (u - z) = ∫ t in 0..1, ρ t := hrem
      _ ≤ |∫ t in 0..1, ρ t| := le_abs_self _
      _ ≤ ∫ t in 0..1, |ρ t| := intervalIntegral.abs_integral_le_integral_abs zero_le_one
      _ ≤ ∫ t in 0..1, (L : ℝ) * ‖u - z‖ ^ 2 * t := hbound_mono
      _ = ((L : ℝ) / 2) * ‖u - z‖ ^ 2 := by
        rw [intervalIntegral.integral_const_mul, integral_id]
        ring
  linarith

/-- Baillon--Haddad theorem: a convex differentiable function `f` with
  `L`-Lipschitz gradient `gradf = ∇f` (via Riesz representation) has a
  `1/L`-cocoercive gradient on the whole space. -/
theorem baillon_haddad {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → ℝ) (gradf : H → H) (L : ℝ) (hL : 0 < L)
    (hconv : ConvexOn ℝ Set.univ f) (hdiff : Differentiable ℝ f)
    (hgrad : ∀ x, HasGradientAt f (gradf x) x)
    (hlip : LipschitzWith (Real.toNNReal L) gradf) :
    CocoerciveOn (1 / L) Set.univ (fun x : Set.univ => gradf x) := by
  apply (fun _ : Differentiable ℝ f => ?_) hdiff
  have hBregman : ∀ x y : H,
      (2 * L)⁻¹ * ‖gradf x - gradf y‖ ^ 2 ≤
        f x - f y - inner ℝ (gradf y) (x - y) := by
    intro x y
    let d : H := gradf x - gradf y
    let w : H := x - L⁻¹ • d
    have hlow := convex_supporting_baillon_haddad f gradf hconv hgrad y w
    have hupp := smoothness_baillon_haddad f gradf (Real.toNNReal L) hgrad hlip x w
    rw [Real.coe_toNNReal L hL.le] at hupp
    have h := hlow.trans hupp
    have hwx : w - x = -L⁻¹ • d := by dsimp [w]; module
    have hwy : w - y = x - y - L⁻¹ • d := by dsimp [w]; module
    have hgd : inner ℝ (gradf x) d - inner ℝ (gradf y) d = ‖d‖ ^ 2 := by
      dsimp [d]
      rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    have hkey : L⁻¹ * ‖d‖ ^ 2 - (L / 2) * ‖-(L⁻¹ • d)‖ ^ 2 ≤
        f x - f y - inner ℝ (gradf y) (x - y) := by
      rw [hwy, hwx, inner_sub_right, real_inner_smul_right] at h
      rw [show -L⁻¹ • d = -(L⁻¹ • d) by module] at h
      rw [inner_neg_right, real_inner_smul_right] at h
      have hscaled := congrArg (fun t : ℝ ↦ L⁻¹ * t) hgd
      ring_nf at hscaled
      nlinarith [hscaled]
    have hnorm : ‖-(L⁻¹ • d)‖ ^ 2 = (L⁻¹) ^ 2 * ‖d‖ ^ 2 := by
      rw [norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hL)]
      ring
    rw [hnorm] at hkey
    have hcoef : L⁻¹ * ‖d‖ ^ 2 - (L / 2) * (L⁻¹) ^ 2 * ‖d‖ ^ 2 =
        (2 * L)⁻¹ * ‖d‖ ^ 2 := by
      field_simp [hL.ne']
      ring
    have hkey' : L⁻¹ * ‖d‖ ^ 2 - (L / 2) * (L⁻¹) ^ 2 * ‖d‖ ^ 2 ≤
        f x - f y - inner ℝ (gradf y) (x - y) := by
      nlinarith [hkey]
    rw [hcoef] at hkey'
    simpa [d] using hkey'
  have hpoint : ∀ x y : H,
      (1 / L) * ‖gradf x - gradf y‖ ^ 2 ≤ inner ℝ (gradf x - gradf y) (x - y) := by
    intro x y
    have hsum := add_le_add (hBregman x y) (hBregman y x)
    have hnorm : ‖gradf y - gradf x‖ ^ 2 = ‖gradf x - gradf y‖ ^ 2 := by
      rw [show gradf y - gradf x = -(gradf x - gradf y) by abel, norm_neg]
    rw [hnorm] at hsum
    have hinner :
        (f x - f y - inner ℝ (gradf y) (x - y)) +
          (f y - f x - inner ℝ (gradf x) (y - x)) =
          inner ℝ (gradf x - gradf y) (x - y) := by
      rw [show y - x = -(x - y) by abel, inner_neg_right, inner_sub_left]
      ring
    rw [hinner] at hsum
    have hcoef :
        (2 * L)⁻¹ * ‖gradf x - gradf y‖ ^ 2 + (2 * L)⁻¹ * ‖gradf x - gradf y‖ ^ 2 =
          L⁻¹ * ‖gradf x - gradf y‖ ^ 2 := by
      field_simp [hL.ne']
      ring
    rw [hcoef] at hsum
    simpa [one_div] using hsum
  apply (CocoerciveOn.pointwise_iff gradf (1 / L) (one_div_pos.mpr hL)).mpr
  intro x y
  exact hpoint y x
