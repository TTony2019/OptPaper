import Mathlib.Data.Rel
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
import Mathlib.Analysis.Normed.Group.Basic

/-!
# SetValued Basic

Set-valued operators, graphs, domains, inverses, selections, and pointwise operations.
-/

open scoped Pointwise

universe u v

-- Compatibility alias used by subsequent textbook items.
abbrev SetValuedOperator (X : Type u) (Y : Type v) : Type (max u v) := X → Set Y

namespace SetValuedOperator

variable {X : Type u} {Y : Type v}

/-- The graph of a set-valued operator consists of the pairs `(x, u)` with `u ∈ A x`. -/
def graph (A : SetValuedOperator X Y) : SetRel X Y := { xu | xu.2 ∈ A xu.1 }

/-- Membership in the graph of a set-valued operator is equivalent to membership in the
corresponding value set. -/
@[simp] theorem mem_graph (A : SetValuedOperator X Y) (x : X) (u : Y) :
    (x, u) ∈ A.graph ↔ u ∈ A x :=
  Iff.rfl

/-- Compatibility form of `mem_graph` using the original `_iff` suffix. -/
theorem mem_graph_iff (A : SetValuedOperator X Y) (x : X) (u : Y) :
    (x, u) ∈ A.graph ↔ u ∈ A x :=
  mem_graph A x u

end SetValuedOperator

/-! Source item: Chap01/Text_1_0_9 -/
universe w

namespace SetValuedOperator

variable {X : Type u} {Y : Type v} {Z : Type w}

/-- Text 1.0.9: The image `A(C)` of a set `C` under a set-valued operator `A` is the union of
the value sets `A x` for `x ∈ C`. -/
def image (A : SetValuedOperator X Y) (C : Set X) : Set Y := ⋃ x ∈ C, A x

/-- Membership in the image of a set under a set-valued operator is equivalent to belonging to
one of the value sets over that set. -/
@[simp] theorem mem_image (A : SetValuedOperator X Y) (C : Set X) (y : Y) :
    y ∈ A.image C ↔ ∃ x ∈ C, y ∈ A x := by
  simp [image]

/-- The composition of set-valued operators sends `x` to the image of the value set `A x` under
`B`. -/
def comp (B : SetValuedOperator Y Z) (A : SetValuedOperator X Y) : SetValuedOperator X Z :=
  fun x ↦ B.image (A x)

/-- Evaluating the composition of set-valued operators amounts to taking the image of the value
set under the second operator. -/
@[simp] theorem comp_apply (B : SetValuedOperator Y Z) (A : SetValuedOperator X Y) (x : X) :
    B.comp A x = B.image (A x) :=
  rfl

/-- Membership in the composition of set-valued operators is equivalent to the existence of an
intermediate point in the first value set whose image under the second operator contains the
element. -/
@[simp] theorem mem_comp (B : SetValuedOperator Y Z) (A : SetValuedOperator X Y) (x : X) (z : Z) :
    z ∈ B.comp A x ↔ ∃ y ∈ A x, z ∈ B y := by
  simp [comp]

end SetValuedOperator

/-! Source item: Chap01/Text_1_0_10 -/

namespace SetValuedOperator

variable {X : Type u} {Y : Type v}

/-- Text 1.0.10: The domain of a set-valued operator `A` is the set of points `x` for which
`A x` is nonempty. -/
def dom (A : SetValuedOperator X Y) : Set X := { x | (A x).Nonempty }

/-- The range of a set-valued operator `A` is the union of all of its value sets. -/
def range (A : SetValuedOperator X Y) : Set Y := ⋃ x, A x

/-- A point belongs to the domain exactly when the corresponding value set is nonempty. -/
theorem mem_dom_iff (A : SetValuedOperator X Y) (x : X) :
    x ∈ A.dom ↔ (A x).Nonempty := by
  rfl

/-- A point belongs to the range exactly when it lies in the value set `A x` for some `x`. -/
theorem mem_range_iff (A : SetValuedOperator X Y) (y : Y) :
    y ∈ A.range ↔ ∃ x, y ∈ A x := by
  simp [range]

end SetValuedOperator

/-! Source item: Chap01/Text_1_0_11 -/

namespace SetValuedOperator

variable {X : Type u} {Y : Type v}

/-- Text 1.0.11: The inverse of a set-valued operator is the operator obtained by reversing
its graph, equivalently by sending `u : Y` to the set of `x : X` such that `u ∈ A x`. -/
def inverse (A : SetValuedOperator X Y) : SetValuedOperator Y X := fun u ↦ { x | u ∈ A x }

/-- Membership in the inverse operator is equivalent to reversing the membership relation in
the original operator. -/
@[simp] theorem mem_inverse_iff (A : SetValuedOperator X Y) (u : Y) (x : X) :
    x ∈ A.inverse u ↔ u ∈ A x := by
  rfl

/-- The zero set of a set-valued operator consists of the points mapped to a set containing
`0`. -/
def zeros [Zero Y] (A : SetValuedOperator X Y) : Set X := A.inverse 0

/-- Membership in the zero set means that `0` belongs to the corresponding value set. -/
@[simp] theorem mem_zeros_iff [Zero Y] (A : SetValuedOperator X Y) (x : X) :
    x ∈ A.zeros ↔ (0 : Y) ∈ A x := by
  rfl

end SetValuedOperator

/-! Source item: Chap01/Text_1_0_12 -/

namespace SetValuedOperator

variable {X : Type u} {Y : Type v}

/-- Text 1.0.12 (1): the domain of the inverse of a set-valued operator is the range of the
original operator. -/
@[simp] theorem dom_inverse (A : SetValuedOperator X Y) :
    A.inverse.dom = A.range := by
  ext u
  rw [mem_dom_iff, mem_range_iff]
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_inverse_iff A u x).mp hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (mem_inverse_iff A u x).mpr hx⟩

/-- Text 1.0.12 (2): the range of the inverse of a set-valued operator is the domain of the
original operator. -/
@[simp] theorem range_inverse (A : SetValuedOperator X Y) :
    A.inverse.range = A.dom := by
  ext x
  rw [mem_range_iff, mem_dom_iff]
  constructor
  · rintro ⟨u, hu⟩
    exact ⟨u, (mem_inverse_iff A u x).mp hu⟩
  · rintro ⟨u, hu⟩
    exact ⟨u, (mem_inverse_iff A u x).mpr hu⟩

end SetValuedOperator

/-! Source item: Chap01/Text_1_0_13 -/

namespace SetValuedOperator

variable {X : Type u} {Y : Type v}

/-- Text 1.0.13: a set-valued operator is at most single-valued when each value set has at most
one element, equivalently when every value over its domain is a singleton. -/
def IsAtMostSingleValued (A : SetValuedOperator X Y) : Prop :=
  ∀ x, (A x).Subsingleton

/-- Textbook reformulation of `IsAtMostSingleValued`: over the domain, every value set is a
singleton. -/
theorem isAtMostSingleValued_iff_forall_eq_singleton (A : SetValuedOperator X Y) :
    IsAtMostSingleValued A ↔ ∀ x ∈ A.dom, ∃ y, A x = ({y} : Set Y) := by
  constructor
  · intro hA x hx
    rcases (mem_dom_iff A x).mp hx with ⟨y, hy⟩
    exact ⟨y, (hA x).eq_singleton_of_mem hy⟩
  · intro hA x
    by_cases hx : x ∈ A.dom
    · rcases hA x hx with ⟨y, hy⟩
      rw [hy]
      exact Set.subsingleton_singleton
    · rw [mem_dom_iff] at hx
      rw [Set.not_nonempty_iff_eq_empty] at hx
      rw [hx]
      exact Set.subsingleton_empty

/-- The set-valued operator associated with a function `T : D → Y` sends points of `D` to the
corresponding singleton values and points outside `D` to the empty set. -/
def ofFunction (D : Set X) (T : D → Y) : SetValuedOperator X Y :=
  fun x ↦ { y | ∃ hx : x ∈ D, y = T ⟨x, hx⟩ }

/-- On points of the domain, the operator associated with a function takes the corresponding
singleton value. -/
theorem ofFunction_apply_of_mem (D : Set X) (T : D → Y) {x : X} (hx : x ∈ D) :
    ofFunction D T x = ({T ⟨x, hx⟩} : Set Y) := by
  ext y
  constructor
  · rintro ⟨hx', rfl⟩
    have hsub : (⟨x, hx'⟩ : D) = ⟨x, hx⟩ := Subtype.ext <| by rfl
    rw [hsub]
    exact Set.mem_singleton _
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨hx, rfl⟩

/-- Outside the domain, the operator associated with a function takes the empty value set. -/
theorem ofFunction_apply_of_not_mem (D : Set X) (T : D → Y) {x : X} (hx : x ∉ D) :
    ofFunction D T x = (∅ : Set Y) := by
  ext y
  constructor
  · rintro ⟨hx', _⟩
    exact (hx hx').elim
  · intro hy
    exact False.elim <| Set.notMem_empty y hy

/-- The operator associated with a function on a subset is at most single-valued. -/
theorem isAtMostSingleValued_ofFunction (D : Set X) (T : D → Y) :
    IsAtMostSingleValued (ofFunction D T) := by
  intro x
  by_cases hx : x ∈ D
  · rw [ofFunction_apply_of_mem D T hx]
    exact Set.subsingleton_singleton
  · rw [ofFunction_apply_of_not_mem D T hx]
    exact Set.subsingleton_empty

end SetValuedOperator

/-! Source item: Chap01/Text_1_0_14 -/

namespace SetValuedOperator

variable {X : Type u} {Y : Type v}

variable {A : SetValuedOperator X Y}

/-- Text 1.0.14: a selection of `A` is an operator `T : A.dom → Y` such that `T x ∈ A x`
for every `x ∈ A.dom`. -/
abbrev Selection (A : SetValuedOperator X Y) : Type (max u v) := ∀ x : A.dom, A x

/-- A selection takes each point of the domain of `A` to a point of the corresponding value
set. -/
@[simp] theorem selection_apply_mem (T : Selection A) (x : A.dom) :
    (T x : Y) ∈ A x :=
  (T x).property

end SetValuedOperator

/-! Source item: Chap01/Text_1_0_16 -/


namespace SetValuedOperator

variable {X : Type u} {Y : Type v} [AddCommGroup Y] [Module ℝ Y]

/-- Text 1.0.16: for set-valued operators `A B : X → Set Y` and a real scalar `c`
(`λ` in the text), the linear combination `A + λ B` is the pointwise operator satisfying
`(A + c • B) x = A x + c • B x`. -/
@[simp] theorem add_smul_apply (A B : SetValuedOperator X Y) (c : ℝ) (x : X) :
    (A + c • B) x = A x + c • B x :=
  rfl

end SetValuedOperator

/-! Source item: Chap01/Text_1_0_17 -/


namespace SetValuedOperator

variable {X : Type u} {Y : Type v} [AddCommGroup Y] [Module ℝ Y]

/-- Membership in `(A + r • B) x` means being representable as `u + r • v` with
`u ∈ A x` and `v ∈ B x`. -/
theorem mem_add_smul_iff (A B : SetValuedOperator X Y) (r : ℝ) (x : X) (w : Y) :
    w ∈ (A + r • B) x ↔ ∃ u ∈ A x, ∃ v ∈ B x, w = u + r • v := by
  constructor
  · intro hw
    -- Expand membership in the pointwise sum, then unpack the scalar-multiple witness.
    rw [add_smul_apply, Set.mem_add] at hw
    rcases hw with ⟨u, hu, z, hz, huz⟩
    rw [Set.mem_smul_set] at hz
    rcases hz with ⟨v, hv, hvz⟩
    refine ⟨u, hu, v, hv, ?_⟩
    simpa [hvz] using huz.symm
  · rintro ⟨u, hu, v, hv, rfl⟩
    -- Rebuild membership by choosing `u` from `A x` and `r • v` from `r • B x`.
    rw [add_smul_apply, Set.mem_add]
    refine ⟨u, hu, r • v, ?_, rfl⟩
    rw [Set.mem_smul_set]
    exact ⟨v, hv, rfl⟩

/-- Helper for Text 1.0.17: `(A + r • B) x` is nonempty exactly when both input value sets
are nonempty. -/
-- Proof sketch: convert nonemptiness to a witness in the linear combination, use
-- `mem_add_smul_iff` to extract witnesses in `A x` and `B x`, and reverse the argument
-- by building the element `u + r • v`.
private lemma add_smul_nonempty_iff
    (A B : SetValuedOperator X Y) (r : ℝ) (x : X) :
    ((A + r • B) x).Nonempty ↔ (A x).Nonempty ∧ (B x).Nonempty := by
  constructor
  · rintro ⟨w, hw⟩
    -- Any witness in the linear combination decomposes into witnesses from both source sets.
    rw [mem_add_smul_iff] at hw
    rcases hw with ⟨u, hu, v, hv, _⟩
    exact ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
  · rintro ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
    -- Given witnesses in both source sets, their linear combination is a witness upstairs.
    refine ⟨u + r • v, ?_⟩
    rw [mem_add_smul_iff]
    exact ⟨u, hu, v, hv, rfl⟩

/-- Text 1.0.17 (1): the graph of the pointwise linear combination `A + λ B` consists of the
pairs `(x, u + λ • v)` coming from matching graph points of `A` and `B`. -/
-- Proof sketch: use `Set.ext`, unfold `SetValuedOperator.graph`, apply
-- `mem_add_smul_iff`, and rewrite the resulting membership conditions using
-- `SetValuedOperator.mem_graph_iff`.
theorem graph_add_smul (A B : SetValuedOperator X Y) (r : ℝ) :
    (A + r • B).graph =
      { xw | ∃ u v, (xw.1, u) ∈ A.graph ∧ (xw.1, v) ∈ B.graph ∧ xw.2 = u + r • v } := by
  ext xw
  constructor
  · intro hxw
    -- A graph point is exactly a point whose second coordinate lies in the combined value set.
    rw [mem_graph_iff, mem_add_smul_iff] at hxw
    rcases hxw with ⟨u, hu, v, hv, hEq⟩
    exact ⟨u, v, (mem_graph_iff A xw.1 u).2 hu, (mem_graph_iff B xw.1 v).2 hv, hEq⟩
  · intro hxw
    -- Conversely, the witness description gives membership in the value set, hence in the graph.
    rcases hxw with ⟨u, v, hu, hv, hEq⟩
    rw [mem_graph_iff, mem_add_smul_iff]
    exact ⟨u, (mem_graph_iff A xw.1 u).1 hu, v, (mem_graph_iff B xw.1 v).1 hv, hEq⟩

/-- Text 1.0.17 (2): the domain of the pointwise linear combination `A + λ B` is
`A.dom ∩ B.dom`. -/
@[simp] theorem dom_add_smul (A B : SetValuedOperator X Y) (r : ℝ) :
    (A + r • B).dom = A.dom ∩ B.dom := by
  ext x
  rw [Set.mem_inter_iff, mem_dom_iff, mem_dom_iff, mem_dom_iff]
  rw [add_smul_nonempty_iff]

end SetValuedOperator

/-! Source item: Chap01/Text_1_0_21 -/

namespace SetValuedOperator

variable {X : Type u} {Y : Type v} [AddGroup X]

/-- Text 1.0.21: The translation of a set-valued operator `A` by `y` sends `x` to the value
of `A` at `x - y`. -/
def translate (A : SetValuedOperator X Y) (y : X) : SetValuedOperator X Y :=
  fun x ↦ A (x - y)

/-- Applying the translation of `A` by `y` at `x` evaluates `A` at `x - y`. -/
@[simp] theorem translate_apply (A : SetValuedOperator X Y) (y x : X) :
    translate A y x = A (x - y) :=
  rfl

/-- Membership in the translation of a set-valued operator is equivalent to membership in the
original operator after translating the input by `-y`. -/
@[simp]
theorem mem_translate_iff (A : SetValuedOperator X Y) (y x : X) (u : Y) :
    u ∈ translate A y x ↔ u ∈ A (x - y) :=
  Iff.rfl

/-- The reversal of a set-valued operator sends `x` to the value of `A` at `-x`. -/
def reverse (A : SetValuedOperator X Y) : SetValuedOperator X Y :=
  fun x ↦ A (-x)

/-- Applying the reversal of `A` at `x` evaluates `A` at `-x`. -/
@[simp] theorem reverse_apply (A : SetValuedOperator X Y) (x : X) :
    reverse A x = A (-x) :=
  rfl

/-- Membership in the reversal of a set-valued operator is equivalent to membership in the
original operator at the negated input. -/
@[simp]
theorem mem_reverse_iff (A : SetValuedOperator X Y) (x : X) (u : Y) :
    u ∈ reverse A x ↔ u ∈ A (-x) :=
  Iff.rfl

end SetValuedOperator

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap01/Text_1_0_13 -/

namespace Function

variable {X : Type u} {Y : Type v}

/-- The singleton-valued set-valued operator associated with a single-valued map on the whole
space. This is the `Set.univ` specialization of `SetValuedOperator.ofFunction`. -/
abbrev toSetValuedOperator (T : X → Y) : SetValuedOperator X Y :=
  SetValuedOperator.ofFunction Set.univ (fun x : Set.univ ↦ T x)

/-- Evaluating `Function.toSetValuedOperator` recovers the corresponding singleton value set. -/
@[simp] theorem toSetValuedOperator_apply (T : X → Y) (x : X) :
    T.toSetValuedOperator x = ({T x} : Set Y) := by
  ext y
  constructor
  · rintro ⟨hx, rfl⟩
    rw [Set.mem_singleton_iff]
  · intro hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨by simp, rfl⟩

@[simp] theorem toSetValuedOperator_range (T : X → Y) :
    T.toSetValuedOperator.range = Set.range T := by
  ext y
  rw [SetValuedOperator.mem_range_iff]
  constructor
  · rintro ⟨x, hx⟩
    rcases hx with ⟨_, rfl⟩
    exact ⟨x, rfl⟩
  · rintro ⟨x, rfl⟩
    simp

end Function

/-! ### Minimal sections

A set-valued operator admits a minimal-norm element at a point when one of its
values contains an element of smallest norm.  This is a common hypothesis in
minimal-norm resolvent and subgradient arguments.

Promoted from `Attouch_Bot_Csetnek_Closed_loop_damping_2023` (ext_def_1).
-/

/-- A minimal-norm element of a nonempty subdifferential value, when specified. -/
def MinimalSection {H : Type*} [NormedAddCommGroup H]
    (A : SetValuedOperator H H) (u : H) : Prop :=
  ∃ v ∈ A u, ∀ w ∈ A u, ‖v‖ ≤ ‖w‖
