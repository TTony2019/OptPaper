import Mathlib
import Foundation.Analysis.ExtendedRealFunctions

/-!
# Argmin sets

The set of minimizers of a function into an ordered type, the constrained
variant, and the propositional `IsArgmin` form.  A single definition covers
the various paper-local argmin definitions (over `ℝ`, `EReal`, `WithTop ℝ`,
and general preorders).
-/

namespace Optimization

/-- The set of global minimizers of `f : X → R` over the whole space. -/
def argminSet {X R : Type*} [LE R] (f : X → R) : Set X :=
  {x | ∀ y, f x ≤ f y}

/-- The set of minimizers of `f` over a subset `C`. -/
def argminOn {X R : Type*} [LE R] (C : Set X) (f : X → R) : Set X :=
  {x | x ∈ C ∧ ∀ y ∈ C, f x ≤ f y}

/-- The infimum value of a function into a conditionally complete linear
order (e.g. `ℝ`).  It agrees with `f x` at a minimizer by
`minimumValue_eq_of_mem_argminSet`. -/
def minimumValue {X R : Type*} [ConditionallyCompleteLinearOrder R] (f : X → R) : R :=
  sInf (Set.range f)

/-- At a minimizer, the minimum value is attained: `minimumValue f = f x`. -/
theorem minimumValue_eq_of_mem_argminSet {X R : Type*} [ConditionallyCompleteLinearOrder R]
    (f : X → R) {x : X} (hx : x ∈ argminSet f) : minimumValue f = f x := by
  unfold minimumValue
  apply IsLeast.csInf_eq
  refine ⟨⟨x, rfl⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact hx y

/-- `x` is a global minimizer of `f`. -/
def IsArgmin {X R : Type*} [LE R] (f : X → R) (x : X) : Prop :=
  ∀ y, f x ≤ f y

/-- Membership in the minimizer set is the propositional form. -/
@[simp]
theorem mem_argminSet_iff {X R : Type*} [LE R] (f : X → R) (x : X) :
    x ∈ argminSet f ↔ IsArgmin f x := by
  rfl

/-- The unconstrained minimizer set is the minimizer set over the whole space. -/
theorem argminSet_eq_argminOn_univ {X R : Type*} [LE R] (f : X → R) :
    argminSet f = argminOn Set.univ f := by
  ext x
  constructor
  · intro hx
    exact ⟨trivial, by intro y hy; exact hx y⟩
  · intro hx
    exact fun y => hx.2 y trivial

/-- In a complete linear order, `x` is a minimizer iff `f` attains its
infimum there: `f x = sInf (Set.range f)`. -/
theorem mem_argminSet_iff_eq_sInf {X R : Type*} [CompleteLinearOrder R]
    (f : X → R) (x : X) : x ∈ argminSet f ↔ f x = sInf (Set.range f) := by
  constructor
  · intro hx
    apply le_antisymm
    · exact le_sInf (by
        intro y hy
        rcases hy with ⟨z, rfl⟩
        exact hx z)
    · exact sInf_le ⟨x, rfl⟩
  · intro hx y
    rw [hx]
    exact sInf_le ⟨y, rfl⟩

end Optimization

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap11/Definition_11_3 -/

namespace ERealFunction

variable {X : Type u}

/-- Definition 11 3: `argminOn f C` is the set of minimizers of `f` over the constraint set `C`,
written `Argmin[C] f`. The global argmin set is the special case `argminOn f Set.univ`, written
`Argmin f`. -/
def argminOn (f : X → EReal) (C : Set X) : Set X :=
  {x | x ∈ C ∧ IsMinOn f C x}

/- Definition 11.3: the constrained minimizer set `argminOn f C` is written `Argmin[C] f`. -/
notation "Argmin[" C "] " f:max => argminOn f C

/-- A point belongs to `Argmin[C] f` exactly when it lies in `C` and minimizes `f` over `C`. -/
@[simp] theorem mem_argminOn_iff {f : X → EReal} {C : Set X} {x : X} :
    x ∈ Argmin[C] f ↔ x ∈ C ∧ IsMinOn f C x :=
  Iff.rfl

/-- Every constrained minimizer belongs to the constraint set. -/
theorem mem_of_mem_argminOn {f : X → EReal} {C : Set X} {x : X}
    (hx : x ∈ Argmin[C] f) :
    x ∈ C :=
  hx.1

/- Definition 11.3: the textbook global minimizer set `Argmin f` is `argminOn f Set.univ`. -/
notation "Argmin " f:arg => argminOn f Set.univ

/-- A point belongs to `Argmin f` exactly when it is a global minimizer of `f`. -/
@[simp] theorem mem_argmin_iff {f : X → EReal} {x : X} :
    x ∈ Argmin f ↔ IsMinOn f Set.univ x :=
  by simp [argminOn]

/-- A point lies in `Argmin f` exactly when its value equals the infimum of the range of `f`. -/
theorem mem_argmin_iff_eq_sInf {f : X → EReal} {x : X} :
    x ∈ Argmin f ↔ f x = sInf (Set.range f) := by
  constructor
  · intro hx
    have hxmin : IsMinOn f Set.univ x := (mem_argmin_iff).1 hx
    simpa only [Set.image_univ] using eq_sInf_image_of_isMinOn (by simp) hxmin
  · intro hx
    rw [mem_argmin_iff, isMinOn_univ_iff]
    intro y
    have hsInf_le : sInf (Set.range f) ≤ f y :=
      (isGLB_sInf (Set.range f)).1 (Set.mem_range_self y)
    simpa [hx] using hsInf_le

/-- Every global minimizer of a proper extended-real-valued function lies in the domain. -/
theorem mem_dom_of_mem_argmin_of_isProper {f : X → EReal} (hf : IsProper f) {x : X}
    (hx : x ∈ Argmin f) :
    x ∈ dom f := by
  obtain ⟨y, hy⟩ := hf.2
  rw [mem_argmin_iff, isMinOn_univ_iff] at hx
  change f x < ⊤
  exact lt_of_le_of_lt (hx y) ((ERealFunction.mem_dom_iff f y).1 hy)

/-- The global argmin set is the sublevel set at the infimum of the range of `f`. -/
theorem argmin_eq_setOf_le_sInf_range {f : X → EReal} :
    Argmin f = {x | f x ≤ sInf (Set.range f)} := by
  ext x
  rw [mem_argmin_iff_eq_sInf]
  constructor
  · intro hx
    exact hx.le
  · intro hx
    exact le_antisymm hx <| (isGLB_sInf (Set.range f)).1 (Set.mem_range_self x)

/-! Source item:
`TheoremLib/Attouch_Chbani_Riahi_Fast_proximal_methods_via_time_scaling_of_damped_inertial_dynamics_2019_correction/items/ext_def_1` -/

/-- The infimum value of an extended-real-valued function, `sInf (Set.range f)`.
This is the `EReal`-valued companion of `Optimization.minimumValue` (which requires a
`ConditionallyCompleteLinearOrder`); it is the value attained at every minimizer, by
`mem_argmin_iff_eq_sInf`. -/
noncomputable def minimumValue (f : X → EReal) : EReal :=
  sInf (Set.range f)

/-- The textbook indicator `ι[C]` of a set, viewed as a `]-∞,+∞]`-valued function. -/
noncomputable def indicator (C : Set X) : X → Set.Ioi (⊥ : EReal) :=
  let _ : DecidablePred (fun y ↦ y ∈ C) := Classical.decPred (fun y ↦ y ∈ C)
  fun x ↦ if hx : x ∈ C then ⟨0, by simp⟩ else ⟨⊤, by simp⟩

notation "ι[" C "]" => ERealFunction.indicator C

/-- Coercing `ι[C]` to `EReal` gives the ordinary extended-real indicator of `C`. -/
@[simp] theorem indicator_apply
    (C : Set X) (x : X) :
    (ι[C] x : EReal) = Cᶜ.indicator (fun _ : X ↦ (⊤ : EReal)) x := by
  by_cases hx : x ∈ C <;> simp [indicator, hx]

/-- The effective domain of the textbook indicator `ι[C]` is exactly `C`. -/
@[simp] theorem effectiveDomain_indicator (C : Set X) :
    effectiveDomain (ι[C]) = C := by
  ext x
  by_cases hx : x ∈ C <;> simp [ERealFunction.effectiveDomain, indicator, hx]

/-- Evaluating the canonical constrained objective `f + (ι[C]).asEReal` adds the indicator value
pointwise. -/
@[simp] theorem add_indicator_apply
    (f : X → EReal) (C : Set X) (x : X) :
    (f + (ι[C]).asEReal) x = f x + (ι[C] x : EReal) :=
  rfl

/-- On `C`, the indicator-augmented function `f + (ι[C]).asEReal` agrees with `f`. -/
theorem add_indicator_eqOn
    (f : X → EReal) (C : Set X) :
    Set.EqOn (f + (ι[C]).asEReal) f C := by
  intro x hx
  simp [hx]

/-- Helper for Definition 11 3: outside the constraint set, the indicator-augmented objective
equals `⊤`. -/
private theorem add_indicator_eq_top_of_not_mem
    {f : X → EReal} {C : Set X} (hbot : ∀ x ∉ C, f x ≠ ⊥) {x : X} (hx : x ∉ C) :
    (f + (ι[C]).asEReal) x = ⊤ := by
  simp [indicator_apply, hx, EReal.add_top_of_ne_bot (hbot x hx)]

/-- Helper for Definition 11 3: a minimizer of `f` on `C` becomes a global minimizer after adding
the indicator of `C`. -/
private theorem isMinOn_univ_add_indicator_of_isMinOn
    {f : X → EReal} {C : Set X} (hbot : ∀ x ∉ C, f x ≠ ⊥) {x : X}
    (hxC : x ∈ C) (hxmin : IsMinOn f C x) :
    IsMinOn (f + (ι[C]).asEReal) Set.univ x := by
  rw [isMinOn_univ_iff]
  intro y
  by_cases hy : y ∈ C
  · have hxy : f x ≤ f y := (isMinOn_iff.mp hxmin) y hy
    simpa [add_indicator_apply, indicator_apply, hxC, hy] using hxy
  · rw [add_indicator_eq_top_of_not_mem hbot hy]
    exact le_top

/-- Helper for Definition 11 3: a global minimizer of the indicator-augmented objective restricts
to a minimizer of `f` on `C`. -/
private theorem isMinOn_of_isMinOn_univ_add_indicator
    {f : X → EReal} {C : Set X} {x : X} (hxC : x ∈ C)
    (hxmin : IsMinOn (f + (ι[C]).asEReal) Set.univ x) :
    IsMinOn f C x := by
  rw [isMinOn_iff]
  intro y hy
  have hxy : (f + (ι[C]).asEReal) x ≤ (f + (ι[C]).asEReal) y :=
    (isMinOn_univ_iff.mp hxmin) y
  simpa [add_indicator_apply, indicator_apply, hxC, hy] using hxy

/-- Minimizers of `f` over `C` are exactly the global minimizers of `f + ι_C`, written here as
the canonical indicator `ι[C]`, that lie in `C`. -/
theorem argminOn_eq_inter_argmin_add_indicator
    (f : X → EReal) (C : Set X) (hbot : ∀ x ∉ C, f x ≠ ⊥) :
    Argmin[C] f = C ∩ Argmin (f + (ι[C]).asEReal) := by
  ext x
  constructor
  · intro hx
    rcases mem_argminOn_iff.mp hx with ⟨hxC, hxmin⟩
    refine ⟨hxC, ?_⟩
    rw [mem_argmin_iff]
    exact isMinOn_univ_add_indicator_of_isMinOn hbot hxC hxmin
  · intro hx
    rcases hx with ⟨hxC, hxaug⟩
    refine mem_argminOn_iff.mpr ⟨hxC, ?_⟩
    have hxmin : IsMinOn (f + (ι[C]).asEReal) Set.univ x := (mem_argmin_iff).mp hxaug
    exact isMinOn_of_isMinOn_univ_add_indicator hxC hxmin

section PseudoMetricSpace

variable [PseudoMetricSpace X]

/-- Any minimizer of `f` on some open ball centered at `x` is a local minimizer of `f`. -/
theorem isLocalMin_of_mem_argminOn_ball {f : X → EReal} {x : X} {ρ : ℝ}
    (hρ : 0 < ρ) (hx : x ∈ Argmin[Metric.ball x ρ] f) :
    IsLocalMin f x :=
  hx.2.isLocalMin (Metric.ball_mem_nhds x hρ)

end PseudoMetricSpace

end ERealFunction
