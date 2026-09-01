import Mathlib
import Foundation.Analysis.ExtendedRealFunctions
import Foundation.Analysis.Semicontinuity
import Foundation.Convex.Gamma0
import Foundation.Convex.Coercive
import Foundation.Convex.WeakClosed
import Foundation.Hilbert.WeakTopology
import Foundation.Hilbert.WeakConvergence
import Foundation.Optimization.Argmin

/-!
# Existence and uniqueness of minimizers

The Weierstrass-style engine for `Γ₀(H)` functions: coercivity gives bounded
lower level sets, quasiconvexity gives convex lower level sets, weak
compactness of bounded closed convex sets gives existence of minimizers, and
strict convexity gives uniqueness.
-/

open Filter Set
open scoped InnerProductSpace Topology

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Membership in the domain of an extended-real-valued function means the value is not `⊤`. -/
theorem mem_dom_iff_ne_top {X : Type*} {f : X → EReal} {x : X} :
    x ∈ dom f ↔ f x ≠ ⊤ := by
  rw [mem_dom_iff, lt_top_iff_ne_top]


/-! Source item: Bauschke-lean-project/BauschkeLean/Chap11/Proposition_11_12 -/

section

omit [InnerProductSpace ℝ H]

/-- Proposition 11.12: an extended-real-valued function is coercive if and only if each of its
real lower level sets is bounded. -/
theorem coercive_iff_bounded_lowerLevelSet (f : H → EReal) :
    Coercive f ↔ ∀ ξ : ℝ, Bornology.IsBounded (lowerLevelSet f ξ) := by
  rw [Coercive, EReal.tendsto_nhds_top_iff_real]
  constructor
  · intro hf ξ
    refine (Bornology.isBounded_def).2 ?_
    change {x : H | ¬f x ≤ (ξ : EReal)} ∈ Bornology.cobounded H
    simpa [not_le] using hf ξ
  · intro h ξ
    have hξ : (lowerLevelSet f ξ)ᶜ ∈ Bornology.cobounded H :=
      (Bornology.isBounded_def).1 (h ξ)
    change {x : H | ¬f x ≤ (ξ : EReal)} ∈ Bornology.cobounded H at hξ
    change {x : H | (ξ : EReal) < f x} ∈ Bornology.cobounded H
    simpa [not_le] using hξ

end

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap12/Definition_12_5 -/

section AffineMinorants

variable {H : Type u} [Inner ℝ H]

/-- Definition 12.5: `f` has a continuous affine minorant with slope `u` if it dominates a
function of the form `x ↦ ⟪x, u⟫ + η`. -/
def HasContinuousAffineMinorantWithSlope (f : H → EReal) (u : H) : Prop :=
  ∃ η : ℝ, ∀ x : H, (((⟪x, u⟫_ℝ + η : ℝ) : EReal) ≤ f x)

/-- The textbook bounded-below formulation says that `f` has a continuous affine minorant with
slope `u` exactly when the shifted function `x ↦ f x - ⟪x, u⟫` admits a real lower bound. -/
theorem hasContinuousAffineMinorantWithSlope_iff
    (f : H → EReal) (u : H) :
    HasContinuousAffineMinorantWithSlope f u ↔
      ∃ η : ℝ, ∀ x : H, (η : EReal) ≤ f x - ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
  constructor
  · rintro ⟨η, hη⟩
    refine ⟨η, fun x ↦ ?_⟩
    refine (EReal.le_sub_iff_add_le (.inl (by simp)) (.inl (by simp))).2 ?_
    simpa [EReal.coe_add, add_comm] using hη x
  · rintro ⟨η, hη⟩
    refine ⟨η, fun x ↦ ?_⟩
    have hx : (η : EReal) + ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ f x :=
      (EReal.le_sub_iff_add_le (.inl (by simp)) (.inl (by simp))).1 (hη x)
    simpa [EReal.coe_add, add_comm] using hx

end AffineMinorants

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap11/Theorem_11_10 -/

section

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- A function is quasiconvex on the whole space exactly when every real lower level set is
convex. -/
theorem quasiconvexOn_univ_iff_convex_lowerLevelSet (f : H → EReal) :
    QuasiconvexOn ℝ Set.univ f ↔ ∀ ξ : ℝ, Convex ℝ (lowerLevelSet f ξ) := by
  constructor
  · intro hf ξ
    rw [quasiconvexOn_iff_le_max] at hf
    rcases hf with ⟨_, hf⟩
    refine (convex_iff_forall_pos).2 ?_
    intro x hx y hy a b ha hb hab
    have hle : f (a • x + b • y) ≤ max (f x) (f y) := hf trivial trivial ha.le hb.le hab
    have hxξ : f x ≤ (ξ : EReal) := hx
    have hyξ : f y ≤ (ξ : EReal) := hy
    have hmax_le : max (f x) (f y) ≤ (ξ : EReal) := max_le hxξ hyξ
    change f (a • x + b • y) ≤ (ξ : EReal)
    exact hle.trans hmax_le
  · intro hlevel
    rw [quasiconvexOn_iff_le_max]
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    let M : EReal := max (f x) (f y)
    have hxM : f x ≤ M := le_max_left _ _
    have hyM : f y ≤ M := le_max_right _ _
    by_cases hM_top : M = ⊤
    · simpa [M, hM_top]
    · by_cases hM_bot : M = ⊥
      · have hz_bot : f (a • x + b • y) = ⊥ := by
          refine (EReal.eq_bot_iff_forall_lt _).2 ?_
          intro ξ
          have hxM' : f x ≤ (⊥ : EReal) := by simpa [M, hM_bot] using hxM
          have hyM' : f y ≤ (⊥ : EReal) := by simpa [M, hM_bot] using hyM
          have hx_level : x ∈ lowerLevelSet f (ξ - 1) := by
            rw [mem_lowerLevelSet_iff]
            exact hxM'.trans (EReal.bot_lt_coe (ξ - 1)).le
          have hy_level : y ∈ lowerLevelSet f (ξ - 1) := by
            rw [mem_lowerLevelSet_iff]
            exact hyM'.trans (EReal.bot_lt_coe (ξ - 1)).le
          have hz_level : a • x + b • y ∈ lowerLevelSet f (ξ - 1) :=
            hlevel (ξ - 1) hx_level hy_level ha hb hab
          have hz_le : f (a • x + b • y) ≤ ((ξ - 1 : ℝ) : EReal) :=
            (mem_lowerLevelSet_iff f (ξ - 1) (a • x + b • y)).1 hz_level
          exact lt_of_le_of_lt hz_le (by exact_mod_cast sub_lt_self ξ (by norm_num))
        simpa [M, hM_bot, hz_bot]
      · have hM_real : M = ((M.toReal : ℝ) : EReal) := (EReal.coe_toReal hM_top hM_bot).symm
        have hx_level : x ∈ lowerLevelSet f M.toReal := by
          rw [mem_lowerLevelSet_iff]
          rw [← hM_real]
          exact hxM
        have hy_level : y ∈ lowerLevelSet f M.toReal := by
          rw [mem_lowerLevelSet_iff]
          rw [← hM_real]
          exact hyM
        have hz_level : a • x + b • y ∈ lowerLevelSet f M.toReal :=
          hlevel M.toReal hx_level hy_level ha hb hab
        have hz_le : f (a • x + b • y) ≤ (M.toReal : EReal) :=
          (mem_lowerLevelSet_iff f M.toReal (a • x + b • y)).1 hz_level
        have hle_coe : (M.toReal : EReal) ≤ M := EReal.coe_toReal_le hM_bot
        exact hz_le.trans hle_coe

end

section

variable [CompleteSpace H]

omit [CompleteSpace H] in
/-- A lower semicontinuous quasiconvex function is lower semicontinuous in the weak topology. -/
theorem weaklyLowerSemicontinuous_of_quasiconvexOn_univ
    {f : H → EReal} (hf_quasi : QuasiconvexOn ℝ Set.univ f)
    (hf_lsc : LowerSemicontinuous f) :
    LowerSemicontinuous (f ∘ (toWeakSpace ℝ H).symm) := by
  rw [lowerSemicontinuous_iff_isClosed_lowerLevelSet]
  intro ξ
  have hlevel_convex : Convex ℝ (lowerLevelSet f ξ) :=
    (quasiconvexOn_univ_iff_convex_lowerLevelSet f).1 hf_quasi ξ
  have hlevel_closed : IsClosed (lowerLevelSet f ξ) :=
    (lowerSemicontinuous_iff_isClosed_lowerLevelSet f).1 hf_lsc ξ
  have hweak_closed : IsClosed ((toWeakSpace ℝ H) '' lowerLevelSet f ξ) :=
    (isClosed_iff_weak_image_isClosed_of_convex hlevel_convex).1 hlevel_closed
  -- The lower level set of `g` in the weak space is the image of the strong lower level set.
  have hpreimage :
      lowerLevelSet (f ∘ (toWeakSpace ℝ H).symm) ξ =
        (toWeakSpace ℝ H) '' lowerLevelSet f ξ := by
    ext w
    constructor
    · intro hw
      refine ⟨(toWeakSpace ℝ H).symm w, ?_, ?_⟩
      · exact (mem_lowerLevelSet_iff f ξ ((toWeakSpace ℝ H).symm w)).mpr
          ((mem_lowerLevelSet_iff (f ∘ (toWeakSpace ℝ H).symm) ξ w).mp hw)
      · exact (toWeakSpace ℝ H).apply_symm_apply w
    · rintro ⟨x, hx, rfl⟩
      exact (mem_lowerLevelSet_iff (f ∘ (toWeakSpace ℝ H).symm) ξ (toWeakSpace ℝ H x)).mpr
        ((mem_lowerLevelSet_iff f ξ x).mp hx)
  rw [hpreimage]
  exact hweak_closed

/-- Theorem 11.10: if a lower semicontinuous quasiconvex `]-∞,+∞]`-valued function on a real
Hilbert space has a nonempty bounded intersection of a closed convex constraint set with one of
its lower level sets, then its constrained argmin set is nonempty. -/
theorem argminOn_nonempty_of_quasiconvexOn_univ_of_nonempty_bounded_inter_lowerLevelSet
    {f : H → EReal} {C : Set H} (hf_quasi : QuasiconvexOn ℝ Set.univ f)
    (hf_lsc : LowerSemicontinuous f) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (ξ : ℝ)
    (hlevel_nonempty : (C ∩ lowerLevelSet f ξ).Nonempty)
    (hlevel_bounded : Bornology.IsBounded (C ∩ lowerLevelSet f ξ)) :
    (Argmin[C] f).Nonempty := by
  let D := C ∩ lowerLevelSet f ξ
  let g : WeakSpace ℝ H → EReal := f ∘ (toWeakSpace ℝ H).symm
  have hlevel_convex : Convex ℝ (lowerLevelSet f ξ) :=
    ((quasiconvexOn_univ_iff_convex_lowerLevelSet f).1 hf_quasi) ξ
  have hD_closed : IsClosed D := by
    refine hC_closed.inter ?_
    exact (lowerSemicontinuous_iff_isClosed_lowerLevelSet f).1 hf_lsc ξ
  have hD_convex : Convex ℝ D :=
    hC_convex.inter hlevel_convex
  have hD_compact : IsCompact (toWeakSpace ℝ H '' D) :=
    weaklyCompact_of_bounded_closed_convex hlevel_bounded hD_closed hD_convex
  have hg_lsc : LowerSemicontinuous g := by
    exact weaklyLowerSemicontinuous_of_quasiconvexOn_univ hf_quasi hf_lsc
  have hD_dom : (toWeakSpace ℝ H '' D ∩ {x | g x < ⊤}).Nonempty := by
    rcases hlevel_nonempty with ⟨x, hxD⟩
    have hxD' : x ∈ C ∩ lowerLevelSet f ξ := by
      simpa [D] using hxD
    refine ⟨toWeakSpace ℝ H x, ⟨⟨x, hxD, rfl⟩, ?_⟩⟩
    exact lt_of_le_of_lt ((mem_lowerLevelSet_iff f ξ x).1 hxD'.2) (by simp)
  obtain ⟨w, hwD, hwmin⟩ :=
    lowerSemicontinuous_exists_isMinOn_of_isCompact hg_lsc hD_compact hD_dom
  rcases hwD with ⟨x, hxD, rfl⟩
  have hxD' : x ∈ C ∩ lowerLevelSet f ξ := by
    simpa [D] using hxD
  have hxD_min : ∀ y ∈ D, f x ≤ f y := by
    rw [isMinOn_iff] at hwmin
    intro y hyD
    simpa [g] using hwmin (toWeakSpace ℝ H y) ⟨y, hyD, rfl⟩
  have hx_le : f x ≤ (ξ : EReal) := by
    exact (mem_lowerLevelSet_iff f ξ x).1 hxD'.2
  refine ⟨x, ?_⟩
  rw [mem_argminOn_iff, isMinOn_iff]
  refine ⟨hxD'.1, ?_⟩
  intro y hyC
  by_cases hy_level : y ∈ lowerLevelSet f ξ
  · exact hxD_min y ⟨hyC, hy_level⟩
  · have hy_gt : (ξ : EReal) < f y := by
      simpa [mem_lowerLevelSet_iff, not_le] using hy_level
    exact le_trans hx_le hy_gt.le

end

end ERealFunction

namespace ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap10/Definition_10_27 -/

section Strict

variable {H : Type u} [AddCommMonoid H] [Module ℝ H]
variable {f : H → EReal}

/-- Definition 10.27 (1): a proper function is strictly quasiconvex when every strict convex
combination of two distinct points of `dom f` has value strictly below the larger endpoint value.
-/
def StrictlyQuasiconvex (f : H → EReal) : Prop :=
  IsProper f ∧
    ∀ ⦃x y : H⦄, x ∈ dom f → y ∈ dom f → x ≠ y →
      ∀ ⦃α : ℝ⦄, 0 < α → α < 1 →
        f (α • x + (1 - α) • y) < max (f x) (f y)

/-- A strictly quasiconvex function is proper. -/
theorem StrictlyQuasiconvex.isProper (hf : StrictlyQuasiconvex f) : IsProper f :=
  hf.1

/-- A strictly quasiconvex function satisfies its defining strict max inequality on `dom f`. -/
theorem StrictlyQuasiconvex.ineq
    (hf : StrictlyQuasiconvex f) {x y : H} (hx : x ∈ dom f) (hy : y ∈ dom f)
    (hxy : x ≠ y) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    f (α • x + (1 - α) • y) < max (f x) (f y) :=
  hf.2 hx hy hxy hα0 hα1

/-- Strict quasiconvexity yields the canonical quasiconvexity owner on `Set.univ`. -/
theorem StrictlyQuasiconvex.quasiconvexOn
    (hf : StrictlyQuasiconvex f) :
    QuasiconvexOn ℝ Set.univ f := by
  rw [quasiconvexOn_iff_le_max]
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  by_cases hxy : x = y
  · subst y
    rw [← add_smul, hab, one_smul]
    exact le_max_left (f x) (f x)
  by_cases hab0 : a = 0
  · have hb1 : b = 1 := by linarith
    simp [hab0, hb1]
  by_cases hba0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp [hba0, ha1]
  have ha_pos : 0 < a := lt_of_le_of_ne ha (Ne.symm hab0)
  have hb_pos : 0 < b := lt_of_le_of_ne hb (Ne.symm hba0)
  by_cases hx_top : f x = ⊤
  · simp [hx_top]
  by_cases hy_top : f y = ⊤
  · simp [hy_top]
  · have ha_lt_one : a < 1 := by linarith
    have hb_eq : b = 1 - a := by linarith
    have hx_dom : x ∈ dom f := (mem_dom_iff_ne_top).2 hx_top
    have hy_dom : y ∈ dom f := (mem_dom_iff_ne_top).2 hy_top
    have hlt : f (a • x + b • y) < max (f x) (f y) := by
      simpa [hb_eq] using hf.ineq hx_dom hy_dom hxy ha_pos ha_lt_one
    exact hlt.le

end Strict

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap11/Proposition_11_8 -/

section StrictQuasiconvex

variable {H : Type u} [AddCommMonoid H] [Module ℝ H]

/-- A strictly quasiconvex objective has at most one global minimizer. -/
theorem argmin_subsingleton_of_strictlyQuasiconvex
    {f : H → EReal} (hstrict : StrictlyQuasiconvex f) :
    (Argmin f).Subsingleton := by
  intro x hx y hy
  by_cases hxy : x = y
  · exact hxy
  have hxmin : ∀ z, f x ≤ f z := by
    exact isMinOn_univ_iff.mp ((mem_argmin_iff).mp hx)
  have hymin : ∀ z, f y ≤ f z := by
    exact isMinOn_univ_iff.mp ((mem_argmin_iff).mp hy)
  rcases hstrict.isProper.2 with ⟨z, hz_dom⟩
  have hx_dom : x ∈ dom f := by
    rw [mem_dom_iff_ne_top]
    intro hxtop
    have : (⊤ : EReal) ≤ f z := by simpa [hxtop] using hxmin z
    exact (not_lt_of_ge this) ((mem_dom_iff f z).mp hz_dom)
  have hy_dom : y ∈ dom f := by
    rw [mem_dom_iff_ne_top]
    intro hytop
    have : (⊤ : EReal) ≤ f z := by simpa [hytop] using hymin z
    exact (not_lt_of_ge this) ((mem_dom_iff f z).mp hz_dom)
  let z : H := (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y
  have hstrict_z : f z < max (f x) (f y) :=
    hstrict.ineq hx_dom hy_dom hxy (by norm_num) (by norm_num)
  have hx_z : f x ≤ f z := hxmin z
  have hy_z : f y ≤ f z := hymin z
  have hmax_z : max (f x) (f y) ≤ f z := max_le hx_z hy_z
  exact (not_lt_of_ge hmax_z hstrict_z).elim

end StrictQuasiconvex

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap11/Proposition_11_21 -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Proposition 11.21: the weak limit of a weakly convergent minimizing sequence of a lower
semicontinuous quasiconvex `]-∞,+∞]`-valued function on a real Hilbert space is a global
minimizer. -/
theorem mem_argmin_of_isMinimizingSequence_of_tendsto_weakly_of_quasiconvexOn_univ
    {f : H → EReal} (hf_quasi : QuasiconvexOn ℝ Set.univ f) (hf_lsc : LowerSemicontinuous f)
    {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ) {x : H}
    (hweak : Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x))) :
    x ∈ Argmin f := by
  rw [mem_argmin_iff_eq_sInf]
  have hg_lsc : LowerSemicontinuous (f ∘ (toWeakSpace ℝ H).symm) :=
    weaklyLowerSemicontinuous_of_quasiconvexOn_univ hf_quasi hf_lsc
  have hx_le_liminf : f x ≤ liminf (f ∘ xₙ) atTop := by
    calc
      f x = (f ∘ (toWeakSpace ℝ H).symm) (toWeakSpace ℝ H x) := by
        simp
      _ ≤ liminf (f ∘ (toWeakSpace ℝ H).symm) (nhds (toWeakSpace ℝ H x)) :=
        hg_lsc.le_liminf (toWeakSpace ℝ H x)
      _ ≤ liminf (f ∘ (toWeakSpace ℝ H).symm) (Filter.map (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop) :=
        Filter.liminf_le_liminf_of_le hweak
      _ = liminf (f ∘ xₙ) atTop := by
        rw [← Filter.liminf_comp]
        congr 1
  have hliminf : liminf (f ∘ xₙ) atTop = sInf (Set.range f) := by
    simpa [Function.comp] using hxₙ.tendsto.liminf_eq
  refine le_antisymm ?_ ((isGLB_sInf (Set.range f)).1 (Set.mem_range_self x))
  calc
    f x ≤ liminf (f ∘ xₙ) atTop := hx_le_liminf
    _ = sInf (Set.range f) := hliminf

end

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap11/Proposition_11_29 -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 11 29: reindexing a minimizing sequence by a strictly monotone map
preserves the minimizing-sequence property. -/
theorem IsMinimizingSequence.comp_strictMono
    {f : H → EReal} {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    IsMinimizingSequence f (fun n ↦ xₙ (φ n)) := by
  constructor
  · intro n
    exact hxₙ.mem_dom (φ n)
  · simpa [Function.comp] using hxₙ.tendsto.comp hφ.tendsto_atTop

/-- Helper for Proposition 11 29: if a minimizing sequence eventually falls into one bounded lower
level set, then its whole range is bounded. -/
theorem IsMinimizingSequence.isBounded_range_of_bounded_lowerLevelSet
    {f : H → EReal} {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hlevel_bounded : Bornology.IsBounded (lowerLevelSet f ξ)) :
    Bornology.IsBounded (Set.range xₙ) := by
  have htail : ∀ᶠ n in atTop, xₙ n ∈ lowerLevelSet f ξ := by
    have hle : ∀ᶠ n in atTop, f (xₙ n) ≤ (ξ : EReal) :=
      hxₙ.tendsto.eventually (Iic_mem_nhds hξ)
    simpa [lowerLevelSet, Function.comp] using hle
  rcases eventually_atTop.mp htail with ⟨N, hN⟩
  let s₀ : Set H := xₙ '' {n : ℕ | n < N}
  have hs₀_finite : s₀.Finite := by
    classical
    simpa [s₀] using (Set.finite_lt_nat N).image xₙ
  have hrange_subset : Set.range xₙ ⊆ s₀ ∪ lowerLevelSet f ξ := by
    rintro y ⟨n, rfl⟩
    by_cases hn : n < N
    · exact Or.inl ⟨n, hn, rfl⟩
    · exact Or.inr (hN n (Nat.le_of_not_lt hn))
  exact (hs₀_finite.isBounded.union hlevel_bounded).subset hrange_subset

/-- Helper for Proposition 11 29: every real lower level set strictly above the infimum is
nonempty. -/
theorem lowerLevelSet_nonempty_of_sInf_lt
    {f : H → EReal} {ξ : ℝ} (hξ : sInf (Set.range f) < (ξ : EReal)) :
    (lowerLevelSet f ξ).Nonempty := by
  by_contra hnonempty
  rw [Set.not_nonempty_iff_eq_empty] at hnonempty
  have hbound : ∀ z ∈ Set.range f, (ξ : EReal) ≤ z := by
    intro z hz
    rcases hz with ⟨x, rfl⟩
    have hxnot : x ∉ lowerLevelSet f ξ := by
      simp [hnonempty]
    exact (by
      have hxlt : (ξ : EReal) < f x := by
        simpa [mem_lowerLevelSet_iff, not_le] using hxnot
      exact hxlt.le)
  exact (not_le_of_gt hξ) ((isGLB_sInf (Set.range f)).2 hbound)

/-- Helper for Proposition 11 29: if the indicator augmentation has no `⊥ + ⊤` ambiguity outside
`C`, then its lower level sets are exactly the feasible lower level sets. -/
theorem lowerLevelSet_add_indicator_eq_inter
    {f : H → EReal} {C : Set H} (hbot : ∀ x ∉ C, f x ≠ ⊥) {η : ℝ} :
    lowerLevelSet (f + (ι[C]).asEReal) η = C ∩ lowerLevelSet f η := by
  ext x
  constructor
  · intro hx
    by_cases hxC : x ∈ C
    · refine ⟨hxC, ?_⟩
      simpa [mem_lowerLevelSet_iff, add_indicator_apply, indicator_apply, hxC] using hx
    · have hxle : (f + (ι[C]).asEReal) x ≤ (η : EReal) :=
        (mem_lowerLevelSet_iff (f + (ι[C]).asEReal) η x).1 hx
      have htop : (f + (ι[C]).asEReal) x = ⊤ := by
        simp [indicator_apply, hxC, EReal.add_top_of_ne_bot (hbot x hxC)]
      have : ¬ ((⊤ : EReal) ≤ (η : EReal)) := by
        simp
      rw [htop] at hxle
      exact False.elim <| this hxle
  · rintro ⟨hxC, hxlevel⟩
    refine (mem_lowerLevelSet_iff (f + (ι[C]).asEReal) η x).2 ?_
    simpa [mem_lowerLevelSet_iff, add_indicator_apply, indicator_apply, hxC] using
      (mem_lowerLevelSet_iff f η x).1 hxlevel

/-- Helper for Proposition 11 29: adding the indicator of a closed set preserves lower
semicontinuity once `⊥ + ⊤` is excluded outside the set. -/
theorem lowerSemicontinuous_add_indicator_of_isClosed
    {f : H → EReal} {C : Set H} (hf_lsc : LowerSemicontinuous f) (hC_closed : IsClosed C)
    (hbot : ∀ x ∉ C, f x ≠ ⊥) :
    LowerSemicontinuous (f + (ι[C]).asEReal) := by
  rw [lowerSemicontinuous_iff_isClosed_lowerLevelSet]
  intro η
  rw [lowerLevelSet_add_indicator_eq_inter hbot]
  exact hC_closed.inter ((lowerSemicontinuous_iff_isClosed_lowerLevelSet f).1 hf_lsc η)

/-- Helper for Proposition 11 29: on a lower level set strictly above the infimum, adding the
indicator does not change the infimum of the objective. -/
theorem sInf_range_add_indicator_lowerLevelSet_eq
    {f : H → EReal} {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hbot : ∀ x ∉ lowerLevelSet f ξ, f x ≠ ⊥) :
    sInf (Set.range (f + (ι[lowerLevelSet f ξ]).asEReal)) = sInf (Set.range f) := by
  let C : Set H := lowerLevelSet f ξ
  let g : H → EReal := f + (ι[C]).asEReal
  have hfg : ∀ x, f x ≤ g x := by
    intro x
    by_cases hxC : x ∈ C
    · simp [g, C, indicator_apply, hxC]
    · have htop : g x = ⊤ := by
        simp [g, C, indicator_apply, hxC, EReal.add_top_of_ne_bot (hbot x hxC)]
      rw [htop]
      exact le_top
  apply le_antisymm
  · by_contra hsInf_gt
    have hsInf_lt : sInf (Set.range f) < sInf (Set.range g) := lt_of_not_ge hsInf_gt
    have hmin_lt : sInf (Set.range f) < min (sInf (Set.range g)) (ξ : EReal) :=
      lt_min hsInf_lt hξ
    rcases EReal.lt_iff_exists_real_btwn.mp hmin_lt with ⟨η, hη_left, hη_right⟩
    have hη_lt_sInf_g : (η : EReal) < sInf (Set.range g) :=
      lt_of_lt_of_le hη_right (min_le_left _ _)
    have hη_lt_ξ : (η : EReal) < (ξ : EReal) :=
      lt_of_lt_of_le hη_right (min_le_right _ _)
    rcases lowerLevelSet_nonempty_of_sInf_lt hη_left with ⟨x, hxη⟩
    have hxC : x ∈ C := by
      exact
        (mem_lowerLevelSet_iff f ξ x).2 <|
          le_trans ((mem_lowerLevelSet_iff f η x).1 hxη) hη_lt_ξ.le
    have hxg : g x ≤ (η : EReal) := by
      simpa [g, C, add_indicator_apply, indicator_apply, hxC] using
        (mem_lowerLevelSet_iff f η x).1 hxη
    have hsInf_le : sInf (Set.range g) ≤ g x :=
      (isGLB_sInf (Set.range g)).1 (Set.mem_range_self x)
    exact (not_le_of_gt hη_lt_sInf_g) (le_trans hsInf_le hxg)
  · exact (isGLB_sInf (Set.range g)).2 <| by
      intro z hz
      rcases hz with ⟨x, rfl⟩
      exact le_trans ((isGLB_sInf (Set.range f)).1 (Set.mem_range_self x)) (hfg x)

/-- Helper for Proposition 11 29: a global minimizer of the indicator objective over the lower
level set is already a global minimizer of the original objective. -/
theorem mem_argmin_of_mem_argmin_indicator_lowerLevelSet
    {f : H → EReal} {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hbot : ∀ x ∉ lowerLevelSet f ξ, f x ≠ ⊥) {x : H}
    (hx : x ∈ Argmin (f + (ι[lowerLevelSet f ξ]).asEReal)) :
    x ∈ Argmin f := by
  let C : Set H := lowerLevelSet f ξ
  have hC_nonempty : C.Nonempty := lowerLevelSet_nonempty_of_sInf_lt hξ
  obtain ⟨y, hyC⟩ := hC_nonempty
  have hxmin : IsMinOn (f + (ι[C]).asEReal) Set.univ x := (mem_argmin_iff).1 hx
  have hxle : (f + (ι[C]).asEReal) x ≤ (f + (ι[C]).asEReal) y :=
    (isMinOn_univ_iff.mp hxmin) y
  have hxC : x ∈ C := by
    by_cases hxC : x ∈ C
    · exact hxC
    · have htop : (f + (ι[C]).asEReal) x = ⊤ := by
        simp [C, indicator_apply, hxC, EReal.add_top_of_ne_bot (hbot x hxC)]
      have hytop : (f + (ι[C]).asEReal) y < ⊤ := by
        simpa [C, add_indicator_apply, indicator_apply, hyC] using
          lt_of_le_of_lt ((mem_lowerLevelSet_iff f ξ y).1 hyC) (EReal.coe_lt_top ξ)
      have : ¬ ((⊤ : EReal) ≤ (f + (ι[C]).asEReal) y) := not_le_of_gt hytop
      exact False.elim <| this <| by simpa [htop] using hxle
  have hx_on : x ∈ Argmin[C] f := by
    rw [argminOn_eq_inter_argmin_add_indicator f C hbot]
    exact ⟨hxC, hx⟩
  rcases (mem_argminOn_iff.mp hx_on) with ⟨hxC, hxminC⟩
  rw [mem_argmin_iff, isMinOn_univ_iff]
  intro z
  by_cases hzC : z ∈ C
  · exact (isMinOn_iff.mp hxminC) z hzC
  · have hx_level : f x ≤ (ξ : EReal) := (mem_lowerLevelSet_iff f ξ x).1 hxC
    have hz_gt : (ξ : EReal) < f z := by
      simpa [C, mem_lowerLevelSet_iff, not_le] using hzC
    exact le_trans hx_level hz_gt.le

/-- Helper for Proposition 11 29: a strictly quasiconvex indicator-augmented objective has at
most one constrained minimizer. -/
theorem argminOn_subsingleton_of_indicator_objective_strictlyQuasiconvex
    {f : H → EReal} {C : Set H}
    (hstrict : StrictlyQuasiconvex (f + (ι[C]).asEReal)) :
    (Argmin[C] f).Subsingleton := by
  have hbot : ∀ x ∉ C, f x ≠ ⊥ := by
    intro x hxC hfx
    have hg : (f + (ι[C]).asEReal) x ≠ ⊥ := hstrict.isProper.1 x
    exact hg <| by simp [hxC, hfx]
  rw [argminOn_eq_inter_argmin_add_indicator f C hbot]
  intro x hx y hy
  by_cases hxy : x = y
  · exact hxy
  have hxmin : ∀ z, (f + (ι[C]).asEReal) x ≤ (f + (ι[C]).asEReal) z := by
    exact isMinOn_univ_iff.mp ((mem_argmin_iff).mp hx.2)
  have hymin : ∀ z, (f + (ι[C]).asEReal) y ≤ (f + (ι[C]).asEReal) z := by
    exact isMinOn_univ_iff.mp ((mem_argmin_iff).mp hy.2)
  rcases hstrict.isProper.2 with ⟨z, hz_dom⟩
  have hx_dom : x ∈ dom (f + (ι[C]).asEReal) := by
    rw [mem_dom_iff_ne_top]
    intro hxtop
    have : (⊤ : EReal) ≤ (f + (ι[C]).asEReal) z := by
      simpa [hxtop] using hxmin z
    exact (not_lt_of_ge this) ((mem_dom_iff (f + (ι[C]).asEReal) z).mp hz_dom)
  have hy_dom : y ∈ dom (f + (ι[C]).asEReal) := by
    rw [mem_dom_iff_ne_top]
    intro hytop
    have : (⊤ : EReal) ≤ (f + (ι[C]).asEReal) z := by
      simpa [hytop] using hymin z
    exact (not_lt_of_ge this) ((mem_dom_iff (f + (ι[C]).asEReal) z).mp hz_dom)
  let z : H := (1 / 2 : ℝ) • x + (1 - (1 / 2 : ℝ)) • y
  have hstrict_z :
      (f + (ι[C]).asEReal) z <
        max ((f + (ι[C]).asEReal) x) ((f + (ι[C]).asEReal) y) :=
    hstrict.ineq hx_dom hy_dom hxy (by norm_num) (by norm_num)
  have hx_z : (f + (ι[C]).asEReal) x ≤ (f + (ι[C]).asEReal) z := hxmin z
  have hy_z : (f + (ι[C]).asEReal) y ≤ (f + (ι[C]).asEReal) z := hymin z
  have hmax_z :
      max ((f + (ι[C]).asEReal) x) ((f + (ι[C]).asEReal) y) ≤
        (f + (ι[C]).asEReal) z :=
    max_le hx_z hy_z
  exact (not_lt_of_ge hmax_z hstrict_z).elim

section CompleteSpace

variable [CompleteSpace H]

/-- Proposition 11 29 (1): clause (i). If some lower level set strictly above the infimum of `f`
is bounded, then every minimizing sequence of `f` has a weak sequential cluster point. -/
theorem IsMinimizingSequence.exists_weakSequentialClusterPoint_of_bounded_lowerLevelSet
    {f : H → EReal} {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hlevel_bounded : Bornology.IsBounded (lowerLevelSet f ξ)) :
    ∃ x : H,
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x) := by
  have hrange_bounded :
      Bornology.IsBounded (Set.range xₙ) :=
    hxₙ.isBounded_range_of_bounded_lowerLevelSet hξ hlevel_bounded
  obtain ⟨r, hrange_subset⟩ := hrange_bounded.subset_closedBall (0 : H)
  obtain ⟨x, -, φ, hφ, hφx⟩ :=
    exists_subsequence_tendsto_weakly_mem_of_bounded_isClosed_convex
      Metric.isBounded_closedBall Metric.isClosed_closedBall (convex_closedBall (0 : H) r) xₙ
      (fun n ↦ hrange_subset (Set.mem_range_self n))
  exact ⟨x, ⟨φ, hφ, by simpa [Function.comp] using hφx⟩⟩

end CompleteSpace

/-- Proposition 11 29 (2): clause (i). Every weak sequential cluster point of a minimizing
sequence of a lower semicontinuous quasiconvex function is a global minimizer. -/
theorem IsSequentialClusterPt.mem_argmin_of_isMinimizingSequence_of_quasiconvexOn_univ
    {f : H → EReal} {xₙ : ℕ → H} {x : H}
    (hx : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x))
    (hf_quasi : QuasiconvexOn ℝ Set.univ f) (hf_lsc : LowerSemicontinuous f)
    (hxₙ : IsMinimizingSequence f xₙ) :
    x ∈ Argmin f := by
  rcases hx.exists_subseq_tendsto with ⟨φ, hφ, hφx⟩
  exact
    mem_argmin_of_isMinimizingSequence_of_tendsto_weakly_of_quasiconvexOn_univ
      hf_quasi hf_lsc (hxₙ.comp_strictMono hφ) <| by
        simpa [Function.comp] using hφx

section CompleteSpace

variable [CompleteSpace H]

/-- Proposition 11 29 (3): clause (ii). If `f + ι_C` is strictly quasiconvex for
`C = lowerLevelSet f ξ`, then `f` has a unique global minimizer. -/
theorem existsUnique_mem_argmin_of_strictlyQuasiconvex_indicator_lowerLevelSet
    {f : H → EReal} (hf_lsc : LowerSemicontinuous f) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hlevel_bounded : Bornology.IsBounded (lowerLevelSet f ξ))
    (hstrict : StrictlyQuasiconvex (f + (ι[lowerLevelSet f ξ]).asEReal)) :
    ∃! x : H, x ∈ Argmin f := by
  let C : Set H := lowerLevelSet f ξ
  let g : H → EReal := f + (ι[C]).asEReal
  have hbot : ∀ x ∉ C, f x ≠ ⊥ := by
    intro x hxC hfx
    exact (hstrict.isProper.1 x) <| by simp [C, hxC, hfx]
  have hC_closed : IsClosed C := by
    simpa [C] using (lowerSemicontinuous_iff_isClosed_lowerLevelSet f).1 hf_lsc ξ
  have hlevel_nonempty : (lowerLevelSet g ξ).Nonempty := by
    rcases lowerLevelSet_nonempty_of_sInf_lt hξ with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [lowerLevelSet_add_indicator_eq_inter hbot]
    exact ⟨hx, hx⟩
  have hlevel_bounded_g : Bornology.IsBounded (lowerLevelSet g ξ) := by
    rw [lowerLevelSet_add_indicator_eq_inter hbot]
    simpa [C, Set.inter_self] using hlevel_bounded
  have hg_lsc : LowerSemicontinuous g :=
    lowerSemicontinuous_add_indicator_of_isClosed hf_lsc hC_closed hbot
  have hg_arg_nonempty : (Argmin g).Nonempty := by
    simpa [g] using
      argminOn_nonempty_of_quasiconvexOn_univ_of_nonempty_bounded_inter_lowerLevelSet
        (f := g) (C := Set.univ) hstrict.quasiconvexOn hg_lsc isClosed_univ convex_univ ξ
        (by simpa using hlevel_nonempty) (by simpa using hlevel_bounded_g)
  rcases hg_arg_nonempty with ⟨x, hxg⟩
  have hx_argmin : x ∈ Argmin f :=
    mem_argmin_of_mem_argmin_indicator_lowerLevelSet hξ hbot hxg
  refine ⟨x, hx_argmin, ?_⟩
  intro y hy
  have hyC : y ∈ C := by
    exact
      (mem_lowerLevelSet_iff f ξ y).2 <| by
        calc
          f y = sInf (Set.range f) := (mem_argmin_iff_eq_sInf).1 hy
          _ ≤ (ξ : EReal) := hξ.le
  have hy_on : y ∈ Argmin[C] f := by
    rw [mem_argminOn_iff, isMinOn_iff]
    refine ⟨hyC, ?_⟩
    intro z hz
    exact (isMinOn_univ_iff.mp ((mem_argmin_iff).1 hy)) z
  have hx_on : x ∈ Argmin[C] f := by
    rw [mem_argminOn_iff, isMinOn_iff]
    refine ⟨?_, ?_⟩
    · exact
        (mem_lowerLevelSet_iff f ξ x).2 <|
          le_trans ((mem_argmin_iff_eq_sInf).1 hx_argmin).le hξ.le
    · intro z hz
      exact (isMinOn_univ_iff.mp ((mem_argmin_iff).1 hx_argmin)) z
  exact
    (argminOn_subsingleton_of_indicator_objective_strictlyQuasiconvex
      (f := f) (C := C) hstrict)
    hy_on hx_on

end CompleteSpace

end

end ERealFunction


namespace ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap11/Proposition_11_14 -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- A `Γ₀(H)` function is bounded below by a global affine function of the norm. -/
theorem exists_linear_lower_bound_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    ∃ R C : ℝ, ∀ x : H, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ (f x : EReal)) := by
  let _ : CompleteSpace H := inferInstance
  rcases hf.2.nonempty with ⟨p, hp⟩
  let ξ : ℝ := (f p : EReal).toReal - 1
  have hp_top : (f p : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hp)
  have hp_bot : (f p : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f p : EReal) from (f p).2)
  have hξ_lt_fp : (ξ : EReal) < (f p : EReal) := by
    rw [show (f p : EReal) = (((f p : EReal).toReal : ℝ) : EReal) by
      symm
      exact EReal.coe_toReal hp_top hp_bot]
    exact_mod_cast (show ξ < (f p : EReal).toReal by
      dsimp [ξ]
      linarith)
  have hopen : IsOpen (f.asEReal ⁻¹' Set.Ioi (ξ : EReal)) := hf.1.isOpen_preimage (ξ : EReal)
  have hp_mem : p ∈ f.asEReal ⁻¹' Set.Ioi (ξ : EReal) := by
    simpa [Function.asEReal] using hξ_lt_fp
  rcases Metric.isOpen_iff.mp hopen p hp_mem with ⟨r, hr_pos, hr_subset⟩
  let δ : ℝ := r / 2
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    linarith
  refine ⟨δ⁻¹, 1 + ‖p‖ / δ - (f p : EReal).toReal, ?_⟩
  intro x
  by_cases hx : x ∈ effectiveDomain f
  · have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    by_cases hnear : ‖x - p‖ < δ
    · have hball : x ∈ Metric.ball p r := by
        have : ‖x - p‖ < r := by
          dsimp [δ] at hnear
          linarith
        simpa [Metric.mem_ball, dist_eq_norm] using this
      have hξ_lt_fx : (ξ : EReal) < (f x : EReal) := by
        exact hr_subset hball
      have hbound_real :
          -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) ≤ ξ := by
        dsimp [ξ]
        have hnonneg : 0 ≤ δ⁻¹ * ‖x‖ + ‖p‖ / δ := by
          positivity
        linarith
      have hbound_ereal :
          (((-δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) : ℝ) : EReal)) ≤ (ξ : EReal) := by
        exact_mod_cast hbound_real
      exact le_trans hbound_ereal hξ_lt_fx.le
    · have hfar : δ ≤ ‖x - p‖ := le_of_not_gt hnear
      have hxp_pos : 0 < ‖x - p‖ := lt_of_lt_of_le hδ_pos hfar
      let t : ℝ := δ / ‖x - p‖
      let y : H := t • x + (1 - t) • p
      have ht_pos : 0 < t := by
        dsimp [t]
        exact div_pos hδ_pos hxp_pos
      have ht_le_one : t ≤ 1 := by
        dsimp [t]
        exact (div_le_iff₀ hxp_pos).2 (by simpa [one_mul] using hfar)
      have hy_sub : y - p = t • (x - p) := by
        dsimp [y]
        calc
          t • x + (1 - t) • p - p = t • x + ((1 - t) • p - p) := by abel
          _ = t • x + (((1 - t) - 1) • p) := by
            congr 1
            calc
              (1 - t) • p - p = (1 - t) • p - (1 : ℝ) • p := by rw [one_smul]
              _ = (((1 - t) - 1) : ℝ) • p := by rw [← sub_smul]
          _ = t • x + (-t) • p := by ring_nf
          _ = t • x - t • p := by rw [sub_eq_add_neg, neg_smul]
          _ = t • (x - p) := by rw [smul_sub]
      have hy_ball : y ∈ Metric.ball p r := by
        have hnorm : ‖y - p‖ < r := by
          calc
            ‖y - p‖ = ‖t • (x - p)‖ := by rw [hy_sub]
            _ = |t| * ‖x - p‖ := norm_smul t (x - p)
            _ = t * ‖x - p‖ := by rw [abs_of_pos ht_pos]
            _ = δ := by
                  dsimp [t]
                  field_simp [hxp_pos.ne']
            _ < r := by
                  dsimp [δ]
                  linarith
        simpa [Metric.mem_ball, dist_eq_norm] using hnorm
      have hξ_lt_fy : (ξ : EReal) < (f y : EReal) := hr_subset hy_ball
      have hconv :
          (f y : EReal) ≤ (t : EReal) * (f x : EReal) + ((1 - t : ℝ) : EReal) * (f p : EReal) := by
        by_cases ht_one : t = 1
        · simp [y, ht_one]
        · have ht_lt_one : t < 1 := lt_of_le_of_ne ht_le_one ht_one
          simpa [y] using hf.2.ineq (x := x) hx (y := p) hp (α := t) ht_pos ht_lt_one
      have hterm1_ne_top : (t : EReal) * (f x : EReal) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨Or.inl (EReal.coe_ne_bot t), Or.inl ?_, Or.inl (EReal.coe_ne_top t), Or.inr hx_top⟩
        exact_mod_cast ht_pos.le
      have hterm2_ne_top : ((1 - t : ℝ) : EReal) * (f p : EReal) ≠ ⊤ := by
        rw [EReal.mul_ne_top]
        refine ⟨Or.inl (EReal.coe_ne_bot (1 - t)), Or.inl ?_,
          Or.inl (EReal.coe_ne_top (1 - t)), Or.inr hp_top⟩
        exact_mod_cast sub_nonneg.mpr ht_le_one
      have hright_ne_top :
          (t : EReal) * (f x : EReal) + ((1 - t : ℝ) : EReal) * (f p : EReal) ≠ ⊤ :=
        EReal.add_ne_top hterm1_ne_top hterm2_ne_top
      have hy_top : (f y : EReal) ≠ ⊤ := by
        intro hy_top
        have : (⊤ : EReal) ≤
            (t : EReal) * (f x : EReal) + ((1 - t : ℝ) : EReal) * (f p : EReal) := by
          simpa [hy_top] using hconv
        exact hright_ne_top (top_unique this)
      have hy_dom : y ∈ effectiveDomain f := by
        exact mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top hy_top)
      have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
      have hξ_lt_fy_real : ξ < (f y : EReal).toReal := by
        rw [← EReal.coe_toReal hy_top hy_bot] at hξ_lt_fy
        exact EReal.coe_lt_coe_iff.1 hξ_lt_fy
      have hconv_real :
          (f y : EReal).toReal ≤ t * (f x : EReal).toReal + (1 - t) * (f p : EReal).toReal := by
        have hconv_cast :
            (((f y : EReal).toReal : ℝ) : EReal) ≤
              (t : EReal) * (((f x : EReal).toReal : ℝ) : EReal) +
                ((1 - t : ℝ) : EReal) * (((f p : EReal).toReal : ℝ) : EReal) := by
          simpa [EReal.coe_toReal hx_top hx_bot, EReal.coe_toReal hy_top hy_bot,
            EReal.coe_toReal hp_top hp_bot] using hconv
        exact EReal.coe_le_coe_iff.1 (by
          simpa [EReal.coe_mul, EReal.coe_add] using hconv_cast)
      have hfx_real :
          -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) < (f x : EReal).toReal := by
        have hdist : ‖x - p‖ ≤ ‖x‖ + ‖p‖ := by
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using norm_sub_le x p
        have hmain : (f p : EReal).toReal - 1 / t < (f x : EReal).toReal := by
          have haux : ξ < t * (f x : EReal).toReal + (1 - t) * (f p : EReal).toReal :=
            lt_of_lt_of_le hξ_lt_fy_real hconv_real
          have hsub : -1 < t * ((f x : EReal).toReal - (f p : EReal).toReal) := by
            dsimp [ξ] at haux
            linarith
          have hdiv : -1 / t < (f x : EReal).toReal - (f p : EReal).toReal := by
            exact (div_lt_iff₀ ht_pos).2 (by simpa [mul_comm] using hsub)
          have hmain_shift :
              (f p : EReal).toReal + (-1 / t) <
                (f p : EReal).toReal + ((f x : EReal).toReal - (f p : EReal).toReal) :=
            add_lt_add_right hdiv (f p : EReal).toReal
          calc
            (f p : EReal).toReal - 1 / t = (f p : EReal).toReal + (-1 / t) := by ring
            _ < (f p : EReal).toReal + ((f x : EReal).toReal - (f p : EReal).toReal) :=
              hmain_shift
            _ = (f x : EReal).toReal := by ring
        have ht_inv : 1 / t = ‖x - p‖ / δ := by
          dsimp [t]
          field_simp [hxp_pos.ne', hδ_pos.ne']
        rw [ht_inv] at hmain
        have hratio : ‖x - p‖ / δ ≤ ‖x‖ / δ + ‖p‖ / δ := by
          have := div_le_div_of_nonneg_right hdist hδ_pos.le
          simpa [add_div] using this
        have hleft_le :
            (f p : EReal).toReal - 1 - (‖x‖ / δ + ‖p‖ / δ) ≤
              (f p : EReal).toReal - ‖x - p‖ / δ := by
          linarith
        have hfinal :
            (f p : EReal).toReal - 1 - (‖x‖ / δ + ‖p‖ / δ) < (f x : EReal).toReal :=
          lt_of_le_of_lt hleft_le hmain
        have hrewrite :
            -δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) =
              (f p : EReal).toReal - 1 - (‖x‖ / δ + ‖p‖ / δ) := by
          rw [div_eq_mul_inv, div_eq_mul_inv]
          ring
        rw [hrewrite]
        exact hfinal
      have hfx_ereal :
          (((-δ⁻¹ * ‖x‖ - (1 + ‖p‖ / δ - (f p : EReal).toReal) : ℝ) : EReal)) <
            (f x : EReal) := by
        rw [show (f x : EReal) = (((f x : EReal).toReal : ℝ) : EReal) by
          symm
          exact EReal.coe_toReal hx_top hx_bot]
        exact_mod_cast hfx_real
      exact hfx_ereal.le
  · have hx_top : (f x : EReal) = ⊤ := by
      apply le_antisymm le_top
      apply not_lt.mp
      intro hxtop
      exact hx (mem_effectiveDomain_iff.mpr hxtop)
    simp [hx_top]

section

variable {H : Type u} [NormedAddCommGroup H]

/-- Helper for Proposition 11 14: a global linear lower bound yields a uniform lower bound for
the normalized values `f x / ‖x‖` on the tail `‖x‖ ≥ 1`. -/
private theorem linear_lower_bound_div_norm
    {f : H → Set.Ioi (⊥ : EReal)} {R C : ℝ}
    (hbound : ∀ x : H, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ (f x : EReal)))
    {x : H} (hnorm : (1 : ℝ) ≤ ‖x‖) :
    ((-(R + |C|) : ℝ) : EReal) ≤ (f x : EReal) / ‖x‖ := by
  have hnorm_pos_real : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hnorm
  have hnorm_pos : (0 : EReal) < ‖x‖ := by
    exact EReal.coe_pos.2 hnorm_pos_real
  have hC_scaled : -(‖x‖ * |C|) ≤ -C := by
    have hC_le : C ≤ ‖x‖ * |C| := by
      have habs_le : |C| ≤ ‖x‖ * |C| := by
        simpa [one_mul, mul_comm] using mul_le_mul_of_nonneg_right hnorm (abs_nonneg C)
      exact le_trans (le_abs_self C) habs_le
    simpa [mul_comm] using neg_le_neg hC_le
  have hreal :
      (-(R + |C|)) * ‖x‖ ≤ -R * ‖x‖ - C := by
    calc
      (-(R + |C|)) * ‖x‖ = -(R * ‖x‖) + -(‖x‖ * |C|) := by ring
      _ ≤ -R * ‖x‖ - C := by linarith
  have hcast :
      ((((-(R + |C|)) * ‖x‖ : ℝ) : EReal)) ≤
        (((-R * ‖x‖ - C : ℝ) : EReal)) := by
    exact_mod_cast hreal
  have hmul_le :
      ((((-(R + |C|) : ℝ) : EReal) * ‖x‖)) ≤ (f x : EReal) := by
    calc
      (((-(R + |C|) : ℝ) : EReal) * ‖x‖)
          = ((((-(R + |C|)) * ‖x‖ : ℝ) : EReal)) := by
              rw [← EReal.coe_mul]
      _ ≤ (((-R * ‖x‖ - C : ℝ) : EReal)) := hcast
      _ ≤ (f x : EReal) := hbound x
  exact (EReal.le_div_iff_mul_le hnorm_pos (by simp)).2 hmul_le

end

section

variable {H : Type u} [NormedAddCommGroup H]

/-- Helper for Proposition 11 14: adding a summand with a global linear lower bound to a
supercoercive summand preserves supercoercivity. -/
private theorem pointwiseAdd_supercoercive_of_linear_lower_bound
    {f g : H → Set.Ioi (⊥ : EReal)}
    (hbound : ∃ R C : ℝ, ∀ x : H, (((-R * ‖x‖ - C : ℝ) : EReal) ≤ (f x : EReal)))
    (hg_super : Supercoercive g.asEReal) :
    Supercoercive (f + g).asEReal := by
  rcases hbound with ⟨R, C, hbound⟩
  rw [Supercoercive, EReal.tendsto_nhds_top_iff_real] at hg_super ⊢
  intro ξ
  have hnorm_tail : ∀ᶠ x in Bornology.cobounded H, (1 : ℝ) ≤ ‖x‖ := by
    simpa using
      (eventually_cobounded_le_norm (1 : ℝ) :
        ∀ᶠ x in Bornology.cobounded H, (1 : ℝ) ≤ ‖x‖)
  have hg_tail :
      ∀ᶠ x in Bornology.cobounded H, ((ξ + (R + |C|) : ℝ) : EReal) < g.asEReal x / ‖x‖ :=
    hg_super (ξ + (R + |C|))
  filter_upwards [hnorm_tail, hg_tail] with x hnorm hxg
  have hf_tail :
      ((-(R + |C|) : ℝ) : EReal) ≤ (f x : EReal) / ‖x‖ :=
    linear_lower_bound_div_norm hbound hnorm
  have hsum :
      (((ξ + (R + |C|) : ℝ) : EReal) + ((-(R + |C|) : ℝ) : EReal)) = (ξ : EReal) := by
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff]
    ring
  have hquot_split :
      ((f + g).asEReal x) / ‖x‖ = (f x : EReal) / ‖x‖ + (g x : EReal) / ‖x‖ := by
    have hnorm_nonneg : (0 : EReal) ≤ (‖x‖ : EReal) := by
      exact_mod_cast norm_nonneg x
    have happly : (((f + g) x : Set.Ioi (⊥ : EReal)) : EReal) = (f x : EReal) + (g x : EReal) :=
      rfl
    rw [Function.asEReal_apply, happly]
    simpa using
      (EReal.add_div_of_nonneg_right
        (a := (f x : EReal)) (b := (g x : EReal)) (c := (‖x‖ : EReal)) hnorm_nonneg)
  have hadd :
      ((ξ + (R + |C|) : ℝ) : EReal) + ((-(R + |C|) : ℝ) : EReal) <
        (g x : EReal) / ‖x‖ + (f x : EReal) / ‖x‖ := by
    have hright_bot : (f x : EReal) / ‖x‖ ≠ ⊥ := by
      exact ne_bot_of_le_ne_bot (by simp) hf_tail
    exact EReal.add_lt_add_of_lt_of_le' hxg hf_tail hright_bot (by
      intro _ hz
      exact (EReal.coe_ne_top _ hz).elim)
  calc
    (ξ : EReal)
        = (((ξ + (R + |C|) : ℝ) : EReal) + ((-(R + |C|) : ℝ) : EReal)) := hsum.symm
    _ < (g x : EReal) / ‖x‖ + (f x : EReal) / ‖x‖ := hadd
    _ = (f x : EReal) / ‖x‖ + (g x : EReal) / ‖x‖ := by rw [add_comm]
    _ = ((f + g).asEReal x) / ‖x‖ := hquot_split.symm

end

/-- Proposition 11 14: if `f ∈ Γ₀(H)` and `g` is supercoercive, then the canonical underlying
extended-real-valued pointwise sum `(f + g).asEReal` is supercoercive. -/
theorem pointwiseAdd_supercoercive_of_mem_gammaZero
    (f g : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H))
    (hg_super : Supercoercive g.asEReal) :
    Supercoercive (f + g).asEReal := by
  let _ : CompleteSpace H := inferInstance
  rcases exists_linear_lower_bound_of_mem_gammaZero hf with ⟨R, C, hbound⟩
  exact pointwiseAdd_supercoercive_of_linear_lower_bound ⟨R, C, hbound⟩ hg_super

end

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap11/Proposition_11_29 (convergence upgrade) -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Helper for Proposition 11 29: a subsequence that stays inside the lower level set is a
minimizing sequence for the indicator-augmented objective. -/
theorem IsMinimizingSequence.comp_add_indicator_lowerLevelSet
    {f : H → EReal} {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hbot : ∀ x ∉ lowerLevelSet f ξ, f x ≠ ⊥)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (hφC : ∀ n, xₙ (φ n) ∈ lowerLevelSet f ξ) :
    IsMinimizingSequence (f + (ι[lowerLevelSet f ξ]).asEReal) (fun n ↦ xₙ (φ n)) := by
  let g : H → EReal := f + (ι[lowerLevelSet f ξ]).asEReal
  have hsub : IsMinimizingSequence f (fun n ↦ xₙ (φ n)) :=
    hxₙ.comp_strictMono hφ
  constructor
  · intro n
    rw [mem_dom_iff]
    simpa [g, indicator_apply, hφC n] using hsub.lt_top n
  · have hEq :
        (fun n ↦ g (xₙ (φ n))) = fun n ↦ f (xₙ (φ n)) := by
      funext n
      simp [g, indicator_apply, hφC n]
    rw [show (g ∘ fun n ↦ xₙ (φ n)) = fun n ↦ g (xₙ (φ n)) by rfl, hEq]
    simpa [g, Function.comp, sInf_range_add_indicator_lowerLevelSet_eq hξ hbot] using hsub.tendsto

/-- Helper for Proposition 11 29: every weak sequential cluster point of a minimizing sequence is
already a global minimizer once the indicator-augmented objective is strictly quasiconvex on the
relevant lower level set. -/
theorem IsSequentialClusterPt.mem_argmin_of_indicator_objective_strictlyQuasiconvex
    {f : H → EReal} {xₙ : ℕ → H} {x : H}
    (hx : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x))
    (hf_lsc : LowerSemicontinuous f) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hxₙ : IsMinimizingSequence f xₙ)
    (hstrict : StrictlyQuasiconvex (f + (ι[lowerLevelSet f ξ]).asEReal)) :
    x ∈ Argmin f := by
  let C : Set H := lowerLevelSet f ξ
  let g : H → EReal := f + (ι[C]).asEReal
  have hbot : ∀ y ∉ C, f y ≠ ⊥ := by
    intro y hyC hfy
    exact (hstrict.isProper.1 y) <| by simp [C, hyC, hfy]
  have hC_closed : IsClosed C := by
    simpa [C] using (lowerSemicontinuous_iff_isClosed_lowerLevelSet f).1 hf_lsc ξ
  have hg_lsc : LowerSemicontinuous g :=
    lowerSemicontinuous_add_indicator_of_isClosed hf_lsc hC_closed hbot
  rcases hx.exists_subseq_tendsto with ⟨φ, hφ, hφx⟩
  have htailC : ∀ᶠ n in atTop, xₙ n ∈ C := by
    have hle : ∀ᶠ n in atTop, f (xₙ n) ≤ (ξ : EReal) :=
      hxₙ.tendsto.eventually (Iic_mem_nhds hξ)
    simpa [C, lowerLevelSet, Function.comp] using hle
  have hsubtailC : ∀ᶠ n in atTop, xₙ (φ n) ∈ C :=
    hφ.tendsto_atTop.eventually htailC
  rcases eventually_atTop.mp hsubtailC with ⟨N, hN⟩
  let ψ : ℕ → ℕ := fun n ↦ φ (n + N)
  have hadd : StrictMono (fun n : ℕ ↦ n + N) := by
    intro m n hmn
    exact Nat.add_lt_add_right hmn N
  have hψ : StrictMono ψ := hφ.comp hadd
  have hψx :
      Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ (ψ n))) atTop (𝓝 (toWeakSpace ℝ H x)) := by
    simpa [ψ, Function.comp] using hφx.comp (tendsto_add_atTop_nat N)
  have hψC : ∀ n, xₙ (ψ n) ∈ C := by
    intro n
    simpa [ψ] using hN (n + N) (Nat.le_add_left N n)
  have hψ_min : IsMinimizingSequence g (fun n ↦ xₙ (ψ n)) :=
    hxₙ.comp_add_indicator_lowerLevelSet hξ hbot hψ hψC
  have hxg : x ∈ Argmin g :=
    mem_argmin_of_isMinimizingSequence_of_tendsto_weakly_of_quasiconvexOn_univ
      hstrict.quasiconvexOn hg_lsc hψ_min hψx
  exact mem_argmin_of_mem_argmin_indicator_lowerLevelSet hξ hbot hxg

namespace IsMinimizingSequence

/-- Proposition 11 29 (4): clause (ii). Under the same strict quasiconvexity hypothesis, the
minimizing sequence converges weakly to a global minimizer of `f`. -/
theorem exists_mem_argmin_and_tendsto_toWeakSpace_of_strictlyQuasiconvex_indicator_lowerLevelSet
    {f : H → EReal} {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ)
    (hf_lsc : LowerSemicontinuous f) {ξ : ℝ}
    (hξ : sInf (Set.range f) < (ξ : EReal))
    (hlevel_bounded : Bornology.IsBounded (lowerLevelSet f ξ))
    (hstrict : StrictlyQuasiconvex (f + (ι[lowerLevelSet f ξ]).asEReal)) :
    ∃ x ∈ Argmin f,
      Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x)) := by
  have hbounded :
      Bornology.IsBounded (Set.range xₙ) :=
    hxₙ.isBounded_range_of_bounded_lowerLevelSet hξ hlevel_bounded
  obtain ⟨x₀, hx₀_argmin, hx₀_unique⟩ :=
    existsUnique_mem_argmin_of_strictlyQuasiconvex_indicator_lowerLevelSet
      hf_lsc hξ hlevel_bounded hstrict
  have hunique :
      ∀ y z : H,
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H y) →
        IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H z) →
        y = z := by
    intro y z hy hz
    have hy_arg : y ∈ Argmin f := by
      exact
        IsSequentialClusterPt.mem_argmin_of_indicator_objective_strictlyQuasiconvex
          hy hf_lsc hξ hxₙ hstrict
    have hz_arg : z ∈ Argmin f := by
      exact
        IsSequentialClusterPt.mem_argmin_of_indicator_objective_strictlyQuasiconvex
          hz hf_lsc hξ hxₙ hstrict
    calc
      y = x₀ := hx₀_unique y hy_arg
      _ = z := (hx₀_unique z hz_arg).symm
  rcases (weaklyConvergent_iff_bounded_and_atMostOne_weakSequentialClusterPoint xₙ).2
      ⟨hbounded, hunique⟩ with ⟨x, hx_tendsto⟩
  have hx_cluster :
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x) := by
    refine ⟨fun n ↦ n, fun _ _ h ↦ h, ?_⟩
    simpa [Function.comp] using hx_tendsto
  have hx_arg : x ∈ Argmin f := by
    exact
      IsSequentialClusterPt.mem_argmin_of_indicator_objective_strictlyQuasiconvex
        hx_cluster hf_lsc hξ hxₙ hstrict
  exact ⟨x, hx_arg, hx_tendsto⟩

end IsMinimizingSequence

end

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap11/Proposition_11_15 -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Proposition 11.15: if `f ∈ Γ₀(H)`, if `C` is a nonempty closed convex set, and if either (i)
the coerced function `x ↦ (f x : EReal)` is coercive or (ii) `C` is bounded, then `f` attains a
minimum over `C`. -/
theorem argminOn_nonempty_of_mem_gammaZero_of_coercive_or_bounded
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {C : Set H} (hC_closed : IsClosed C)
    (hC_convex : Convex ℝ C) (hC_nonempty : C.Nonempty)
    (hcase : Coercive f.asEReal ∨ Bornology.IsBounded C) :
    (Argmin[C] f.asEReal).Nonempty := by
  by_cases hC_dom : (C ∩ effectiveDomain f).Nonempty
  · rcases hC_dom with ⟨x, hxC, hxdom⟩
    let ξ : ℝ := (f x : EReal).toReal
    have hx_level : x ∈ lowerLevelSet f.asEReal ξ := by
      rw [mem_lowerLevelSet_iff]
      exact EReal.le_coe_toReal (ne_of_lt (mem_effectiveDomain_iff.mp hxdom))
    have hlevel_nonempty : (C ∩ lowerLevelSet f.asEReal ξ).Nonempty := ⟨x, hxC, hx_level⟩
    have hlevel_bounded : Bornology.IsBounded (C ∩ lowerLevelSet f.asEReal ξ) := by
      rcases hcase with hf_coe | hC_bounded
      · have hbounded : Bornology.IsBounded (lowerLevelSet f.asEReal ξ) :=
          (coercive_iff_bounded_lowerLevelSet f.asEReal).1 hf_coe ξ
        exact hbounded.subset (fun _ hy ↦ hy.2)
      · exact hC_bounded.subset (fun _ hy ↦ hy.1)
    have hconv_epi : Convex ℝ (epigraph f.asEReal) := by
      refine (convex_epigraph_iff_jensen_on_dom f.asEReal).2 ?_
      intro y z hy hz a ha ha_lt_one
      have hy' : y ∈ effectiveDomain f := by
        simpa [effectiveDomain, dom] using hy
      have hz' : z ∈ effectiveDomain f := by
        simpa [effectiveDomain, dom] using hz
      simpa using hf.2.ineq hy' hz' ha ha_lt_one
    have hf_quasi : QuasiconvexOn ℝ Set.univ f.asEReal := by
      rw [quasiconvexOn_univ_iff_convex_lowerLevelSet f.asEReal]
      intro η
      exact convex_lowerLevelSet_of_convex_epigraph f.asEReal η hconv_epi
    exact
      argminOn_nonempty_of_quasiconvexOn_univ_of_nonempty_bounded_inter_lowerLevelSet
        hf_quasi hf.1 hC_closed hC_convex ξ hlevel_nonempty hlevel_bounded
  · rcases hC_nonempty with ⟨x, hxC⟩
    have htop : ∀ {y : H}, y ∈ C → f.asEReal y = ⊤ := by
      intro y hyC
      have hy_not_dom : y ∉ effectiveDomain f := by
        intro hy_dom
        exact hC_dom ⟨y, hyC, hy_dom⟩
      exact le_antisymm le_top <| not_lt.mp <| by
        simpa [mem_effectiveDomain_iff] using hy_not_dom
    refine ⟨x, ?_⟩
    rw [mem_argminOn_iff, isMinOn_iff]
    refine ⟨hxC, ?_⟩
    intro y hyC
    simp [htop hxC, htop hyC]

end

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap11/Corollary_11_9 -/

section

variable {H : Type u} [AddCommGroup H] [Module ℝ H]

/-- A source-facing strictly convex `]-∞,+∞]`-valued function with nonempty effective domain
yields the strictly quasiconvex owner on its canonical underlying `EReal`-valued function. -/
theorem StrictlyConvex.toStrictlyQuasiconvex_asEReal
    {f : H → Set.Ioi (⊥ : EReal)} (hstrict : StrictlyConvex f)
    (hdom : (effectiveDomain f).Nonempty) :
    StrictlyQuasiconvex f.asEReal := by
  refine ⟨?_, ?_⟩
  · refine ⟨fun x ↦ ne_of_gt (f x).2, ?_⟩
    simpa [effectiveDomain, dom] using hdom
  intro x y hx hy hxy α hα0 hα1
  have hx_eff : x ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hx
  have hy_eff : y ∈ effectiveDomain f := by
    simpa [effectiveDomain, dom] using hy
  have hsub_cast : (((1 - α : ℝ) : EReal)) = 1 - (α : EReal) := by
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
  have hstrict' :
      (f (α • x + (1 - α) • y) : EReal) <
        (α : EReal) * (f x : EReal) + (((1 - α : ℝ) : EReal) * (f y : EReal)) := by
    simpa [hsub_cast] using hstrict.ineq hx_eff hy_eff hxy hα0 hα1
  have hα_nonneg : 0 ≤ (α : EReal) := by
    exact_mod_cast hα0.le
  have hβ_nonneg : 0 ≤ (((1 - α : ℝ) : EReal)) := by
    exact_mod_cast sub_nonneg.mpr hα1.le
  have hweight_sum : (α : EReal) + (((1 - α : ℝ) : EReal)) = 1 := by
    exact_mod_cast (show α + (1 - α : ℝ) = 1 by ring)
  calc
    (f (α • x + (1 - α) • y) : EReal)
        < (α : EReal) * (f x : EReal) + (((1 - α : ℝ) : EReal) * (f y : EReal)) := hstrict'
    _ ≤ (α : EReal) * max (f x : EReal) (f y : EReal) +
          (((1 - α : ℝ) : EReal) * max (f x : EReal) (f y : EReal)) := by
      gcongr
      · exact le_max_left _ _
      · exact le_max_right _ _
    _ = max (f x : EReal) (f y : EReal) := by
      rw [← EReal.right_distrib_of_nonneg hα_nonneg hβ_nonneg, hweight_sum, one_mul]

/-- Corollary 11.9: a strictly convex `]-∞,+∞]`-valued function with nonempty effective domain has
at most one global minimizer. -/
theorem argmin_subsingleton_of_nonempty_effectiveDomain_of_strictlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} (hdom : (effectiveDomain f).Nonempty)
    (hstrict : StrictlyConvex f) :
    (Argmin f.asEReal).Subsingleton :=
  argmin_subsingleton_of_strictlyQuasiconvex <|
    hstrict.toStrictlyQuasiconvex_asEReal hdom

end

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap11/Corollary_11_16 -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {f g : H → Set.Ioi (⊥ : EReal)}

private theorem hasContinuousAffineMinorantWithSlope_zero_of_bddBelow
    (hg_bddBelow : BddBelow (Set.range g)) :
    HasContinuousAffineMinorantWithSlope g.asEReal 0 := by
  rcases hg_bddBelow with ⟨η, hη⟩
  by_cases hη_top : (η : EReal) = ⊤
  · refine ⟨0, ?_⟩
    intro x
    have hηx : (η : EReal) ≤ g.asEReal x := hη ⟨x, rfl⟩
    have hgx_top : g.asEReal x = ⊤ := by
      apply le_antisymm le_top
      simpa [hη_top] using hηx
    simp [hgx_top]
  · refine ⟨(η : EReal).toReal, ?_⟩
    intro x
    have hηx : (η : EReal) ≤ g.asEReal x := hη ⟨x, rfl⟩
    have hη_bot : (η : EReal) ≠ ⊥ := ne_of_gt η.2
    simpa [EReal.coe_toReal hη_top hη_bot] using hηx

/-- Adding a summand with a zero-slope continuous affine minorant to a coercive
`]-∞,+∞]`-valued function preserves coercivity. This is the affine-minorant companion to the
source-facing bounded-below formulation used in Corollary 11.16. -/
theorem pointwiseAdd_coercive_of_coercive_of_zeroSlopeAffineMinorant
    (hf_coe : Coercive f.asEReal)
    (hg_minor : HasContinuousAffineMinorantWithSlope g.asEReal 0) :
    Coercive (f + g).asEReal := by
  rw [Coercive, EReal.tendsto_nhds_top_iff_real] at hf_coe ⊢
  rcases hg_minor with ⟨η, hη⟩
  intro ξ
  have hf_tail : ∀ᶠ x in Bornology.cobounded H, ((ξ - η : ℝ) : EReal) < f.asEReal x :=
    hf_coe (ξ - η)
  filter_upwards [hf_tail] with x hx
  have hgx : (η : EReal) ≤ g.asEReal x := by
    simpa using hη x
  have hsum : (ξ : EReal) = ((ξ - η : ℝ) : EReal) + (η : EReal) := by
    rw [← EReal.coe_add]
    ring_nf
  calc
    (ξ : EReal) = ((ξ - η : ℝ) : EReal) + (η : EReal) := hsum
    _ < f.asEReal x + g.asEReal x := by
      exact EReal.add_lt_add_of_lt_of_le' hx hgx (by
        exact ne_of_gt (show (⊥ : EReal) < g.asEReal x from (g x).2)) <| by
          intro hgx_top hη_top
          simp at hη_top
    _ = (f + g).asEReal x := by simp [Function.asEReal]

end

section

variable {H : Type u} [AddCommGroup H] [Module ℝ H]
variable {f g : H → Set.Ioi (⊥ : EReal)}

/-- Adding a convex-on-effective-domain summand to a strictly convex `]-∞,+∞]`-valued function
preserves strict convexity. -/
theorem StrictlyConvex.add_convexOn_effectiveDomain
    (hf : StrictlyConvex f) (hg : ConvexOn g (effectiveDomain g)) :
    StrictlyConvex (f + g) := by
  intro x hx y hy hxy α hα0 hα1
  rcases (mem_effectiveDomain_pointwiseAdd_iff f g x).1 hx with ⟨hx_f, hx_g⟩
  rcases (mem_effectiveDomain_pointwiseAdd_iff f g y).1 hy with ⟨hy_f, hy_g⟩
  have hxg_top : (g x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx_g)
  have hyg_top : (g y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_g)
  have hterm1_ne_top : (α : EReal) * (g x : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot α), Or.inl ?_, Or.inl (EReal.coe_ne_top α), Or.inr hxg_top⟩
    exact_mod_cast hα0.le
  have hterm2_ne_top : (1 - α : EReal) * (g y : EReal) ≠ ⊤ := by
    rw [EReal.mul_ne_top]
    refine ⟨Or.inl (EReal.coe_ne_bot (1 - α)), Or.inl ?_,
      Or.inl (EReal.coe_ne_top (1 - α)), Or.inr hyg_top⟩
    exact_mod_cast sub_nonneg.mpr hα1.le
  have hright_ne_top :
      (α : EReal) * (g x : EReal) + (1 - α : EReal) * (g y : EReal) ≠ ⊤ := by
    exact EReal.add_ne_top hterm1_ne_top hterm2_ne_top
  calc
    ((f + g) (α • x + (1 - α) • y) : EReal)
        = (f (α • x + (1 - α) • y) : EReal) + (g (α • x + (1 - α) • y) : EReal) := by simp
    _ < ((α : EReal) * (f x : EReal) + (1 - α : EReal) * (f y : EReal)) +
          ((α : EReal) * (g x : EReal) + (1 - α : EReal) * (g y : EReal)) := by
      exact EReal.add_lt_add_of_lt_of_le
        (hf.ineq hx_f hy_f hxy hα0 hα1)
        (hg.ineq hx_g hy_g hα0 hα1)
        (ne_of_gt (show (⊥ : EReal) < (g (α • x + (1 - α) • y) : EReal) from
          (g (α • x + (1 - α) • y)).2))
        hright_ne_top
    _ = (α : EReal) * ((f x : EReal) + (g x : EReal)) +
          (1 - α : EReal) * ((f y : EReal) + (g y : EReal)) := by
      have hα_nonneg : (0 : EReal) ≤ (α : EReal) := by
        exact_mod_cast hα0.le
      have hβ_nonneg : (0 : EReal) ≤ (1 - α : EReal) := by
        exact_mod_cast sub_nonneg.mpr hα1.le
      have hα_ne_top : (α : EReal) ≠ ⊤ := EReal.coe_ne_top α
      have hβ_ne_top : (1 - α : EReal) ≠ ⊤ := EReal.coe_ne_top (1 - α)
      rw [EReal.left_distrib_of_nonneg_of_ne_top hα_nonneg hα_ne_top,
        EReal.left_distrib_of_nonneg_of_ne_top hβ_nonneg hβ_ne_top]
      simp [add_assoc, add_left_comm]
    _ = (α : EReal) * (((f + g) x : EReal)) + (1 - α : EReal) * (((f + g) y : EReal)) := by
      simp

/-- Adding a strictly convex summand to a convex-on-effective-domain `]-∞,+∞]`-valued function
preserves strict convexity. -/
theorem ConvexOn.add_strictlyConvex_effectiveDomain
    (hf : ConvexOn f (effectiveDomain f)) (hg : StrictlyConvex g) :
    StrictlyConvex (f + g) := by
  convert hg.add_convexOn_effectiveDomain hf using 1
  ext x
  simp [add_comm]

end

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable {f g : H → Set.Ioi (⊥ : EReal)}

/-- Corollary 11.16 (1): if `g ∈ Γ₀(H)` and if either (i) `f` is supercoercive or (ii) `f` is
coercive while `g` is bounded below, then `f + g` is coercive. -/
theorem pointwiseAdd_coercive_of_supercoercive_or_coercive_bddBelow
    (hg : g ∈ Γ₀(H))
    (hcase :
      Supercoercive f.asEReal ∨
        (Coercive f.asEReal ∧ BddBelow (Set.range g))) :
    Coercive (f + g).asEReal := by
  rcases hcase with hf_super | ⟨hf_coe, hg_bddBelow⟩
  · convert
      coercive_of_supercoercive
        (pointwiseAdd_supercoercive_of_mem_gammaZero g f hg hf_super) using 1
    ext x
    simp [add_comm]
  · exact pointwiseAdd_coercive_of_coercive_of_zeroSlopeAffineMinorant hf_coe
      (hasContinuousAffineMinorantWithSlope_zero_of_bddBelow hg_bddBelow)

/-- Corollary 11.16 (2): if `f, g ∈ Γ₀(H)` and if either (i) `f` is supercoercive or (ii) `f` is
coercive while `g` is bounded below, then `f + g` has a global minimizer. -/
theorem pointwiseAdd_argmin_nonempty_of_supercoercive_or_coercive_bddBelow
    (hg : g ∈ Γ₀(H)) (hf : f ∈ Γ₀(H))
    (hcase :
      Supercoercive f.asEReal ∨
        (Coercive f.asEReal ∧ BddBelow (Set.range g))) :
    (Argmin (f + g).asEReal).Nonempty := by
  by_cases hdom_fg : (effectiveDomain f ∩ effectiveDomain g).Nonempty
  · have hfg : f + g ∈ Γ₀(H) := pointwiseAdd_mem_gammaZero f g hf hg hdom_fg
    have hcoe : Coercive (f + g).asEReal :=
      pointwiseAdd_coercive_of_supercoercive_or_coercive_bddBelow hg hcase
    simpa using
      argminOn_nonempty_of_mem_gammaZero_of_coercive_or_bounded hfg
        isClosed_univ convex_univ Set.univ_nonempty (Or.inl hcoe)
  · rcases hf.2.nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [mem_argmin_iff, isMinOn_univ_iff]
    intro y
    have hy_top : (f + g).asEReal y = ⊤ := by
      apply le_antisymm le_top
      apply not_lt.mp
      intro hy
      exact hdom_fg ⟨y, ((mem_effectiveDomain_pointwiseAdd_iff f g y).1 hy).1,
        ((mem_effectiveDomain_pointwiseAdd_iff f g y).1 hy).2⟩
    simp [hy_top]

/-- Corollary 11.16 (3): if `f, g ∈ Γ₀(H)`, if their effective domains intersect, and if one
summand is strictly convex, then `f + g` has at most one global minimizer. -/
theorem pointwiseAdd_argmin_subsingleton_of_inter_nonempty_of_strictlyConvex
    (hg : g ∈ Γ₀(H)) (hf : f ∈ Γ₀(H))
    (hdom : (effectiveDomain f ∩ effectiveDomain g).Nonempty)
    (hstrict : StrictlyConvex f ∨ StrictlyConvex g) :
    (Argmin (f + g).asEReal).Subsingleton := by
  have hsum_strict : StrictlyConvex (f + g) := by
    rcases hstrict with hf_strict | hg_strict
    · exact hf_strict.add_convexOn_effectiveDomain hg.2
    · exact hf.2.add_strictlyConvex_effectiveDomain hg_strict
  exact
    argmin_subsingleton_of_nonempty_effectiveDomain_of_strictlyConvex
      (effectiveDomain_add_nonempty_of_inter_nonempty f g hdom) hsum_strict

end

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap11/Corollary_11_30 -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

private theorem exists_strict_upperLevel_of_isMinimizingSequence
    {f : H → EReal} {xₙ : ℕ → H} (hxₙ : IsMinimizingSequence f xₙ) :
    ∃ ξ : ℝ, sInf (Set.range f) < (ξ : EReal) := by
  let ξ : ℝ := (f (xₙ 0)).toReal + 1
  refine ⟨ξ, ?_⟩
  have hx0_lt_ξ : f (xₙ 0) < (ξ : EReal) := by
    by_cases hx0_bot : f (xₙ 0) = ⊥
    · simpa [ξ, hx0_bot] using EReal.bot_lt_coe ((f (xₙ 0)).toReal + 1)
    · rw [← EReal.coe_toReal (ne_of_lt (hxₙ.lt_top 0)) hx0_bot]
      exact_mod_cast show (f (xₙ 0)).toReal < (f (xₙ 0)).toReal + 1 by linarith
  exact lt_of_le_of_lt (sInf_le (Set.mem_range_self (xₙ 0))) hx0_lt_ξ

private theorem lowerLevelSet_subset_effectiveDomain_asEReal
    {f : H → Set.Ioi (⊥ : EReal)} {ξ : ℝ} :
    lowerLevelSet f.asEReal ξ ⊆ effectiveDomain f := by
  intro x hx
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt ((mem_lowerLevelSet_iff f.asEReal ξ x).1 hx) (EReal.coe_lt_top ξ)

private theorem exists_nonempty_lowerLevelSet_above_sInf_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    ∃ ξ : ℝ, sInf (Set.range f.asEReal) < (ξ : EReal) ∧
      (lowerLevelSet f.asEReal ξ).Nonempty := by
  obtain ⟨x, hxdom⟩ := (isProper_of_mem_gammaZero hf).2
  let ξ : ℝ := (f x : EReal).toReal + 1
  have hx_lt_ξ : (f x : EReal) < (ξ : EReal) := by
    rw [← EReal.coe_toReal (ne_of_lt (mem_effectiveDomain_iff.mp hxdom)) (ne_of_gt (f x).2)]
    exact_mod_cast show (f x : EReal).toReal < (f x : EReal).toReal + 1 by linarith
  refine ⟨ξ, lt_of_le_of_lt (sInf_le (Set.mem_range_self x)) hx_lt_ξ, x, ?_⟩
  exact (mem_lowerLevelSet_iff f.asEReal ξ x).2 hx_lt_ξ.le

private theorem exists_nonempty_bounded_convex_lowerLevelSet_above_sInf_of_mem_gammaZero_of_coercive
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (hf_coe : Coercive f.asEReal) :
    ∃ ξ : ℝ, sInf (Set.range f.asEReal) < (ξ : EReal) ∧
      (lowerLevelSet f.asEReal ξ).Nonempty ∧
      Bornology.IsBounded (lowerLevelSet f.asEReal ξ) ∧
      Convex ℝ (lowerLevelSet f.asEReal ξ) := by
  obtain ⟨ξ, hξ, hlevel_nonempty⟩ := exists_nonempty_lowerLevelSet_above_sInf_of_mem_gammaZero hf
  refine ⟨ξ, hξ, hlevel_nonempty, ?_, convex_lowerLevelSet_asEReal_of_mem_gammaZero hf ξ⟩
  exact (coercive_iff_bounded_lowerLevelSet f.asEReal).1 hf_coe ξ

private theorem convexCombination_le_max {a b : EReal} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    (α : EReal) * a + ((1 - α : ℝ) : EReal) * b ≤ max a b := by
  have hα_nonneg : 0 ≤ (α : EReal) := by
    exact_mod_cast hα0.le
  have hβ_nonneg : 0 ≤ (((1 - α : ℝ) : EReal)) := by
    exact_mod_cast (sub_pos.2 hα1).le
  have hsum : (α : EReal) + ((1 - α : ℝ) : EReal) = 1 := by
    rw [← EReal.coe_add]
    norm_num
  calc
    (α : EReal) * a + ((1 - α : ℝ) : EReal) * b
        ≤ (α : EReal) * max a b + ((1 - α : ℝ) : EReal) * max a b := by
          gcongr
          · exact le_max_left a b
          · exact le_max_right a b
    _ = max a b := by
          rw [← EReal.right_distrib_of_nonneg hα_nonneg hβ_nonneg, hsum, one_mul]

private theorem strictlyQuasiconvex_add_indicator_of_strictlyConvexOn
    {f : H → Set.Ioi (⊥ : EReal)} {C : Set H}
    (hC_convex : Convex ℝ C) (hstrict : StrictlyConvexOn f C) :
    StrictlyQuasiconvex (f.asEReal + (ι[C]).asEReal) := by
  let g : H → EReal := f.asEReal + (ι[C]).asEReal
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro x
      by_cases hx : x ∈ C
      · simpa [g, hx] using (ne_of_gt (f x).2)
      · have hbot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
        simp [hx, hbot]
    · rcases hstrict.nonempty with ⟨x, hx⟩
      refine ⟨x, ?_⟩
      rw [mem_dom_iff]
      simpa [g, hx] using mem_effectiveDomain_iff.mp (hstrict.subset_effectiveDomain hx)
  · intro x y hx hy hxy α hα0 hα1
    rw [mem_dom_iff_ne_top] at hx hy
    have hxC : x ∈ C := by
      by_contra hxC
      have hbot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
      exact hx (by simp [hxC, hbot])
    have hyC : y ∈ C := by
      by_contra hyC
      have hbot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
      exact hy (by simp [hyC, hbot])
    have hcomboC :
        α • x + (1 - α) • y ∈ C := by
      exact hC_convex hxC hyC hα0.le (by linarith) (by ring)
    have hstrict_lt :
        (f (α • x + (1 - α) • y) : EReal) < max (f x : EReal) (f y : EReal) := by
      calc
        (f (α • x + (1 - α) • y) : EReal)
            < (α : EReal) * (f x : EReal) + ((1 - α : ℝ) : EReal) * (f y : EReal) :=
              hstrict.ineq hxC hyC hxy hα0 hα1
        _ ≤ max (f x : EReal) (f y : EReal) :=
              convexCombination_le_max hα0 hα1
    simpa [g, hxC, hyC, hcomboC] using hstrict_lt

section CompleteSpace

variable [CompleteSpace H]

/-- Corollary 11.30 (1): clause (i). Every minimizing sequence of a coercive `]-∞,+∞]`-valued
function has a weak sequential cluster point. -/
theorem exists_weakSequentialClusterPoint_of_coercive
    {f : H → Set.Ioi (⊥ : EReal)} (hf_coe : Coercive f.asEReal) {xₙ : ℕ → H}
    (hxₙ : IsMinimizingSequence f.asEReal xₙ) :
    ∃ x : H,
      IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x) := by
  obtain ⟨ξ, hξ⟩ := exists_strict_upperLevel_of_isMinimizingSequence hxₙ
  have hlevel_bounded : Bornology.IsBounded (lowerLevelSet f.asEReal ξ) :=
    (coercive_iff_bounded_lowerLevelSet f.asEReal).1 hf_coe ξ
  exact
    IsMinimizingSequence.exists_weakSequentialClusterPoint_of_bounded_lowerLevelSet
      hxₙ hξ hlevel_bounded

end CompleteSpace

/-- Corollary 11.30 (2): clause (i). Every weak sequential cluster point of a minimizing sequence
of a member of `Γ₀(H)` is a global minimizer. -/
theorem mem_argmin_of_weakSequentialClusterPoint_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) {xₙ : ℕ → H}
    (hxₙ : IsMinimizingSequence f.asEReal xₙ) {x : H}
    (hx : IsSequentialClusterPt (fun n ↦ toWeakSpace ℝ H (xₙ n)) (toWeakSpace ℝ H x)) :
    x ∈ Argmin f.asEReal := by
  have hf_quasi : QuasiconvexOn ℝ Set.univ f.asEReal := by
    rw [quasiconvexOn_univ_iff_convex_lowerLevelSet f.asEReal]
    intro ξ
    exact convex_lowerLevelSet_asEReal_of_mem_gammaZero hf ξ
  exact
    IsSequentialClusterPt.mem_argmin_of_isMinimizingSequence_of_quasiconvexOn_univ hx
      hf_quasi hf.1 hxₙ

section CompleteSpace

variable [CompleteSpace H]

/-- Corollary 11.30 (3): clause (ii). If `f` is strictly convex, then `f` has a unique global
minimizer. -/
theorem existsUnique_mem_argmin_of_mem_gammaZero_of_coercive_of_strictlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hf_coe : Coercive f.asEReal) (hstrict : StrictlyConvex f) :
    ∃! x : H, x ∈ Argmin f.asEReal := by
  obtain ⟨ξ, hξ, hlevel_nonempty, hlevel_bounded, hlevel_convex⟩ :=
    exists_nonempty_bounded_convex_lowerLevelSet_above_sInf_of_mem_gammaZero_of_coercive
      hf hf_coe
  have hstrict_level :
      StrictlyConvexOn f (lowerLevelSet f.asEReal ξ) :=
    hstrict.strictlyConvexOn hlevel_nonempty lowerLevelSet_subset_effectiveDomain_asEReal
  exact
    existsUnique_mem_argmin_of_strictlyQuasiconvex_indicator_lowerLevelSet
      hf.1 hξ hlevel_bounded
      (strictlyQuasiconvex_add_indicator_of_strictlyConvexOn hlevel_convex hstrict_level)

/-- Corollary 11.30 (4): clause (ii). If `f` is strictly convex, then every minimizing sequence
converges weakly to a global minimizer of `f`. -/
theorem exists_mem_argmin_and_tendsto_toWeakSpace_of_mem_gammaZero_of_coercive_of_strictlyConvex
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H))
    (hf_coe : Coercive f.asEReal) (hstrict : StrictlyConvex f) {xₙ : ℕ → H}
    (hxₙ : IsMinimizingSequence f.asEReal xₙ) :
    ∃ x ∈ Argmin f.asEReal,
      Tendsto (fun n ↦ toWeakSpace ℝ H (xₙ n)) atTop (𝓝 (toWeakSpace ℝ H x)) := by
  obtain ⟨ξ, hξ, hlevel_nonempty, hlevel_bounded, hlevel_convex⟩ :=
    exists_nonempty_bounded_convex_lowerLevelSet_above_sInf_of_mem_gammaZero_of_coercive
      hf hf_coe
  have hstrict_level :
      StrictlyConvexOn f (lowerLevelSet f.asEReal ξ) :=
    hstrict.strictlyConvexOn hlevel_nonempty lowerLevelSet_subset_effectiveDomain_asEReal
  exact
    hxₙ.exists_mem_argmin_and_tendsto_toWeakSpace_of_strictlyQuasiconvex_indicator_lowerLevelSet
      hf.1 hξ hlevel_bounded
      (strictlyQuasiconvex_add_indicator_of_strictlyConvexOn hlevel_convex hstrict_level)

end CompleteSpace

end

end ERealFunction
