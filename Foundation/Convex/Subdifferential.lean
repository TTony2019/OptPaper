import Mathlib
import Foundation.Analysis.ExtendedRealFunctions
import Foundation.Analysis.Semicontinuity
import Foundation.Convex.Conjugate
import Foundation.Convex.Gamma0
import Foundation.Convex.NormalCone
import Foundation.Convex.ProximalOperator
import Foundation.Optimization.Argmin
import Foundation.SetValued.Basic
import Foundation.SetValued.Minty
import Foundation.SetValued.Monotone

/-!
# The convex subdifferential

Definition 16.1 and the fundamental properties of the subdifferential of an
`]-∞,+∞]`-valued function on a real Hilbert space, promoted from the
Bauschke–Combettes book formalization (Bauschke-lean-project, Chap16).
-/



/-! Source item: Bauschke-lean-project/BauschkeLean/Chap16/Definition_16_1.lean -/

open scoped InnerProductSpace Set

universe u

namespace ERealFunction

noncomputable section

section Subdifferential

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The canonical codomain bridge from `]-∞,+∞]`-valued functions to `EReal`-valued functions. -/
instance {X : Type*} : CoeTC (X → Set.Ioi (⊥ : EReal)) (X → EReal) := ⟨Function.asEReal⟩

/-- Definition 16.1: the subdifferential of a function with canonical `EReal`-valued codomain
coercion sends `x` to the set of vectors `u` such that the affine function
`y ↦ ⟪y - x, u⟫ + f x` minorizes `f` everywhere. In particular, the same owner surface applies
directly to both `EReal`-valued and `]-∞,+∞]`-valued functions. -/
def subdifferential {α : Type*} [CoeTC α EReal] (f : H → α) : SetValuedOperator H H :=
  fun x ↦ {u | ∀ y : H, (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal)}

scoped prefix:100 "∂ " => ERealFunction.subdifferential

/-- The function `f` is subdifferentiable at `x` when `x` belongs to the domain of the
subdifferential operator. -/
abbrev SubdifferentiableAt {α : Type*} [CoeTC α EReal] (f : H → α) (x : H) : Prop :=
  x ∈ SetValuedOperator.dom (∂ f)

/-- Subdifferentiability at `x` is membership of `x` in the domain of the subdifferential
operator. -/
@[simp] theorem subdifferentiableAt_iff_mem_dom
    {α : Type*} [CoeTC α EReal] (f : H → α) (x : H) :
    SubdifferentiableAt f x ↔ x ∈ SetValuedOperator.dom (∂ f) :=
  Iff.rfl

/-- Membership in the subdifferential is exactly the global affine-minorant inequality. -/
@[simp] theorem mem_subdifferential_iff
    {α : Type*} [CoeTC α EReal] (f : H → α) (x u : H) :
    u ∈ subdifferential f x ↔
      ∀ y : H, (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) :=
  Iff.rfl

end Subdifferential

end

end ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap16/Theorem_16_3.lean -/

open scoped InnerProductSpace

namespace ERealFunction

section Subdifferentials

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: this is the direct bridge between the owner declarations `Argmin`,
-- `SetValuedOperator.zeros`, and `subdifferential`. At slope `0`, the affine-minorant inequality
-- in `mem_subdifferential_iff` is exactly the global minimality condition.
/-- Theorem 16.3: Fermat's rule. The global minimizers of an `]-∞,+∞]`-valued function are exactly
the zeros of its subdifferential. -/
theorem argmin_eq_zeros_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) :
    Optimization.argminSet f.asEReal = (∂ f).zeros := by
  ext x
  rw [Optimization.mem_argminSet_iff, SetValuedOperator.mem_zeros_iff, mem_subdifferential_iff]
  constructor <;> intro hx y <;> simpa using hx y

end Subdifferentials

end ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap16/Proposition_16_4.lean -/

open scoped InnerProductSpace


namespace ERealFunction

section SubdifferentialBasicProperties

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 16 4: outside the effective domain of an `]-∞,+∞]`-valued function,
the value is necessarily `⊤`. -/
private theorem value_eq_top_of_not_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∉ effectiveDomain f) :
    (f x : EReal) = ⊤ := by
  -- A finite value would put `x` back into the effective domain.
  by_contra htop
  exact hx (mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top htop))

-- Proof sketch: choose a point `y` in the effective domain. If `u ∈ subdifferential f x`, then
-- the defining inequality with that `y` forces `(f x : EReal) < ⊤`.
/-- Proposition 16 4 (1): if `f` has a nonempty effective domain, then every point at which the
subdifferential is nonempty lies in the effective domain. For `]-∞,+∞]`-valued functions, this is
the remaining properness content after excluding `-∞` by the codomain. -/
theorem subdifferential_domain_subset_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) (hdom : (effectiveDomain f).Nonempty) :
    SetValuedOperator.dom (∂ f) ⊆ effectiveDomain f := by
  intro x hx
  rcases hdom with ⟨y, hy⟩
  rw [SetValuedOperator.mem_dom_iff] at hx
  rcases hx with ⟨u, hu⟩
  by_contra hx_not_mem
  have hx_top : (f x : EReal) = ⊤ := value_eq_top_of_not_mem_effectiveDomain hx_not_mem
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  -- Evaluating the subgradient inequality at a finite-domain point forces `f x` to be finite.
  have hxy : (⊤ : EReal) ≤ (f y : EReal) := by
    have hxy₀ : (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) := hu y
    rw [hx_top] at hxy₀
    simpa using hxy₀
  exact hy_top (le_antisymm le_top hxy)

/-- Pointwise form of Proposition 16 4 (1): subdifferentiability forces effective-domain
membership. -/
theorem SubdifferentiableAt.mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hdom : (effectiveDomain f).Nonempty) {x : H}
    (hx : SubdifferentiableAt f x) :
    x ∈ effectiveDomain f := by
  -- Clause (1) applies directly to the subdifferential domain point `x`.
  exact subdifferential_domain_subset_effectiveDomain f hdom hx

/-- Helper for Proposition 16 4: at finite points, the affine `EReal` subgradient inequality is
equivalent to the corresponding real half-space inequality. -/
private theorem ereal_affine_ineq_iff_inner_le_toReal_sub
    {f : H → Set.Ioi (⊥ : EReal)} {x y u : H}
    (hx : x ∈ effectiveDomain f) (hy : y ∈ effectiveDomain f) :
    (((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal)) ↔
      (⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal)) := by
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hsub :
      (((f y : EReal).toReal - (f x : EReal).toReal : ℝ) : EReal) =
        (f y : EReal) - (f x : EReal) := by
    -- Replace the two finite `EReal` values by their real representatives once and for all.
    calc
      (((f y : EReal).toReal - (f x : EReal).toReal : ℝ) : EReal) =
          (((f y : EReal).toReal : EReal) - (((f x : EReal).toReal : EReal))) := by
            rw [EReal.coe_sub]
      _ = (f y : EReal) - (f x : EReal) := by
        rw [EReal.coe_toReal hy_top hy_bot, EReal.coe_toReal hx_top hx_bot]
  constructor
  · intro hineq
    -- Move the finite value `f x` to the right-hand side inside `EReal`.
    have hsubineq : (⟪y - x, u⟫_ℝ : EReal) ≤ (f y : EReal) - (f x : EReal) := by
      exact (EReal.le_sub_iff_add_le (.inl hx_bot) (.inl hx_top)).2 hineq
    have hcast :
        (⟪y - x, u⟫_ℝ : EReal) ≤
          (((f y : EReal).toReal - (f x : EReal).toReal : ℝ) : EReal) := by
      simpa [hsub] using hsubineq
    exact_mod_cast hcast
  · intro hineq
    -- Cast the real half-space inequality back to `EReal` and undo the subtraction step.
    have hcast :
        (⟪y - x, u⟫_ℝ : EReal) ≤
          (((f y : EReal).toReal - (f x : EReal).toReal : ℝ) : EReal) := by
      exact_mod_cast hineq
    have hsubineq : (⟪y - x, u⟫_ℝ : EReal) ≤ (f y : EReal) - (f x : EReal) := by
      simpa [hsub] using hcast
    exact (EReal.le_sub_iff_add_le (.inl hx_bot) (.inl hx_top)).1 hsubineq

/-- A subgradient at `x` gives the usual real-valued subgradient inequality at every finite
effective-domain point `y`. -/
theorem subgradient_ineq_toReal_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ gammaZero H)
    {x u y : H} (hu : u ∈ subdifferential f x) (hy : y ∈ effectiveDomain f) :
    (f y : EReal).toReal ≥ (f x : EReal).toReal + inner ℝ u (y - x) := by
  have hdom : (effectiveDomain f).Nonempty := hf.2.nonempty
  have hx : x ∈ effectiveDomain f :=
    SubdifferentiableAt.mem_effectiveDomain hdom ⟨u, hu⟩
  have hinner : inner ℝ (y - x) u ≤
      (f y : EReal).toReal - (f x : EReal).toReal :=
    (ereal_affine_ineq_iff_inner_le_toReal_sub hx hy).1
      ((mem_subdifferential_iff _ _ _).1 hu y)
  rw [real_inner_comm]
  linarith

/-- Helper for Proposition 16 4: at a finite point `x`, subgradient membership is equivalent to
the family of affine half-space inequalities indexed by the effective domain. -/
private theorem mem_subdifferential_iff_forall_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {x u : H} (hx : x ∈ effectiveDomain f) :
    u ∈ (∂ f) x ↔
      ∀ y ∈ effectiveDomain f,
        ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by
  -- Route correction: isolate the finite-value `EReal`/`toReal` transport in one adapter lemma,
  -- then use it uniformly in both directions of the subgradient rewrite.
  constructor
  · intro hu y hy
    -- On the effective domain, the global subgradient inequality is exactly the affine half-space
    -- inequality after converting finite `EReal` values to real numbers.
    exact
      (ereal_affine_ineq_iff_inner_le_toReal_sub hx hy).1
        ((mem_subdifferential_iff _ _ _).1 hu y)
  · intro hu
    rw [mem_subdifferential_iff]
    intro y
    by_cases hy : y ∈ effectiveDomain f
    · -- The finite branch is the adapter lemma in the reverse direction.
      exact (ereal_affine_ineq_iff_inner_le_toReal_sub hx hy).2 (hu y hy)
    · -- Outside the effective domain, the target value is `⊤`, so the inequality is automatic.
      have hy_top : (f y : EReal) = ⊤ := value_eq_top_of_not_mem_effectiveDomain hy
      change ((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal))
      rw [hy_top]
      exact le_top

-- Proof sketch: rewrite `u ∈ subdifferential f x` using the defining affine-minorant inequality,
-- then move the finite value `(f x : EReal)` to the right-hand side for each `y ∈ effectiveDomain
-- f`.
/-- Proposition 16 4 (2): at a point of the effective domain, the subdifferential is the
intersection of the affine half-spaces cut out by the subgradient inequalities over the effective
domain. -/
theorem subdifferential_eq_iInter_affine_halfspaces
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) (hx : x ∈ effectiveDomain f) :
    (∂ f) x =
      ⋂ y ∈ effectiveDomain f,
        {u : H | ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal} := by
  ext u
  -- Clause (2) is just the set-level version of the pointwise membership rewrite.
  rw [Set.mem_iInter₂]
  exact mem_subdifferential_iff_forall_mem_effectiveDomain hx

/-- Helper for Proposition 16 4: outside the effective domain, the subdifferential is either empty
or all of `H`, depending on whether the effective domain itself is nonempty. -/
theorem subdifferential_eq_empty_or_univ_of_not_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∉ effectiveDomain f) :
    (∂ f) x = ∅ ∨ (∂ f) x = Set.univ := by
  by_cases hdom : (effectiveDomain f).Nonempty
  · left
    ext u
    constructor
    · intro hu
      -- If the effective domain is nonempty, clause (1) forbids any subgradient outside it.
      have hx_dom : x ∈ SetValuedOperator.dom (∂ f) := by
        rw [SetValuedOperator.mem_dom_iff]
        exact ⟨u, hu⟩
      exact False.elim (hx (subdifferential_domain_subset_effectiveDomain f hdom hx_dom))
    · intro hu
      exact hu.elim
  · right
    ext u
    constructor
    · intro _
      simp
    · intro _
      rw [mem_subdifferential_iff]
      intro y
      have hy_not_mem : y ∉ effectiveDomain f := by
        intro hy
        exact hdom ⟨y, hy⟩
      have hy_top : (f y : EReal) = ⊤ := value_eq_top_of_not_mem_effectiveDomain hy_not_mem
      -- When the effective domain is empty, every value is `⊤`, so every affine inequality holds.
      change ((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal))
      rw [hy_top]
      exact le_top

/-- Proposition 16 4: outside the effective domain, the subdifferential is empty whenever the
effective domain itself is nonempty. -/
theorem subdifferential_eq_empty_of_not_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} (hdom : (effectiveDomain f).Nonempty) {x : H}
    (hx : x ∉ effectiveDomain f) :
    (∂ f) x = ∅ := by
  rcases subdifferential_eq_empty_or_univ_of_not_mem_effectiveDomain hx with hempty | huniv
  · exact hempty
  · exfalso
    have hx_dom : x ∈ SetValuedOperator.dom (∂ f) := by
      rw [SetValuedOperator.mem_dom_iff]
      exact ⟨x, by simp [huniv]⟩
    exact hx (subdifferential_domain_subset_effectiveDomain f hdom hx_dom)

/-- Helper for Proposition 16 4: each affine subgradient half-space is closed. -/
private theorem isClosed_subgradient_halfspace
    {x y : H} {c : ℝ} :
    IsClosed ({u : H | ⟪y - x, u⟫_ℝ ≤ c} : Set H) := by
  -- The half-space is the preimage of `Iic c` under the continuous functional
  -- `u ↦ ⟪y - x, u⟫`.
  simpa using isClosed_le (continuous_const.inner continuous_id) continuous_const

/-- Helper for Proposition 16 4: each affine subgradient half-space is convex. -/
private theorem convex_subgradient_halfspace
    {x y : H} {c : ℝ} :
    Convex ℝ ({u : H | ⟪y - x, u⟫_ℝ ≤ c} : Set H) := by
  rw [convex_iff_forall_pos]
  intro u hu v hv a b ha hb hab
  have hcombo :
      ⟪y - x, a • u + b • v⟫_ℝ = a * ⟪y - x, u⟫_ℝ + b * ⟪y - x, v⟫_ℝ := by
    rw [inner_add_right, inner_smul_right, inner_smul_right]
  have hle : a * ⟪y - x, u⟫_ℝ + b * ⟪y - x, v⟫_ℝ ≤ c := by
    have ha0 : 0 ≤ a := le_of_lt ha
    have hb0 : 0 ≤ b := le_of_lt hb
    have hscaled :
        a * ⟪y - x, u⟫_ℝ + b * ⟪y - x, v⟫_ℝ ≤ a * c + b * c := by
      exact add_le_add (mul_le_mul_of_nonneg_left hu ha0) (mul_le_mul_of_nonneg_left hv hb0)
    have hsum : a * c + b * c = c := by
      calc
        a * c + b * c = (a + b) * c := by ring
        _ = c := by rw [hab, one_mul]
    exact hscaled.trans_eq hsum
  -- Expanding the inner product of the convex combination puts the goal into the linear form
  -- handled by the scalar inequality above.
  simpa [hcombo, smul_eq_mul] using hle

-- Proof sketch: if `x ∈ effectiveDomain f`, use the half-space description from clause (2). Each
-- defining set is closed, and arbitrary intersections of closed sets are closed. If
-- `x ∉ effectiveDomain f`, then `(∂ f) x` is either `∅` or `Set.univ`, hence closed.
/-- Proposition 16 4 (3): the subdifferential is closed at every point. -/
theorem isClosed_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    IsClosed ((∂ f) x) := by
  by_cases hx : x ∈ effectiveDomain f
  · -- On the effective domain, clause (2) writes the fiber as an intersection of closed
    -- half-spaces.
    rw [subdifferential_eq_iInter_affine_halfspaces f x hx]
    exact isClosed_iInter fun y ↦ isClosed_iInter fun _ ↦ isClosed_subgradient_halfspace
  · -- Outside the effective domain, the fiber is either `∅` or `univ`.
    rcases subdifferential_eq_empty_or_univ_of_not_mem_effectiveDomain hx with hempty | huniv
    · rw [hempty]
      exact isClosed_empty
    · rw [huniv]
      exact isClosed_univ

-- Proof sketch: if `x ∈ effectiveDomain f`, use the half-space description from clause (2). Each
-- defining set is convex, and arbitrary intersections of convex sets are convex. If
-- `x ∉ effectiveDomain f`, then `(∂ f) x` is either `∅` or `Set.univ`, hence convex.
/-- Proposition 16 4 (4): the subdifferential is convex at every point. -/
theorem convex_subdifferential
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    Convex ℝ ((∂ f) x) := by
  by_cases hx : x ∈ effectiveDomain f
  · -- On the effective domain, clause (2) writes the fiber as an intersection of convex
    -- half-spaces.
    rw [subdifferential_eq_iInter_affine_halfspaces f x hx]
    exact convex_iInter₂ fun y _ ↦ convex_subgradient_halfspace
  · -- Outside the effective domain, the fiber is either `∅` or `univ`.
    rcases subdifferential_eq_empty_or_univ_of_not_mem_effectiveDomain hx with hempty | huniv
    · rw [hempty]
      exact convex_empty
    · rw [huniv]
      exact convex_univ

/-! Source item: Attouch_Adly_First_order_inertial_algorithms_involving_dry_friction_damping_2021
items/ext_thm_3 -/

/-- The subdifferential of a proper extended-real-valued function is a monotone set-valued
operator: for `u ∈ ∂f x` and `v ∈ ∂f y` we have `⟪u - v, x - y⟫ ≥ 0`. -/
theorem isMonotone_subdifferential (F : H → EReal) (hproper : IsProper F) :
    SetValuedOperator.IsMonotone (∂ F) := by
  intro x y u hu v hv
  rw [subdifferential, Set.mem_setOf_eq] at hu hv
  have hu_top : F x ≠ ⊤ := by
    rcases hproper with ⟨_, ⟨z, hz⟩⟩
    intro htop
    have hz0 := hu z
    change (inner ℝ (z - x) u : EReal) + (F x : EReal) ≤ F z at hz0
    rw [htop] at hz0
    have hle : (⊤ : EReal) ≤ F z := by simpa using hz0
    exact ((ERealFunction.mem_dom_iff F z).1 hz).ne (top_unique hle)
  have hu_bot : F x ≠ ⊥ := hproper.1 x
  have hv_top : F y ≠ ⊤ := by
    rcases hproper with ⟨_, ⟨z, hz⟩⟩
    intro htop
    have hz0 := hv z
    change (inner ℝ (z - y) v : EReal) + (F y : EReal) ≤ F z at hz0
    rw [htop] at hz0
    have hle : (⊤ : EReal) ≤ F z := by simpa using hz0
    exact ((ERealFunction.mem_dom_iff F z).1 hz).ne (top_unique hle)
  have hv_bot : F y ≠ ⊥ := hproper.1 y
  have hxy : (inner ℝ (y - x) u : EReal) + F x ≤ F y := by
    have hy0 := hu y
    change (inner ℝ (y - x) u : EReal) + (F x : EReal) ≤ F y at hy0
    exact hy0
  have hyx : (inner ℝ (x - y) v : EReal) + F y ≤ F x := by
    have hx0 := hv x
    change (inner ℝ (x - y) v : EReal) + (F y : EReal) ≤ F x at hx0
    exact hx0
  have hxy_real := EReal.toReal_le_toReal hxy
    (EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, hu_bot⟩) hv_top
  have hyx_real := EReal.toReal_le_toReal hyx
    (EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, hv_bot⟩) hu_top
  rw [EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _) hu_top hu_bot] at hxy_real
  rw [EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _) hv_top hv_bot] at hyx_real
  simp only [EReal.toReal_coe] at hxy_real hyx_real
  rw [inner_sub_left] at hxy_real hyx_real
  rw [← real_inner_comm y u, ← real_inner_comm x u] at hxy_real
  rw [← real_inner_comm x v, ← real_inner_comm y v] at hyx_real
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  linarith

-- Proof sketch: pick `u ∈ subdifferential f x`; the subgradient inequality gives
-- `f x ≤ f y - ⟪y - x, u⟫`, and continuity of the affine term transfers this to the liminf
-- characterization of lower semicontinuity at `x`.
/-- Proposition 16 4 (5): if the subdifferential of `f` at `x` is nonempty, then `f` is
lower semicontinuous at `x`. -/
theorem SubdifferentiableAt.lowerSemicontinuousAt
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hxsub : SubdifferentiableAt f x) :
    LowerSemicontinuousAt f.asEReal x := by
  by_cases hdom : (effectiveDomain f).Nonempty
  · rcases hxsub with ⟨u, hu⟩
    have hx : x ∈ effectiveDomain f := SubdifferentiableAt.mem_effectiveDomain hdom ⟨u, hu⟩
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    let g : H → EReal := fun y ↦
      ((⟪y - x, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal)
    have hg_le : g ≤ f.asEReal := by
      intro y
      -- The affine minorant is exactly the defining subgradient lower bound after freezing the
      -- finite value `f x`.
      have hg_eq : g y = ((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal)) := by
        calc
          g y = (((⟪y - x, u⟫_ℝ + (f x : EReal).toReal : ℝ) : EReal)) := rfl
          _ = ((⟪y - x, u⟫_ℝ : EReal) + (((f x : EReal).toReal : ℝ) : EReal)) := by
            rw [EReal.coe_add]
          _ = ((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal)) := by
            rw [EReal.coe_toReal hx_top hx_bot]
      rw [hg_eq]
      simpa [Function.asEReal_apply] using hu y
    have hgx : g x = f.asEReal x := by
      -- At the touching point `x`, the affine minorant agrees with `f`.
      calc
        g x = (((0 : ℝ) + (f x : EReal).toReal : ℝ) : EReal) := by
          simp [g]
        _ = (((f x : EReal).toReal : ℝ) : EReal) := by simp
        _ = f.asEReal x := by
          simpa [Function.asEReal_apply] using EReal.coe_toReal hx_top hx_bot
    have hg_cont : ContinuousAt g x := by
      have hreal_cont :
          ContinuousAt (fun y : H ↦ ⟪y - x, u⟫_ℝ + (f x : EReal).toReal) x := by
        exact (((continuous_id.sub continuous_const).inner continuous_const).continuousAt).add
          continuousAt_const
      exact continuous_coe_real_ereal.continuousAt.comp hreal_cont
    rw [lowerSemicontinuousAt_iff_le_liminf]
    calc
      f.asEReal x = g x := hgx.symm
      _ ≤ Filter.liminf g (nhds x) := hg_cont.lowerSemicontinuousAt.le_liminf
      _ ≤ Filter.liminf f.asEReal (nhds x) := by
        exact Filter.liminf_le_liminf
          (show ∀ᶠ y in nhds x, g y ≤ f.asEReal y from Filter.Eventually.of_forall hg_le)
  · have hconst : f.asEReal = fun _ : H ↦ (⊤ : EReal) := by
      funext y
      have hy : y ∉ effectiveDomain f := by
        intro hy
        exact hdom ⟨y, hy⟩
      exact value_eq_top_of_not_mem_effectiveDomain hy
    -- If the effective domain is empty, `f` is the constant `⊤` function, hence trivially lsc.
    simpa [hconst] using
      (continuousAt_const : ContinuousAt (fun _ : H ↦ (⊤ : EReal)) x).lowerSemicontinuousAt

-- Proof sketch: first obtain ordinary lower semicontinuity at `x` from clause (5). Then view the
-- same subgradient inequality on `WeakSpace ℝ H`; the affine functional remains weakly continuous,
end SubdifferentialBasicProperties

end ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap16/Proposition_16_6.lean -/

open scoped InnerProductSpace Pointwise


namespace ContinuousLinearMap

section SetValuedOperatorCalculus

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The set-valued operator `L^* ∘ B ∘ L`, sending `x` to the adjoint image of `B (L x)`. -/
def adjointImage
    (L : H →L[ℝ] K) (B : SetValuedOperator K K) : SetValuedOperator H H :=
  fun x ↦ L.adjoint '' (B (L x))

/-- Evaluating `ContinuousLinearMap.adjointImage L B` gives the adjoint image of `B (L x)`. -/
@[simp] theorem adjointImage_apply
    (L : H →L[ℝ] K) (B : SetValuedOperator K K) (x : H) :
    L.adjointImage B x = L.adjoint '' (B (L x)) :=
  rfl

end SetValuedOperatorCalculus

end ContinuousLinearMap

namespace ERealFunction

noncomputable section

section SubdifferentialBasicProperties

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 16 6: the reciprocal of a positive real is still positive. -/
private theorem posReal_inv_pos (γ : PosReal) : 0 < (γ : ℝ)⁻¹ := by
  -- The reciprocal of a strictly positive real stays strictly positive.
  exact inv_pos.mpr γ.2

/-- Helper for Proposition 16 6: the auxiliary reciprocal positive real used to undo positive
scaling. -/
private def posRealInv (γ : PosReal) : PosReal :=
  ⟨(γ : ℝ)⁻¹, posReal_inv_pos γ⟩

/-- Helper for Proposition 16 6: the auxiliary reciprocal cancels `γ` on the left. -/
@[simp] private theorem posRealInv_mul (γ : PosReal) :
    ((posRealInv γ : ℝ) * (γ : ℝ)) = 1 := by
  -- Rewrite the auxiliary reciprocal to the ordinary real inverse.
  simpa [posRealInv] using inv_mul_cancel₀ γ.2.ne'

/-- Helper for Proposition 16 6: the auxiliary reciprocal cancels `γ` on the right. -/
@[simp] private theorem mul_posRealInv (γ : PosReal) :
    ((γ : ℝ) * (posRealInv γ : ℝ)) = 1 := by
  -- This is the commuted real inverse identity.
  simpa [posRealInv] using mul_inv_cancel₀ γ.2.ne'

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 16 6: scaling by `γ` and then by its reciprocal recovers the original
function. -/
@[simp] private theorem posRealInv_smul_posReal_smul
    (γ : PosReal) (f : H → Set.Ioi (⊥ : EReal)) :
    (posRealInv γ • (γ • f) : H → Set.Ioi (⊥ : EReal)) = f := by
  funext x
  apply Subtype.ext
  -- Rewrite both positive-real actions to ordinary `EReal` multiplication and cancel the scalar.
  calc
    (((posRealInv γ) • (γ • f)) x : EReal)
        = (posRealInv γ : EReal) * ((γ : EReal) * (f x : EReal)) := by
            rw [posReal_smul_apply, posReal_smul_apply]
    _ = (((posRealInv γ : ℝ) * (γ : ℝ) : ℝ) : EReal) * (f x : EReal) := by
          rw [← mul_assoc, ← EReal.coe_mul]
    _ = (f x : EReal) := by
          simp [posRealInv_mul]

/-- Helper for Proposition 16 6: positive scaling sends a subgradient of `f` at `x` to a
subgradient of `γ • f` at `x`. -/
private theorem smul_mem_subdifferential_posReal_smul
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) {x u : H}
    (hu : u ∈ (∂ f) x) :
    (γ : ℝ) • u ∈ (∂ ((γ • f : H → Set.Ioi (⊥ : EReal)))) x := by
  rw [mem_subdifferential_iff] at hu ⊢
  intro y
  have hγ_nonneg : (0 : EReal) ≤ (γ : EReal) := EReal.coe_nonneg.mpr γ.2.le
  have hγ_ne_top : (γ : EReal) ≠ ⊤ := EReal.coe_ne_top (γ : ℝ)
  have hscaled :
      (γ : EReal) * ((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal)) ≤
        (γ : EReal) * (f y : EReal) := by
    -- Multiply the defining affine-minorant inequality by the positive scalar.
    exact mul_le_mul_of_nonneg_left (hu y) hγ_nonneg
  calc
    (⟪y - x, (γ : ℝ) • u⟫_ℝ : EReal) + ((γ • f) x : EReal)
        = (γ : EReal) * ((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal)) := by
            -- Normalize the scaled inner product and the scaled function value.
            rw [inner_smul_right, posReal_smul_apply, EReal.coe_mul]
            rw [← EReal.left_distrib_of_nonneg_of_ne_top hγ_nonneg hγ_ne_top]
    _ ≤ (γ : EReal) * (f y : EReal) := hscaled
    _ = ((γ • f) y : EReal) := by
          rw [posReal_smul_apply]

-- Proof sketch: unfold membership in both subdifferentials and rewrite the affine-minorant
-- inequality for the canonical positive-real scalar action on `]-∞,+∞]`-valued functions;
-- dividing by the positive scalar identifies witnesses on the two sides.
/-- Proposition 16 6 (1): the subdifferential of a positive scalar multiple is the corresponding
positive scalar multiple of the subdifferential. -/
theorem subdifferential_posReal_smul_eq_smul
    (f : H → Set.Ioi (⊥ : EReal)) (γ : PosReal) :
    ∂ ((γ • f : H → Set.Ioi (⊥ : EReal))) = (γ : ℝ) • (∂ f : SetValuedOperator H H) := by
  ext x u
  constructor
  · intro hu
    have hscaledBack :
        ((posRealInv γ : ℝ) • u) ∈ (∂ f) x := by
      -- Apply the forward-scaling lemma to the reciprocal scalar and cancel the function scaling.
      have hscaled :=
        smul_mem_subdifferential_posReal_smul
          (f := (γ • f : H → Set.Ioi (⊥ : EReal))) (γ := posRealInv γ) (u := u) (x := x) hu
      rw [posRealInv_smul_posReal_smul] at hscaled
      exact hscaled
    -- Rewrite scalar-set membership through inverse scaling instead of repackaging a witness.
    change u ∈ (γ : ℝ) • ((∂ f) x)
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne']
    simpa [posRealInv] using hscaledBack
  · intro hu
    change u ∈ (γ : ℝ) • ((∂ f) x) at hu
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hu
    -- The forward scaling helper closes the remaining direction after undoing the scalar.
    simpa [smul_smul, posRealInv, mul_inv_cancel₀ γ.2.ne'] using
      (smul_mem_subdifferential_posReal_smul
        (f := f) (γ := γ) (u := ((γ : ℝ)⁻¹ • u)) (x := x) hu)

end SubdifferentialBasicProperties

namespace ContinuousLinearMap

section SubdifferentialCalculus

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- The set-valued operator `L^* ∘ (∂ g) ∘ L`, sending `x` to the adjoint image of the
subdifferential of `g` at `L x`. This is the specialization of
`ContinuousLinearMap.adjointImage` to the subdifferential of `g`. -/
abbrev adjointImageSubdifferential
    (L : H →L[ℝ] K) (g : K → Set.Ioi (⊥ : EReal)) : SetValuedOperator H H :=
  L.adjointImage (∂ g)

/-- Evaluating `ContinuousLinearMap.adjointImageSubdifferential L g` gives the adjoint image of
the subdifferential of `g` at `L x`. -/
@[simp] theorem adjointImageSubdifferential_apply
    (L : H →L[ℝ] K) (g : K → Set.Ioi (⊥ : EReal)) (x : H) :
    ContinuousLinearMap.adjointImageSubdifferential L g x = L.adjoint '' ((∂ g) (L x)) :=
  _root_.ContinuousLinearMap.adjointImage_apply L (∂ g) x

/-- Helper for Proposition 16 6: the inner product against a subtracted image under `L`
rewrites through the adjoint of `L`. -/
theorem adjoint_inner_sub_eq
    (L : H →L[ℝ] K) (x y : H) (v : K) :
    ⟪L y - L x, v⟫_ℝ = ⟪y - x, L.adjoint v⟫_ℝ := by
  -- Rewrite the image difference as `L (y - x)` and apply the adjoint identity once.
  simpa [ContinuousLinearMap.map_sub] using
    (ContinuousLinearMap.adjoint_inner_right L (y - x) v).symm

end SubdifferentialCalculus

end ContinuousLinearMap

section SubdifferentialBasicProperties

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]

/-- Helper for Proposition 16 6: adding a subgradient of `f` at `x` to the adjoint of a
subgradient of `g` at `L x` yields a subgradient of `f + g ∘ L` at `x`. -/
private theorem add_adjoint_subgradient_mem_subdifferential_add_comp
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal))
    (L : H →L[ℝ] K) (x u : H) (v : K)
    (hu : u ∈ (∂ f) x) (hv : v ∈ (∂ g) (L x)) :
    u + L.adjoint v ∈ (∂ (f + g ∘ L)) x := by
  rw [mem_subdifferential_iff] at hu hv ⊢
  intro y
  have hfy : (⟪y - x, u⟫_ℝ : EReal) + (f x : EReal) ≤ (f y : EReal) := hu y
  have hgy :
      (⟪y - x, L.adjoint v⟫_ℝ : EReal) + (g (L x) : EReal) ≤ (g (L y) : EReal) := by
    -- Evaluate the subgradient inequality for `g` at `L y` and transport it back with the adjoint.
    simpa [Function.comp_apply,
      ContinuousLinearMap.adjoint_inner_sub_eq (L := L) (x := x) (y := y) (v := v)] using hv (L y)
  have hsum := add_le_add hfy hgy
  -- Normalize the left side to the sum of the two affine-minorant inequalities.
  calc
    (⟪y - x, u + L.adjoint v⟫_ℝ : EReal) + ((f + g ∘ L) x : EReal)
        = (((⟪y - x, u⟫_ℝ : EReal) + (⟪y - x, L.adjoint v⟫_ℝ : EReal)) +
            ((f x : EReal) + (g (L x) : EReal))) := by
              rw [inner_add_right, EReal.coe_add, add_apply, Function.comp_apply]
    _ = ((⟪y - x, u⟫_ℝ : EReal) + (f x : EReal)) +
          ((⟪y - x, L.adjoint v⟫_ℝ : EReal) + (g (L x) : EReal)) := by
            simp [add_assoc, add_left_comm, add_comm]
    _ ≤ (f y : EReal) + (g (L y) : EReal) := hsum
    _ = ((f + g ∘ L) y : EReal) := by
          simp [add_apply, Function.comp_apply]

-- Proof sketch: if `u ∈ (∂ f) x` and `v ∈ (∂ g) (L x)`, combine the two subgradient inequalities;
-- rewrite the second one with the adjoint identity
-- `⟪L y - L x, v⟫ = ⟪y - x, L.adjoint v⟫` to obtain the defining inequality for
-- `u + L.adjoint v ∈ ∂ (f + g ∘ L) x`.
/-- Part (2) of Proposition 16 6: if the effective domain of `g` meets the image under `L` of the
effective domain of `f`, then every sum of a subgradient of `f` at `x` and the adjoint image of a
subgradient of `g` at `L x` is a subgradient of `f + g ∘ L` at `x`. -/
theorem subdifferential_add_adjoint_image_subset_subdifferential_add_comp
    (f : H → Set.Ioi (⊥ : EReal)) (g : K → Set.Ioi (⊥ : EReal)) (L : H →L[ℝ] K) (x : H) :
    (∂ f) x + ContinuousLinearMap.adjointImageSubdifferential L g x ⊆
      (∂ (f + g ∘ L)) x := by
  intro w hw
  rcases Set.mem_add.mp hw with ⟨u, hu, w', hw', rfl⟩
  rw [ContinuousLinearMap.adjointImageSubdifferential_apply, Set.mem_image] at hw'
  rcases hw' with ⟨v, hv, rfl⟩
  -- The pointwise closing helper is exactly the desired inclusion after unpacking the witnesses.
  exact add_adjoint_subgradient_mem_subdifferential_add_comp f g L x u v hu hv

end SubdifferentialBasicProperties

end

end ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap16/Proposition_16_10.lean -/

open scoped InnerProductSpace


namespace ERealFunction

noncomputable section

section SubdifferentialConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (f : H → Set.Ioi (⊥ : EReal))

/-- Helper for Proposition 16.10: finiteness of the raw conjugate value gives an effective-domain
point for the packaged conjugate. -/
theorem mem_effectiveDomain_properConjugateIoi_of_ne_top
    (hdom : (effectiveDomain f).Nonempty) {u : H} (hu_top : f.asEReal∗ u ≠ ⊤) :
    u ∈ effectiveDomain (properConjugateIoi f hdom) := by
  -- The packaged conjugate has the same `EReal` value, so `≠ ⊤` is exactly effective-domain
  -- membership.
  rw [mem_effectiveDomain_iff]
  have hgu_top : (properConjugateIoi f hdom u : EReal) ≠ ⊤ := by
    simpa [properConjugateIoi_apply] using hu_top
  exact lt_of_le_of_ne le_top hgu_top

/-- Helper for Proposition 16.10: conjugating the packaged conjugate recovers the Fenchel
biconjugate of the original function. -/
theorem properConjugateIoi_conjugate_eq_biconjugate
    (hdom : (effectiveDomain f).Nonempty) (x : H) :
    (properConjugateIoi f hdom).asEReal∗ x = f.asEReal∗∗ x := by
  -- Coercing `properConjugateIoi f hdom` back to `EReal` is definitionally the raw conjugate.
  simp [Function.asEReal]

/-- Proposition 16.10 (1): `u` is a
subgradient of `f` at `x` exactly when equality holds in the Fenchel--Young inequality
`f(x) + f^*(u) = ⟪x, u⟫`. -/
theorem mem_subdifferential_iff_fenchel_young_eq
    (hdom : (effectiveDomain f).Nonempty) (x u : H) :
    u ∈ (∂ f) x ↔
      (f x : EReal) + f.asEReal∗ u =
        ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
  -- Upgrade the `]-∞,+∞]`-valued function to a proper `EReal`-valued function so that
  -- Proposition 13.15 applies.
  have hproper : IsProper f.asEReal := by
    refine ⟨fun y ↦ ne_of_gt (f y).2, ?_⟩
    simpa [effectiveDomain, dom] using hdom
  constructor
  · intro hu
    have hx_dom : x ∈ SetValuedOperator.dom (∂ f) := by
      rw [SetValuedOperator.mem_dom_iff]
      exact ⟨u, hu⟩
    -- Proposition 16.4 puts the base point inside the effective domain.
    have hx : x ∈ effectiveDomain f :=
      subdifferential_domain_subset_effectiveDomain f hdom hx_dom
    have hfx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
    have hu_halfspace :
        ∀ y ∈ effectiveDomain f,
          ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by
      rw [subdifferential_eq_iInter_affine_halfspaces f x hx, Set.mem_iInter₂] at hu
      exact hu
    -- Every affine defect is bounded by the defect at `x`.
    have hdefect_le :
        ∀ y : H,
          ((⟪y, u⟫_ℝ : ℝ) : EReal) - (f y : EReal) ≤
            ((⟪x, u⟫_ℝ : ℝ) : EReal) - (f x : EReal) := by
      intro y
      by_cases hy : y ∈ effectiveDomain f
      · have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
        have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
        have hinner_sub :
            ⟪y - x, u⟫_ℝ = ⟪y, u⟫_ℝ - ⟪x, u⟫_ℝ := by
          simp [sub_eq_add_neg, inner_add_left]
        have hdefect_real :
            ⟪y, u⟫_ℝ - (f y : EReal).toReal ≤ ⟪x, u⟫_ℝ - (f x : EReal).toReal := by
          linarith [hu_halfspace y hy, hinner_sub]
        have hy_toReal :
            ((((f y : EReal).toReal : ℝ) : EReal)) = (f y : EReal) :=
          EReal.coe_toReal hy_top hy_bot
        have hx_toReal :
            ((((f x : EReal).toReal : ℝ) : EReal)) = (f x : EReal) :=
          EReal.coe_toReal hfx_top hfx_bot
        have hdefect_ereal :
            (((⟪y, u⟫_ℝ - (f y : EReal).toReal : ℝ) : EReal)) ≤
              (((⟪x, u⟫_ℝ - (f x : EReal).toReal : ℝ) : EReal)) :=
          EReal.coe_le_coe_iff.mpr hdefect_real
        simpa [EReal.coe_sub, hy_toReal, hx_toReal] using hdefect_ereal
      · have hy_top : (f y : EReal) = ⊤ := by
          exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy))
        rw [hy_top, EReal.sub_top]
        exact bot_le
    have hconj_le : f.asEReal∗ u ≤ ((⟪x, u⟫_ℝ : ℝ) : EReal) - f x := by
      rw [conjugate_apply]
      exact iSup_le hdefect_le
    have hsum_le : (f x : EReal) + f.asEReal∗ u ≤ ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
      simpa [add_comm] using
        (EReal.le_sub_iff_add_le (Or.inl hfx_bot) (Or.inl hfx_top)).1 hconj_le
    -- Proposition 13.15 supplies the reverse Fenchel--Young inequality.
    have hfy_le :
        ((⟪x, u⟫_ℝ : ℝ) : EReal) ≤ (f x : EReal) + f.asEReal∗ u := by
      simpa using fenchel_young_inequality hproper x u
    exact le_antisymm hsum_le hfy_le
  · intro hEq
    have hconj_bot : f.asEReal∗ u ≠ ⊥ :=
      conjugate_ne_bot_of_effectiveDomain_nonempty hdom u
    have hfx_top : (f x : EReal) ≠ ⊤ := by
      intro hx_top
      have hsum_top : (f x : EReal) + f.asEReal∗ u = ⊤ := by
        rw [hx_top]
        exact EReal.top_add_of_ne_bot hconj_bot
      exact EReal.coe_ne_top _ (hEq.symm.trans hsum_top)
    have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
    have hconj_top : f.asEReal∗ u ≠ ⊤ := by
      intro hu_top
      have hsum_top : (f x : EReal) + f.asEReal∗ u = ⊤ := by
        rw [hu_top]
        exact EReal.add_top_of_ne_bot hfx_bot
      exact EReal.coe_ne_top _ (hEq.symm.trans hsum_top)
    have hx : x ∈ effectiveDomain f := by
      rw [mem_effectiveDomain_iff]
      exact lt_of_le_of_ne le_top hfx_top
    have hEq_real : (f x : EReal).toReal + (f.asEReal∗ u).toReal = ⟪x, u⟫_ℝ := by
      have hEq' := hEq
      rw [← EReal.coe_toReal hfx_top hfx_bot,
        ← EReal.coe_toReal hconj_top hconj_bot, ← EReal.coe_add] at hEq'
      exact EReal.coe_eq_coe_iff.mp hEq'
    -- Proposition 16.4 turns the contact equality back into the affine half-space inequalities.
    rw [subdifferential_eq_iInter_affine_halfspaces f x hx, Set.mem_iInter₂]
    intro y hy
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
    have hfy :
        ((⟪y, u⟫_ℝ : ℝ) : EReal) ≤ (f y : EReal) + f.asEReal∗ u := by
      simpa using fenchel_young_inequality hproper y u
    have hfy_real : ⟪y, u⟫_ℝ ≤ (f y : EReal).toReal + (f.asEReal∗ u).toReal := by
      have hfy' := hfy
      rw [← EReal.coe_toReal hy_top hy_bot,
        ← EReal.coe_toReal hconj_top hconj_bot, ← EReal.coe_add] at hfy'
      exact EReal.coe_le_coe_iff.mp hfy'
    have hinner_sub :
        ⟪y - x, u⟫_ℝ = ⟪y, u⟫_ℝ - ⟪x, u⟫_ℝ := by
      simp [sub_eq_add_neg, inner_add_left]
    have hineq :
        ⟪y, u⟫_ℝ - ⟪x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := by
      linarith [hfy_real, hEq_real]
    simpa [hinner_sub] using hineq

/-- Helper for Proposition 16.10: Fenchel--Young equality at an active subgradient forces the
conjugate value to stay finite above. -/
theorem conjugate_value_ne_top_of_mem_subdifferential
    (hdom : (effectiveDomain f).Nonempty) {x u : H} (hu : u ∈ (∂ f) x) :
    f.asEReal∗ u ≠ ⊤ := by
  -- First place `x` in the effective domain so the primal value is finite above.
  have hx_dom : x ∈ SetValuedOperator.dom (∂ f) := by
    rw [SetValuedOperator.mem_dom_iff]
    exact ⟨u, hu⟩
  have hx : x ∈ effectiveDomain f :=
    subdifferential_domain_subset_effectiveDomain f hdom hx_dom
  have hfx_bot : (f x : EReal) ≠ ⊥ := ne_of_gt (f x).2
  -- Then the contact equality from Proposition 16.10(1) rules out `f*(u) = +∞`.
  have hEq :
      (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) :=
    (mem_subdifferential_iff_fenchel_young_eq (f := f) hdom x u).1 hu
  intro hu_top
  have hsum_top : (f x : EReal) + f.asEReal∗ u = ⊤ := by
    rw [hu_top]
    exact EReal.add_top_of_ne_bot hfx_bot
  exact EReal.coe_ne_top _ (hEq.symm.trans hsum_top)

-- Semantic recall: `lean_leansearch` was uninformative for this project-local API; local Chapter
-- 16 uses confirm that clause (2) at the properness level is the one-way transfer to the packaged
-- conjugate, while the inverse-operator identity is deferred to the later `Γ₀(H)` specialization.
/-- Proposition 16.10 (2): if `u ∈ (∂ f) x`, then `x` is a subgradient of the packaged Fenchel
conjugate `properConjugateIoi f hdom` at `u`. -/
theorem mem_subdifferential_properConjugateIoi_of_mem_subdifferential
    (hdom : (effectiveDomain f).Nonempty) (x u : H) :
    u ∈ (∂ f) x → x ∈ (∂ (properConjugateIoi f hdom)) u := by
  intro hu
  let g : H → Set.Ioi (⊥ : EReal) := properConjugateIoi f hdom
  -- First extract the contact equality for `(f, x, u)`.
  have hcontact_f :
      (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) :=
    (mem_subdifferential_iff_fenchel_young_eq (f := f) hdom x u).1 hu
  have hconj_top : f.asEReal∗ u ≠ ⊤ :=
    conjugate_value_ne_top_of_mem_subdifferential (f := f) hdom hu
  have hu_dom_g : u ∈ effectiveDomain g :=
    mem_effectiveDomain_properConjugateIoi_of_ne_top (f := f) hdom hconj_top
  have hdom_g : (effectiveDomain g).Nonempty := ⟨u, hu_dom_g⟩
  have hproper_g : IsProper g.asEReal := by
    refine ⟨fun y ↦ ne_of_gt (g y).2, ?_⟩
    simpa [effectiveDomain, dom] using hdom_g
  -- The biconjugate minorizes `f`, so the contact equality for `f` bounds the packaged
  -- conjugate pair from above.
  have hcontact_g_le :
      (g u : EReal) + g.asEReal∗ x ≤ ((⟪u, x⟫_ℝ : ℝ) : EReal) := by
    calc
      (g u : EReal) + g.asEReal∗ x
          = f.asEReal∗ u + f.asEReal∗∗ x := by
              simp [g, Function.asEReal]
      _ ≤ f.asEReal∗ u + (f x : EReal) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_right (biconjugate_le (f := f.asEReal) x) (f.asEReal∗ u)
      _ = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
            simpa [add_comm] using hcontact_f
      _ = ((⟪u, x⟫_ℝ : ℝ) : EReal) := by
            rw [real_inner_comm]
  -- Proposition 13.15 gives the reverse inequality for the packaged conjugate.
  have hcontact_g_ge :
      ((⟪u, x⟫_ℝ : ℝ) : EReal) ≤ (g u : EReal) + g.asEReal∗ x := by
    simpa [g] using fenchel_young_inequality hproper_g u x
  have hcontact_g :
      (g u : EReal) + g.asEReal∗ x = ((⟪u, x⟫_ℝ : ℝ) : EReal) :=
    le_antisymm hcontact_g_le hcontact_g_ge
  -- Apply Proposition 16.10(1) to the packaged conjugate at `(u, x)`.
  exact
    (mem_subdifferential_iff_fenchel_young_eq (f := g) hdom_g u x).2 hcontact_g

end SubdifferentialConjugation

end

end ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap16/Corollary_16_30.lean -/

open scoped InnerProductSpace


namespace ERealFunction

section SubdifferentialConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Corollary 16.30 is the `Γ₀(H)` reading of the inverse-subdifferential identity.
- `core/canonical`: Proposition 16.10 is the owner theorem at the primitive nonempty-domain layer.
- `bridge/view`: `f∗[hf]` is the canonical `Γ₀(H)` package
  `properConjugateIoi f hf.2.nonempty`.

Corollary 16.30 is therefore the source-facing `Γ₀(H)` specialization of Proposition 16.10,
obtained by rewriting the packaged conjugate through `gammaZeroConjugate`. -/
/-- Corollary 16.30: if `f ∈ Γ₀(H)`, then the inverse of the subdifferential of `f` is the
subdifferential of its Fenchel conjugate `f*`, represented by `f∗[hf]`. -/
theorem inverse_subdifferential_eq_subdifferential_gammaZeroConjugate
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    ((∂ f).inverse : SetValuedOperator H H) = ∂ (f∗[hf]) := by
  ext u x
  constructor
  · intro hux
    rw [SetValuedOperator.mem_inverse_iff] at hux
    simpa [gammaZeroConjugate] using
      mem_subdifferential_properConjugateIoi_of_mem_subdifferential
        (f := f) hf.2.nonempty x u hux
  · intro hxu
    have hconj : f∗[hf] ∈ Γ₀(H) := gammaZeroConjugate_mem_gammaZero hf
    have hu_sub :
        u ∈ (∂ ((f∗[hf])∗[hconj])) x := by
      simpa [gammaZeroConjugate] using
        mem_subdifferential_properConjugateIoi_of_mem_subdifferential
          (f := f∗[hf]) hconj.2.nonempty u x hxu
    have hbiconj :
        (f∗[hf])∗[hconj] = f := by
      funext z
      apply Subtype.ext
      calc
        (((f∗[hf])∗[hconj] z : Set.Ioi (⊥ : EReal)) : EReal) = (f∗[hf]).asEReal∗ z := by
          simp [gammaZeroConjugate]
        _ = f.asEReal∗∗ z := by
          have hpc :=
            properConjugateIoi_conjugate_eq_biconjugate
              (f := f) hf.2.nonempty z
          exact hpc
        _ = (f z : EReal) := by
          exact congrArg (fun g : H → EReal ↦ g z) (biconjugate_eq_of_mem_gammaZero hf)
    rw [SetValuedOperator.mem_inverse_iff]
    have hu_f : u ∈ (∂ f) x := by
      simpa [hbiconj] using hu_sub
    exact hu_f

end SubdifferentialConjugation

end ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap16/Proposition_16_44.lean -/

open scoped InnerProductSpace Pointwise


namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Proposition 16 44: membership in `Id + ∂ f` at `p` is exactly the residual
subgradient inclusion `x - p ∈ ∂ f(p)`. -/
private theorem mem_id_add_subdifferential_iff_sub_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (x p : H) :
    x ∈ ((id : H → H).toSetValuedOperator + ∂ f) p ↔ x - p ∈ (∂ f) p := by
  constructor
  · intro hx
    rcases Set.mem_add.mp hx with ⟨u, hu, v, hv, huv⟩
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hu
    subst u
    have hsub : x - p = v := by
      rw [sub_eq_iff_eq_add]
      simpa [add_comm] using huv.symm
    simpa [hsub] using hv
  · intro hx
    have hid_mem : p ∈ (id : H → H).toSetValuedOperator p := by
      simp [Function.toSetValuedOperator_apply]
    have hdecomp : p + (x - p) = x := by
      abel_nf
    exact Set.mem_add.2 ⟨p, hid_mem, x - p, hx, hdecomp⟩

-- Proof sketch: rewrite `p = Prox_f x` as `IsProxPoint f x p` via the Chapter 12 owner theorem
-- `eq_proximityOperator_of_isProxPoint`, then apply Proposition 12.26 and Definition 16.1.
/-- Proposition 16 44: for `f ∈ Γ₀(H)` and `x, p ∈ H`, the point `p` equals `Prox_f x` exactly
when the residual `x - p` belongs to the subdifferential of `f` at `p`. -/
theorem eq_proximityOperator_iff_sub_mem_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (x p : H) :
    p = Prox[f, hf] x ↔
      x - p ∈ (∂ f) p := by
  have hconv : ConvexOn f (effectiveDomain f) := (mem_gammaZero_iff.mp hf).2
  constructor
  · intro hp
    have hp_prox : IsProxPoint f x p := by
      rw [hp]
      simpa using
        proximityOperator_isProxPoint f
          (hasUniqueProxPoint_of_mem_gammaZero (f := f) hf) x
    rw [mem_subdifferential_iff]
    exact (isProxPoint_iff_forall_inner_add_le f hconv x p).mp hp_prox
  · intro hp
    rw [mem_subdifferential_iff] at hp
    have hp_prox : IsProxPoint f x p :=
      (isProxPoint_iff_forall_inner_add_le f hconv x p).mpr hp
    simpa using
      eq_proximityOperator_of_isProxPoint f
        (hasUniqueProxPoint_of_mem_gammaZero (f := f) hf) hp_prox

/-- The residual of the positively scaled proximity operator is a subgradient. -/
theorem scaledProximityOperator_residual_mem
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (γ : PosReal) (x : H) :
    (γ : ℝ)⁻¹ • (x - Prox[γ, f, hf] x) ∈
      (∂ f) (Prox[γ, f, hf] x) := by
  let g : H → Set.Ioi (⊥ : EReal) := γ • f
  have hg : g ∈ Γ₀(H) := smul_mem_gammaZero f hf γ
  let p : H := Prox[γ, f, hf] x
  have hp : p = Prox[g, hg] x := by
    rfl
  have hsub : x - p ∈ (∂ g) p := by
    rw [hp]
    exact (eq_proximityOperator_iff_sub_mem_subdifferential hg x p).mp rfl
  rw [subdifferential_posReal_smul_eq_smul f γ] at hsub
  change x - p ∈ (γ : ℝ) • ((∂ f) p) at hsub
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hsub
  simpa [p] using hsub

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap20/Theorem_20_25 -/

/-- Moreau's theorem: the subdifferential of a `Γ₀` function is maximally monotone. -/
theorem subdifferential_isMaximallyMonotone_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    Maximal SetValuedOperator.IsMonotone (∂ f) := by
  have hmono : SetValuedOperator.IsMonotone (∂ f) := by
    intro x y u hu v hv
    simpa only [subdifferential] using
      (isMonotone_subdifferential (fun x : H ↦ (f x : EReal))
        (isProper_of_mem_gammaZero (f := f) hf) u hu v hv)
  have hmax : Maximal SetValuedOperator.IsMonotone (∂ f) := by
    rw [minty_surjective_iff_maximal_isMonotone hmono]
    intro y
    let p : H := Prox[f, hf] y
    refine ⟨p, y - p, ?_, by abel⟩
    exact (eq_proximityOperator_iff_sub_mem_subdifferential hf y p).mp rfl
  exact hmax

/-- Compatibility form of Moreau's theorem using Foundation's original maximality predicate. -/
theorem subdifferential_isMaximalMonotone_of_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    SetValuedOperator.IsMaximalMonotone (∂ f) :=
  (SetValuedOperator.isMaximalMonotone_iff_maximal_isMonotone (∂ f)).mpr
    (subdifferential_isMaximallyMonotone_of_mem_gammaZero hf)

-- Proof sketch: extensionality on `x` and set extensionality on `p` reduce the operator identity
-- to the pointwise equivalence above and the singleton description of `id.toSetValuedOperator`.
/-- The proximity operator of a `Γ₀(H)` function is the inverse of the set-valued operator
`id.toSetValuedOperator + ∂ f`, which is the textbook formula `Prox_f = (Id + ∂ f)⁻¹`
written through the canonical singleton-valued operator owner. -/
theorem singleton_proximityOperator_eq_inverse_add_subdifferential
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) :
    Prox[f, hf].toSetValuedOperator = ((id : H → H).toSetValuedOperator + ∂ f).inverse := by
  funext x
  ext p
  constructor
  · intro hp
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff] at hp
    rw [SetValuedOperator.mem_inverse_iff]
    exact (mem_id_add_subdifferential_iff_sub_mem_subdifferential (f := f) x p).2 <|
      (eq_proximityOperator_iff_sub_mem_subdifferential hf x p).1 hp
  · intro hp
    rw [Function.toSetValuedOperator_apply, Set.mem_singleton_iff]
    rw [SetValuedOperator.mem_inverse_iff] at hp
    exact (eq_proximityOperator_iff_sub_mem_subdifferential hf x p).2 <|
      (mem_id_add_subdifferential_iff_sub_mem_subdifferential (f := f) x p).1 hp

/-! Source item: Attouch_Adly_First_order_inertial_algorithms_involving_dry_friction_damping_2021
items/rem_1 -/

/-- If the scaled vector `γ⁻¹ • z` is a subgradient of `φ` at `0`, then the scaled proximal
point `Prox_{γφ}(z)` vanishes: the subgradient inclusion at `0` forces the proximal minimizer
of `y ↦ γ φ(y) + (1 / 2) ‖z - y‖²` to be `0`. -/
theorem proximityOperator_eq_zero_of_inv_smul_mem_subdifferential
    (φ : H → EReal) (hproper : IsProper φ) (hf : properIoi φ hproper ∈ Γ₀(H))
    (γ : PosReal) (z : H) (hsub : (γ : ℝ)⁻¹ • z ∈ subdifferential φ 0) :
    Prox[γ, properIoi φ hproper, hf] z = 0 := by
  rw [eq_comm]
  exact (eq_proximityOperator_iff_sub_mem_subdifferential (f := γ • properIoi φ hproper)
    (smul_mem_gammaZero (properIoi φ hproper) hf γ) z 0).2 <| by
      rw [subdifferential_posReal_smul_eq_smul (properIoi φ hproper) γ]
      change (z - 0) ∈ (γ : ℝ) • ((∂ (properIoi φ hproper)) 0)
      rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne']
      simpa [sub_zero, properIoi_apply] using hsub

end SubdifferentialCalculus

end ERealFunction


/-! Source item: Bauschke-lean-project/BauschkeLean/Chap16/Proposition_16_33.lean -/

namespace ERealFunction

section SubdifferentialConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 16.33 is the minimizer/subgradient-at-zero statement for `f*`.
- `core/canonical`: the owner declarations are `Argmin`, `∂`, `SetValuedOperator.zeros`, and
  `SetValuedOperator.inverse`.
- `bridge/view`: `f∗[hf]` is the canonical `Γ₀(H)` packaging of the Fenchel conjugate.

The proposition should therefore stay source-facing, while its implementation is the direct owner
combination of Theorem 16.3 with Corollary 16.30, evaluated at `0`. -/
/-- Proposition 16.33: for `f ∈ Γ₀(H)`, the set of minimizers of `f` coincides with the
subdifferential of its Fenchel conjugate at `0`, represented here by `f∗[hf]`. -/
theorem argmin_eq_subdifferential_gammaZeroConjugate_zero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) :
    Optimization.argminSet f.asEReal = (∂ (f∗[hf])) 0 := by
  ext x
  rw [argmin_eq_zeros_subdifferential, SetValuedOperator.mem_zeros_iff]
  rw [← inverse_subdifferential_eq_subdifferential_gammaZeroConjugate f hf]
  exact (SetValuedOperator.mem_inverse_iff (∂ f) 0 x).symm

end SubdifferentialConjugation

end ERealFunction


/-! Source item: Bauschke-lean-project/BauschkeLean/Chap16/Example_16_32.lean -/

namespace ERealFunction

noncomputable section

section NormSubdifferential

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Classical decidability of equality on `H`, used to state the piecewise formula for the norm
subdifferential. -/
local instance instDecidableEqNormSubdifferential : DecidableEq H := Classical.decEq H

/-- Helper for Example 16 32: for the norm, subdifferential membership is the real-valued affine
minorant inequality obtained by unpacking the `EReal` owner. -/
private lemma mem_subdifferential_norm_iff (x u : H) :
    u ∈ (∂ (fun y : H ↦ ‖y‖).toEReal) x ↔
      ∀ y : H, inner ℝ (y - x) u + ‖x‖ ≤ ‖y‖ := by
  rw [ERealFunction.mem_subdifferential_iff]
  constructor
  · intro hu y
    -- All terms are finite reals here, so the `EReal` inequality descends to `ℝ`.
    exact EReal.coe_le_coe_iff.mp (by simpa [EReal.coe_add] using hu y)
  · intro hu y
    -- Conversely, recast the real inequality back into the `EReal` owner.
    exact (EReal.coe_le_coe_iff).2 (by simpa [EReal.coe_add] using hu y)

/-- Helper for Example 16 32: at the origin, the norm subdifferential is the closed unit ball. -/
private lemma mem_subdifferential_norm_zero_iff (u : H) :
    u ∈ (∂ (fun y : H ↦ ‖y‖).toEReal) (0 : H) ↔ u ∈ Metric.closedBall (0 : H) 1 := by
  rw [mem_subdifferential_norm_iff]
  constructor
  · intro hu
    -- Testing the affine minorant inequality at `y = u` yields `‖u‖² ≤ ‖u‖`.
    have hsq_le : ‖u‖ ^ 2 ≤ ‖u‖ := by
      simpa [sub_zero, real_inner_self_eq_norm_sq] using hu u
    have hu_norm_le : ‖u‖ ≤ 1 := by
      nlinarith [hsq_le, norm_nonneg u]
    simpa [Metric.mem_closedBall, dist_eq_norm] using hu_norm_le
  · intro hu y
    -- The unit-ball bound and Cauchy--Schwarz give the required affine minorant inequality.
    have hu_norm_le : ‖u‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hu
    calc
      inner ℝ (y - (0 : H)) u + ‖(0 : H)‖ ≤ ‖y - (0 : H)‖ * ‖u‖ := by
        simpa using real_inner_le_norm (y - (0 : H)) u
      _ ≤ ‖y - (0 : H)‖ * 1 := by
        exact mul_le_mul_of_nonneg_left hu_norm_le (norm_nonneg (y - (0 : H)))
      _ = ‖y‖ := by simp

/-- Helper for Example 16 32: away from the origin, the norm subdifferential is the singleton
containing the normalized vector. -/
private lemma mem_subdifferential_norm_nonzero_iff_eq_inv_norm_smul {x u : H} (hx : x ≠ 0) :
    u ∈ (∂ (fun y : H ↦ ‖y‖).toEReal) x ↔ u = ‖x‖⁻¹ • x := by
  rw [mem_subdifferential_norm_iff]
  constructor
  · intro hu
    -- Testing at `y = 0` gives the lower bound `‖x‖ ≤ ⟪x, u⟫`.
    have hu_zero : ‖x‖ ≤ inner ℝ x u := by
      have hzero := hu (0 : H)
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hzero
    have hu_norm_ge : 1 ≤ ‖u‖ := by
      have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
      have hinner_le : inner ℝ x u ≤ ‖x‖ * ‖u‖ := real_inner_le_norm x u
      have hmul : ‖x‖ ≤ ‖x‖ * ‖u‖ := le_trans hu_zero hinner_le
      by_contra hu_lt
      have hu_lt' : ‖u‖ < 1 := lt_of_not_ge hu_lt
      have hmul_lt : ‖x‖ * ‖u‖ < ‖x‖ := by
        nlinarith
      exact (not_lt_of_ge hmul hmul_lt)
    -- Testing at `y = x + u` and using the triangle inequality gives the reverse bound.
    have hu_eval := hu (x + u)
    have hu_norm_le : ‖u‖ ≤ 1 := by
      have hsq_add : ‖u‖ ^ 2 + ‖x‖ ≤ ‖x + u‖ := by
        simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, real_inner_self_eq_norm_sq]
          using hu_eval
      have htri : ‖x + u‖ ≤ ‖x‖ + ‖u‖ := norm_add_le x u
      have hsq_le : ‖u‖ ^ 2 ≤ ‖u‖ := by
        linarith
      nlinarith [hsq_le, norm_nonneg u]
    have hu_norm : ‖u‖ = 1 := by
      linarith
    -- Equality in Cauchy--Schwarz aligns `u` with `x` on the same nonnegative ray.
    have hinner_eq_norm : inner ℝ x u = ‖x‖ := by
      have hinner_le : inner ℝ x u ≤ ‖x‖ := by
        simpa [hu_norm] using (real_inner_le_norm x u)
      linarith
    have hinner_eq : inner ℝ x u = ‖x‖ * ‖u‖ := by
      simpa [hu_norm] using hinner_eq_norm
    have halign : ‖u‖ • x = ‖x‖ • u := (inner_eq_norm_mul_iff_real).1 hinner_eq
    have hxnorm_ne : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
    calc
      u = ‖x‖⁻¹ • (‖x‖ • u) := by
        rw [smul_smul, inv_mul_cancel₀ hxnorm_ne, one_smul]
      _ = ‖x‖⁻¹ • (‖u‖ • x) := by rw [halign]
      _ = ‖x‖⁻¹ • x := by rw [hu_norm, one_smul]
  · intro hu y
    -- Substituting the normalized vector reduces the inequality to Cauchy--Schwarz.
    rw [hu]
    calc
      inner ℝ (y - x) (‖x‖⁻¹ • x) + ‖x‖ = inner ℝ y (‖x‖⁻¹ • x) := by
        rw [inner_sub_left, real_inner_smul_right, real_inner_smul_right,
          real_inner_self_eq_norm_sq]
        field_simp [norm_ne_zero_iff.mpr hx]
        ring
      _ ≤ ‖y‖ * ‖‖x‖⁻¹ • x‖ := real_inner_le_norm y (‖x‖⁻¹ • x)
      _ ≤ ‖y‖ * 1 := by
        exact mul_le_mul_of_nonneg_left
          (by simpa using (norm_smul_inv_norm hx).le) (norm_nonneg y)
      _ = ‖y‖ := by simp

-- Proof sketch: unpack the defining affine-minorant inequality for the norm subdifferential. At
-- `x = 0`, testing at `y = u` shows `‖u‖² ≤ ‖u‖`, hence `‖u‖ ≤ 1`, and the converse is just
-- Cauchy--Schwarz. For `x ≠ 0`, testing at `y = 0` and `y = x + u` gives `‖u‖ = 1`; equality in
-- Cauchy--Schwarz then forces `u` to be the normalized vector `‖x‖⁻¹ • x`.
/-- Example 16 32: the subdifferential of the norm is the singleton containing the normalized
vector away from `0`, and the closed unit ball at `0`. -/
theorem subdifferential_norm_eq_singleton_or_closedBall (x : H) :
    (∂ (fun y : H ↦ ‖y‖).toEReal) x =
      if x = 0 then (Metric.closedBall (0 : H) 1 : Set H) else ({‖x‖⁻¹ • x} : Set H) := by
  by_cases hx : x = 0
  · subst hx
    -- The origin branch is exactly the closed-ball characterization proved above.
    ext u
    rw [mem_subdifferential_norm_zero_iff]
    simp
  · -- Away from `0`, membership is equivalent to equality with the normalized vector.
    ext u
    rw [mem_subdifferential_norm_nonzero_iff_eq_inv_norm_smul (x := x) (u := u) hx]
    simp [hx]
end NormSubdifferential

end



/-! Source item: Bauschke-lean-project/BauschkeLean/Chap16/Example_16_12.lean -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: apply Proposition 16.10 to `halfSquaredNorm`, use Example 13.6 to
-- identify its Fenchel conjugate with itself, and then simplify the Fenchel--Young equality to
-- the identity `u = x`.
/-- Example 16.12: the subdifferential of the quadratic function `f = (1 / 2)‖·‖²` is the
identity set-valued operator, written pointwise as the singleton-valued map `x ↦ {x}`. -/
theorem subdifferential_halfSquaredNorm_eq_singleton :
    ∂ halfSquaredNorm = (fun x : H ↦ ({x} : Set H)) := by
  ext x u
  rw [Set.mem_singleton_iff]
  constructor
  · intro hu
    have hfy :=
      (mem_subdifferential_iff_fenchel_young_eq (f := halfSquaredNorm)
        ⟨0, by rw [mem_effectiveDomain_iff]; simp⟩ x u).1 hu
    rw [conjugate_halfSquaredNorm] at hfy
    norm_num [halfSquaredNorm_apply] at hfy
    have hfy' :
        (1 / 2 : ℝ) * ‖x‖ ^ (2 : ℕ) + (1 / 2 : ℝ) * ‖u‖ ^ (2 : ℕ) = ⟪x, u⟫_ℝ := by
      exact_mod_cast hfy
    have hnorm : ‖x - u‖ ^ (2 : ℕ) = 0 := by
      rw [norm_sub_sq_real]
      nlinarith [hfy', real_inner_comm x u]
    have hzero : ‖x - u‖ = 0 := sq_eq_zero_iff.mp hnorm
    exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm
  · intro hu
    subst u
    exact
      (mem_subdifferential_iff_fenchel_young_eq (f := halfSquaredNorm)
        ⟨0, by rw [mem_effectiveDomain_iff]; simp⟩ x x).2 <| by
      rw [conjugate_halfSquaredNorm, Function.asEReal_apply, halfSquaredNorm_apply,
        real_inner_self_eq_norm_sq]
      exact_mod_cast (by ring :
        ‖x‖ ^ (2 : ℕ) / 2 + ‖x‖ ^ (2 : ℕ) / 2 = ‖x‖ ^ (2 : ℕ))

-- Proof sketch: evaluate the operator identity from
-- `subdifferential_halfSquaredNorm_eq_singleton` at `x`.
/-- The subdifferential of `x ↦ ‖x‖² / 2` at `x` is the singleton `{x}`. -/
@[simp] theorem subdifferential_halfSquaredNorm_apply (x : H) :
    (∂ halfSquaredNorm) x = ({x} : Set H) := by
  rw [subdifferential_halfSquaredNorm_eq_singleton]

end


/-! Source item: Bauschke-lean-project/BauschkeLean/Chap16/Example_16_13.lean -/

section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: for `x ∈ C`, unfold `(∂ ι[C]) x`; the indicator is `0` on `C` and `⊤` off `C`,
-- so the subgradient inequality reduces to `⟪y - x, u⟫ ≤ 0` for all `y ∈ C`, which is exactly
-- the defining inequality of `N[C] x`. For `x ∉ C`, nonemptiness of `C` furnishes `y ∈ C`,
-- forcing the subdifferential to be empty, matching `normalCone_of_not_mem`.
/-- Example 16.13: for a nonempty subset `C` of a real Hilbert space, hence in particular for a
nonempty convex subset, the subdifferential of the indicator `ι_C` is exactly the normal cone
mapping `N_C`. -/
theorem subdifferential_setIndicator_eq_normalCone
    (C : Set H) (hC_nonempty : C.Nonempty) :
    ∂ ι[C] = N[C] := by
  ext x u
  by_cases hx : x ∈ C
  · rw [Set.normalCone_of_mem hx, mem_subdifferential_iff]
    have hsup_iff :
        innerSupremumOn (C - ({x} : Set H)) u ≤ 0 ↔ ∀ y ∈ C, ⟪y - x, u⟫_ℝ ≤ 0 := by
      exact
        (innerSupremumOn_sub_singleton_le_zero_iff :
          innerSupremumOn (C - ({x} : Set H)) u ≤ 0 ↔ ∀ y ∈ C, ⟪y - x, u⟫_ℝ ≤ 0)
    constructor
    · intro hu
      refine hsup_iff.2 ?_
      intro y hy
      have hy' :
          ((⟪y - x, u⟫_ℝ : EReal) + (ι[C] x : EReal) ≤ (ι[C] y : EReal)) :=
        hu y
      have hinner : (⟪y - x, u⟫_ℝ : EReal) ≤ 0 := by
        simpa [ERealFunction.indicator, hx, hy] using hy'
      exact_mod_cast hinner
    · intro hu y
      by_cases hy : y ∈ C
      · have hinner : ⟪y - x, u⟫_ℝ ≤ 0 := hsup_iff.1 hu y hy
        have hx_zero : (ι[C] x : EReal) = 0 := by
          simp [ERealFunction.indicator, hx]
        have hy_zero : (ι[C] y : EReal) = 0 := by
          simp [ERealFunction.indicator, hy]
        change ((⟪y - x, u⟫_ℝ : EReal) + (ι[C] x : EReal) ≤ (ι[C] y : EReal))
        rw [hx_zero, hy_zero]
        simpa using (show ((⟪y - x, u⟫_ℝ : EReal) ≤ (0 : EReal)) by
          exact_mod_cast hinner)
      · have hx_zero : (ι[C] x : EReal) = 0 := by
          simp [ERealFunction.indicator, hx]
        have hy_top : (ι[C] y : EReal) = ⊤ := by
          simp [ERealFunction.indicator, hy]
        change ((⟪y - x, u⟫_ℝ : EReal) + (ι[C] x : EReal) ≤ (ι[C] y : EReal))
        rw [hx_zero, hy_top]
        simp
  · rw [Set.normalCone_of_not_mem hx, mem_subdifferential_iff]
    constructor
    · intro hu
      have hy :
          ((⟪hC_nonempty.choose - x, u⟫_ℝ : EReal) + (ι[C] x : EReal) ≤
            (ι[C] hC_nonempty.choose : EReal)) :=
        hu hC_nonempty.choose
      have hx_top : (ι[C] x : EReal) = ⊤ := by
        simp [ERealFunction.indicator, hx]
      have hchoose_zero : (ι[C] hC_nonempty.choose : EReal) = 0 := by
        simp [ERealFunction.indicator, hC_nonempty.choose_spec]
      rw [hx_top, hchoose_zero] at hy
      simp at hy
    · simp

end

end ERealFunction

/-! Source item: Bauschke-lean-project/BauschkeLean/Chap16/Proposition_16_5.lean -/

open scoped InnerProductSpace

namespace ERealFunction

section BiconjugationAndSubdifferentials

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (f : H → Set.Ioi (⊥ : EReal)) (x : H)

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Proposition 16 5: if the effective domain is empty, then the canonical
`EReal`-valued coercion of `f` is identically `+∞`. -/
theorem asEReal_eq_top_of_effectiveDomain_eq_empty
    (hempty : effectiveDomain f = ∅) :
    f.asEReal = (fun _ : H ↦ (⊤ : EReal)) := by
  funext y
  -- Empty effective domain means every point value fails to be finite above, hence equals `⊤`.
  have hy_not_mem : y ∉ effectiveDomain f := by
    simp [hempty]
  have hy_not_lt : ¬ (f y : EReal) < ⊤ := by
    simpa [mem_effectiveDomain_iff] using hy_not_mem
  exact le_antisymm le_top (not_lt.mp hy_not_lt)

omit [CompleteSpace H] in
/-- Helper for Proposition 16 5: the Fenchel conjugate of the constant `+∞` function is the
constant `-∞` function. -/
theorem conjugate_top_eq_bot :
    ((fun _ : H ↦ (⊤ : EReal))∗) = (fun _ : H ↦ (⊥ : EReal)) := by
  funext u
  rw [conjugate_apply]
  apply le_antisymm
  · -- Every affine defect against `⊤` is `⊥`, so the supremum is bounded above by `⊥`.
    refine iSup_le fun y ↦ ?_
    simp
  · exact bot_le

omit [CompleteSpace H] in
/-- Helper for Proposition 16 5: the Fenchel biconjugate of the constant `+∞` function is again
the constant `+∞` function. -/
theorem biconjugate_top_eq_top :
    ((fun _ : H ↦ (⊤ : EReal))∗∗) = (fun _ : H ↦ (⊤ : EReal)) := by
  rw [conjugate_top_eq_bot]
  funext x
  rw [conjugate_apply]
  apply le_antisymm
  · exact le_top
  · -- Evaluating the defining supremum at `0` already yields the value `⊤`.
    have htop_le :
        (⊤ : EReal) ≤
          ⨆ u : H, ((⟪u, x⟫_ℝ : ℝ) : EReal) - (⊥ : EReal) := by
      refine le_iSup (fun u : H ↦ ((⟪u, x⟫_ℝ : ℝ) : EReal) - (⊥ : EReal)) 0
    exact htop_le

-- Proof sketch: choose a subgradient `u ∈ (∂ f) x`. Apply Proposition 16.10 to `f` to obtain
-- Fenchel--Young equality for `(x,u)`, then use Proposition 16.10 again on the packaged Fenchel
-- conjugate `properConjugateIoi f hdom` to obtain the corresponding equality for `(u,x)`. After
-- rewriting the middle conjugate value by `toReal`, both identities solve for the same quantity,
-- so `f** x = f x`.
/-- Proposition 16 5 (1): if an `]-∞,+∞]`-valued function is subdifferentiable at `x`, then its
Fenchel biconjugate agrees with `f` at `x`. -/
theorem biconjugate_eq_self_at_of_subdifferentiableAt
    (hxsub : SubdifferentiableAt f x) :
    f.asEReal∗∗ x = f.asEReal x := by
  let _ : CompleteSpace H := inferInstance
  by_cases hdom : (effectiveDomain f).Nonempty
  · rcases hxsub with ⟨u, hu⟩
    have hconj_top : f.asEReal∗ u ≠ ⊤ :=
      conjugate_value_ne_top_of_mem_subdifferential (f := f) (x := x) hdom hu
    have hconj_bot : f.asEReal∗ u ≠ ⊥ :=
      conjugate_ne_bot_of_effectiveDomain_nonempty (f := f) hdom u
    have hfy_f :
        (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) :=
      (mem_subdifferential_iff_fenchel_young_eq (f := f) (x := x) hdom u).1 hu
    let g : H → Set.Ioi (⊥ : EReal) := properConjugateIoi f hdom
    have hxu : x ∈ (∂ g) u := by
      -- Active subgradients transfer directly to the packaged conjugate.
      simpa [g] using
        mem_subdifferential_properConjugateIoi_of_mem_subdifferential
          (f := f) hdom x u hu
    have hgdom : (effectiveDomain g).Nonempty := by
      refine ⟨u, ?_⟩
      -- The active slope remains a finite point after packaging the conjugate.
      simpa [g] using
        mem_effectiveDomain_properConjugateIoi_of_ne_top (f := f) hdom hconj_top
    have hfy_g :
        (g u : EReal) + g.asEReal∗ x = ((⟪u, x⟫_ℝ : ℝ) : EReal) :=
      (mem_subdifferential_iff_fenchel_young_eq (f := g) (x := u) hgdom x).1 hxu
    have hgu_eq : (g u : EReal) = f.asEReal∗ u := by
      simp [g]
    have hgstar_apply : g.asEReal∗ x = f.asEReal∗∗ x := by
      simp [g]
    let a : ℝ := (f.asEReal∗ u).toReal
    have ha : ((a : ℝ) : EReal) = f.asEReal∗ u := by
      exact EReal.coe_toReal hconj_top hconj_bot
    have hf_eq :
        f.asEReal x = ((⟪x, u⟫_ℝ : ℝ) : EReal) - (a : EReal) := by
      -- The first Fenchel--Young identity solves for `f x`.
      have hfy_f' : f.asEReal x + (a : EReal) = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
        rw [ha]
        simpa using hfy_f
      have hfy_f'' := congrArg (fun t : EReal ↦ t - a) hfy_f'
      simpa [EReal.add_sub_cancel_right] using hfy_f''
    have hbiconj_eq :
        f.asEReal∗∗ x = ((⟪x, u⟫_ℝ : ℝ) : EReal) - (a : EReal) := by
      have hfy_g' :
          f.asEReal∗∗ x + (a : EReal) = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
        -- The packaged-conjugate Fenchel--Young identity solves for `f** x`.
        rw [ha, ← hgu_eq, ← hgstar_apply]
        simpa [real_inner_comm, add_comm] using hfy_g
      have hfy_g'' := congrArg (fun t : EReal ↦ t - a) hfy_g'
      simpa [EReal.add_sub_cancel_right] using hfy_g''
    exact hbiconj_eq.trans hf_eq.symm
  · have hempty : effectiveDomain f = ∅ := Set.not_nonempty_iff_eq_empty.mp hdom
    have htop : f.asEReal = (fun _ : H ↦ (⊤ : EReal)) :=
      asEReal_eq_top_of_effectiveDomain_eq_empty (f := f) hempty
    have hbtop : f.asEReal∗∗ = (fun _ : H ↦ (⊤ : EReal)) := by
      rw [htop]
      exact biconjugate_top_eq_top (H := H)
    have hfx_top : f.asEReal x = ⊤ := by
      simpa [htop] using congrFun htop x
    -- If the effective domain is empty, both `f` and its biconjugate are the constant `⊤`
    -- function.
    simpa [hfx_top] using congrFun hbtop x

-- Proof sketch: choose `u₀ ∈ ∂ f x` from `hxsub` and package the conjugate as
-- `g := properConjugateIoi f hdom`. The one-way transfer from active subgradients sends
-- `u ∈ ∂ f x` to `x ∈ ∂ g u`, and applying the same transfer to `g` yields
-- `u ∈ ∂ f** x`. For the converse inclusion, rewrite `u ∈ ∂ f** x` as Fenchel--Young equality for
-- the packaged biconjugate `p := properConjugateIoi g hgdom`, then use clause (1) to replace
-- `p x = f x` and Proposition 13.16 to identify `p* = g = f*`.
/-- Clause (2) of Proposition 16 5: if an `]-∞,+∞]`-valued function is subdifferentiable at `x`,
then the
subdifferential of the Fenchel biconjugate `f^{**}` at `x` coincides with the subdifferential of
`f` at `x`. -/
theorem biconjugate_subdifferential_eq_subdifferential_at_of_subdifferentiableAt
    (hxsub : SubdifferentiableAt f x) :
    (∂ (f.asEReal∗∗)) x = (∂ f) x := by
  by_cases hdom : (effectiveDomain f).Nonempty
  · have hxsub' := hxsub
    rcases hxsub with ⟨u0, hu0⟩
    have hxeff : x ∈ effectiveDomain f :=
      SubdifferentiableAt.mem_effectiveDomain hdom hxsub'
    have hconj_top : f.asEReal∗ u0 ≠ ⊤ :=
      conjugate_value_ne_top_of_mem_subdifferential (f := f) (x := x) hdom hu0
    let g : H → Set.Ioi (⊥ : EReal) := properConjugateIoi f hdom
    have hgdom : (effectiveDomain g).Nonempty := by
      refine ⟨u0, ?_⟩
      -- The chosen slope `u₀` lies in the effective domain of the packaged conjugate.
      simpa [g] using
        mem_effectiveDomain_properConjugateIoi_of_ne_top (f := f) hdom hconj_top
    let p : H → Set.Ioi (⊥ : EReal) := properConjugateIoi g hgdom
    have hbiconj_eq :
        f.asEReal∗∗ x = f.asEReal x :=
      biconjugate_eq_self_at_of_subdifferentiableAt (f := f) (x := x) hxsub'
    have hpx : (p x : EReal) = f.asEReal x := by
      simpa [p, g, properConjugateIoi_apply] using hbiconj_eq
    have hpdom : (effectiveDomain p).Nonempty := by
      refine ⟨x, ?_⟩
      rw [mem_effectiveDomain_iff]
      simpa [hpx] using
        (mem_effectiveDomain_iff.mp hxeff)
    have htriple_apply (u : H) : p.asEReal∗ u = (g u : EReal) := by
      simpa [p, g, properConjugateIoi_apply] using
        congrFun (triple_conjugate_eq_conjugate (f := f.asEReal)) u
    ext u
    constructor
    · intro hu
      have hEq_p :
          (p x : EReal) + p.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
        have hu_p : u ∈ (∂ p) x := by
          -- Rewrite the biconjugate fiber on the packaged surface.
          simpa [p, g, properConjugateIoi_apply] using hu
        exact (mem_subdifferential_iff_fenchel_young_eq (f := p) (x := x) hpdom u).1 hu_p
      have hEq_f :
          (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
        have hpx' : (p x : EReal) = (f x : EReal) := by
          simpa using hpx
        have hpstar : p.asEReal∗ u = f.asEReal∗ u := by
          simpa [p, g, properConjugateIoi_apply] using htriple_apply u
        calc
          (f x : EReal) + f.asEReal∗ u = (p x : EReal) + p.asEReal∗ u := by
            rw [← hpx', ← hpstar]
          _ = ((⟪x, u⟫_ℝ : ℝ) : EReal) := hEq_p
      exact (mem_subdifferential_iff_fenchel_young_eq (f := f) (x := x) hdom u).2 hEq_f
    · intro hu
      have hxu : x ∈ (∂ g) u := by
        -- First transfer `u ∈ ∂ f x` to the packaged conjugate `g`.
        simpa [g] using
          mem_subdifferential_properConjugateIoi_of_mem_subdifferential
            (f := f) hdom x u hu
      have hu_p : u ∈ (∂ p) x := by
        -- Apply the same transfer once more to package the biconjugate.
        simpa [p] using
          mem_subdifferential_properConjugateIoi_of_mem_subdifferential
            (f := g) hgdom u x hxu
      -- The second packaged conjugate is exactly the Fenchel biconjugate of `f`.
      simpa [p, g, properConjugateIoi_apply] using hu_p
  · have hempty : effectiveDomain f = ∅ := Set.not_nonempty_iff_eq_empty.mp hdom
    have htop : f.asEReal = (fun _ : H ↦ (⊤ : EReal)) :=
      asEReal_eq_top_of_effectiveDomain_eq_empty (f := f) hempty
    have hbtop : f.asEReal∗∗ = (fun _ : H ↦ (⊤ : EReal)) := by
      rw [htop]
      exact biconjugate_top_eq_top (H := H)
    -- In the empty-domain branch, both operators are the subdifferential of the constant `⊤`
    -- function, hence both fibers are all of `H`.
    ext u
    rw [mem_subdifferential_iff, mem_subdifferential_iff]
    have htop_apply (z : H) : (f z : EReal) = ⊤ := by
      simpa using congrFun htop z
    have hbtop_apply (z : H) : f.asEReal∗∗ z = ⊤ := by
      simpa using congrFun hbtop z
    constructor
    · intro _hu y
      calc
        (((⟪y - x, u⟫_ℝ : ℝ) : EReal) + (f x : EReal)) =
            (((⟪y - x, u⟫_ℝ : ℝ) : EReal) + (⊤ : EReal)) := by
              rw [htop_apply x]
        _ ≤ (f y : EReal) := by
              rw [htop_apply y]
              exact le_top
    · intro _hu y
      calc
        (((⟪y - x, u⟫_ℝ : ℝ) : EReal) + f.asEReal∗∗ x) =
            (((⟪y - x, u⟫_ℝ : ℝ) : EReal) + (⊤ : EReal)) := by
              rw [hbtop_apply x]
        _ ≤ f.asEReal∗∗ y := by
              rw [hbtop_apply y]
              exact le_top

end BiconjugationAndSubdifferentials

end ERealFunction


/-! Source item: Bauschke-lean-project/BauschkeLean/Chap16/Proposition_16_16.lean -/

open scoped InnerProductSpace Pointwise Set

namespace ERealFunction

section SubdifferentialAndEpigraphNormalCone

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

attribute [local instance] prod_seminormedAddCommGroup_l2_real
attribute [local instance] prod_normedAddCommGroup_l2_real
attribute [local instance] prod_normedSpace_l2_real
attribute [local instance] prod_innerProductSpace_l2_real

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 16.16: an effective-domain point gives a canonical real-height point of
the epigraph. -/
private lemma mem_epigraph_toReal_of_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} (hy : y ∈ effectiveDomain f) :
    (y, (f y : EReal).toReal) ∈ epigraph f.asEReal := by
  -- Finiteness of `f y` says that the canonical real height lies on the epigraph.
  rw [mem_epigraph_iff]
  exact EReal.le_coe_toReal (ne_of_lt (mem_effectiveDomain_iff.mp hy))

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] in
/-- Helper for Proposition 16.16: every real-height epigraph point has base point in the
effective domain, and its height dominates the finite value `(f y).toReal`. -/
private lemma effectiveDomain_and_toReal_le_of_mem_epigraph
    {f : H → Set.Ioi (⊥ : EReal)} {y : H} {η : ℝ}
    (hyη : (y, η) ∈ epigraph f.asEReal) :
    y ∈ effectiveDomain f ∧ (f y : EReal).toReal ≤ η := by
  -- Epigraph membership gives a finite upper bound on `f y`, hence both finiteness and the
  -- height comparison after applying `toReal`.
  have hfy_le : (f y : EReal) ≤ (η : EReal) := (mem_epigraph_iff _ _ _).mp hyη
  have hy_dom : y ∈ effectiveDomain f := by
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_lt hfy_le (EReal.coe_lt_top η)
  have hfy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hη_top : ((η : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top η
  have htoReal : (f y : EReal).toReal ≤ ((η : EReal)).toReal := by
    simpa using EReal.toReal_le_toReal hfy_le hfy_bot hη_top
  exact ⟨hy_dom, htoReal⟩

/-- Helper for Proposition 16.16: the product Hilbert inner product against `(u, -1)` separates
into the `H`-component minus the height difference. -/
private lemma inner_pair_sub_right_neg_one
    {x y u : H} {ξ η : ℝ} :
    ⟪(y, η) - (x, ξ), (u, (-1 : ℝ))⟫_ℝ = ⟪y - x, u⟫_ℝ - (η - ξ) := by
  -- Under the canonical `ℓ²` product structure, the horizontal and vertical parts decouple.
  simp [sub_eq_add_neg]

/-- Helper for Proposition 16.16: epigraph normal-cone membership at the real-height graph point
is equivalent to the translated pointwise inner-product inequalities against all epigraph
points. -/
private lemma mem_normalCone_epigraph_iff_forall_inner_pair_nonpos
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ effectiveDomain f) {u : H} {a : ℝ} :
    (u, a) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) ↔
      ∀ y η, (y, η) ∈ epigraph f.asEReal →
        ⟪(y, η) - (x, (f x : EReal).toReal), (u, a)⟫_ℝ ≤ 0 := by
  have hx_epi : (x, (f x : EReal).toReal) ∈ epigraph f.asEReal :=
    mem_epigraph_toReal_of_mem_effectiveDomain (f := f) hx
  -- Unfold the normal cone at a point of the epigraph and rewrite the translated support
  -- inequality pointwise.
  rw [Set.normalCone_of_mem hx_epi]
  have hnormal_iff :
      innerSupremumOn
          (epigraph f.asEReal - ({(x, (f x : EReal).toReal)} : Set (H × ℝ))) (u, a) ≤ 0 ↔
        ∀ z ∈ epigraph f.asEReal,
          ⟪z - (x, (f x : EReal).toReal), (u, a)⟫_ℝ ≤ 0 := by
    exact
      (innerSupremumOn_sub_singleton_le_zero_iff :
        innerSupremumOn
            (epigraph f.asEReal - ({(x, (f x : EReal).toReal)} : Set (H × ℝ))) (u, a) ≤ 0 ↔
          ∀ z ∈ epigraph f.asEReal,
            ⟪z - (x, (f x : EReal).toReal), (u, a)⟫_ℝ ≤ 0)
  constructor
  · intro hu
    have hpointwise := hnormal_iff.1 hu
    intro y η hyη
    exact hpointwise (y, η) hyη
  · intro hu
    have hpointwise :
        ∀ z ∈ epigraph f.asEReal,
          ⟪z - (x, (f x : EReal).toReal), (u, a)⟫_ℝ ≤ 0 := by
      intro z hz
      rcases z with ⟨y, η⟩
      exact hu y η hz
    exact hnormal_iff.2 hpointwise

/-- Helper for Proposition 16.16: at a point of the effective domain, subgradients are exactly
the normals of the real-height epigraph slice with vertical component `-1`. -/
private lemma mem_subdifferential_iff_mem_normalCone_epigraph_at_effectiveDomain_point
    (f : H → Set.Ioi (⊥ : EReal)) {x u : H} (hx : x ∈ effectiveDomain f) :
    u ∈ (∂ f) x ↔
      (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) := by
  constructor
  · intro hu
    rw [subdifferential_eq_iInter_affine_halfspaces f x hx, Set.mem_iInter₂] at hu
    -- Lift the canonical domain inequalities to arbitrary epigraph points by monotonicity in the
    -- height coordinate.
    refine (mem_normalCone_epigraph_iff_forall_inner_pair_nonpos (f := f) hx).2 ?_
    intro y η hyη
    rcases effectiveDomain_and_toReal_le_of_mem_epigraph (f := f) hyη with ⟨hy, hη⟩
    have hxy : ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal := hu y hy
    have hminor : ⟪y - x, u⟫_ℝ + (f x : EReal).toReal ≤ η := by
      linarith
    have hpair : ⟪y - x, u⟫_ℝ - (η - (f x : EReal).toReal) ≤ 0 := by
      linarith
    have hpair' :
        ⟪(y, η) - (x, (f x : EReal).toReal), (u, (-1 : ℝ))⟫_ℝ ≤ 0 := by
      rw [inner_pair_sub_right_neg_one]
      exact hpair
    exact hpair'
  · intro hu
    rw [subdifferential_eq_iInter_affine_halfspaces f x hx, Set.mem_iInter₂]
    intro y hy
    have hy_epi : (y, (f y : EReal).toReal) ∈ epigraph f.asEReal :=
      mem_epigraph_toReal_of_mem_effectiveDomain (f := f) hy
    have hineq :=
      (mem_normalCone_epigraph_iff_forall_inner_pair_nonpos (f := f) hx).1 hu
        y ((f y : EReal).toReal) hy_epi
    rw [inner_pair_sub_right_neg_one] at hineq
    change ⟪y - x, u⟫_ℝ ≤ (f y : EReal).toReal - (f x : EReal).toReal
    linarith

-- Proof sketch: the epigraph normal-cone computation gives `(i) ↔ (ii)`, and convexity of `f`
-- identifies that criterion with equality in the Fenchel--Young identity `(iii)`. The
-- proper-conjugate clause `(iv)` is the downstream bridge owned by Proposition 16.10, so it is
-- recorded separately below only in the source direction `(iii) → (iv)`.
/-- Proposition 16.16 (1): for an effective-domain point `x`, clauses `(i)`, `(ii)`, and `(iii)`
say that the following are equivalent: `u ∈ ∂ f x`, `(u, -1)` lies in the normal cone to the
real-height epigraph of `f` at `(x, (f x : EReal).toReal)`, and equality holds in the
Fenchel--Young identity `f(x) + f^*(u) = ⟪x, u⟫`. -/
theorem subdifferential_normalCone_fenchelYoung_tfae
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f)) (hdom : (effectiveDomain f).Nonempty)
    (x u : H) (hx : x ∈ effectiveDomain f) :
    List.TFAE
      [u ∈ (∂ f) x,
        (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal),
        (f x : EReal) + f.asEReal∗ u =
          ((⟪x, u⟫_ℝ : ℝ) : EReal)] := by
  let _ := hconv
  -- Clause `(i) ↔ (ii)` is the epigraph-normal characterization at the real-height graph point.
  tfae_have 1 ↔ 2 := by
    change u ∈ (∂ f) x ↔
      (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal)
    exact mem_subdifferential_iff_mem_normalCone_epigraph_at_effectiveDomain_point f hx
  -- Clause `(i) ↔ (iii)` is exactly Proposition 16.10.
  tfae_have 1 ↔ 3 := by
    change u ∈ (∂ f) x ↔
      (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal)
    exact mem_subdifferential_iff_fenchel_young_eq (f := f) hdom x u
  tfae_finish

/-- Proposition 16.16 (2): if `f` is convex and proper, then the Fenchel--Young equality
clause `(iii)` implies the conjugate subdifferential clause `x ∈ ∂ f*(u)`. On the implementation
surface this is stated for the packaged conjugate `properConjugateIoi f hdom`. -/
theorem mem_subdifferential_properConjugateIoi_of_fenchel_young_eq_of_convexOn
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f)) (hdom : (effectiveDomain f).Nonempty) (x u : H)
    (hfy : (f x : EReal) + f.asEReal∗ u =
      ((⟪x, u⟫_ℝ : ℝ) : EReal)) :
    x ∈ (∂ (properConjugateIoi f hdom)) u := by
  let _ := hconv
  -- First convert the contact equality into primal subgradient membership.
  have hsub : u ∈ (∂ f) x :=
    (mem_subdifferential_iff_fenchel_young_eq (f := f) hdom x u).2 hfy
  -- Then Proposition 16.10 transports that subgradient to the packaged conjugate.
  exact mem_subdifferential_properConjugateIoi_of_mem_subdifferential (f := f) hdom x u hsub

/-- Companion to Proposition 16.16: for a proper convex function and an effective-domain point
`x`, the subdifferential criterion is equivalent to the epigraph normal-cone criterion at the
real-height point `(x, (f x : EReal).toReal)`, which is the textbook point `(x, f(x))`. -/
theorem mem_subdifferential_iff_mem_normalCone_epigraph
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f)) (hdom : (effectiveDomain f).Nonempty)
    {x u : H} (hx : x ∈ effectiveDomain f) :
    u ∈ (∂ f) x ↔
      (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) := by
  let _ := hconv
  let _ := hdom
  -- This is exactly the geometric core lemma specialized to the effective-domain point `x`.
  exact mem_subdifferential_iff_mem_normalCone_epigraph_at_effectiveDomain_point f hx

end SubdifferentialAndEpigraphNormalCone

end ERealFunction


/-! Source item: Bauschke-lean-project/BauschkeLean/Chap16/Theorem_16_29.lean -/

open scoped InnerProductSpace Pointwise Set

namespace ERealFunction

noncomputable section

section SubdifferentialConjugation

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

attribute [local instance] prod_seminormedAddCommGroup_l2_real
attribute [local instance] prod_normedAddCommGroup_l2_real
attribute [local instance] prod_normedSpace_l2_real
attribute [local instance] prod_innerProductSpace_l2_real

-- Proof sketch: Proposition 16.16 gives the equivalence of clauses `(i)`, `(ii)`, and `(iii)`.
-- Corollary 16.30 identifies clause `(iv)` with clause `(i)` by rewriting `(∂ f)⁻¹` as the
-- subdifferential of the canonical packaged conjugate `gammaZeroConjugate f hf`.
/-- Theorem 16.29: for `f ∈ Γ₀(H)`, membership of `(x, u)` in the graph of `∂ f`,
membership of `(u, -1)` in the normal cone to `epi f` at `(x, f x)`, equality in the
Fenchel--Young identity, and membership of `(u, x)` in the graph of `∂ f^*` are equivalent.
In Lean, clauses (i) and (iv) are written as the corresponding subdifferential-membership
statements, and clause (ii) uses the real-height epigraph point
`(x, (f x : EReal).toReal)`. -/
theorem subdifferential_normalCone_fenchelYoung_conjugate_tfae
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (x u : H) :
    List.TFAE
      [u ∈ (∂ f) x,
        (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal),
        (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal),
        x ∈ (∂ (gammaZeroConjugate f hf)) u] := by
  have hinv := inverse_subdifferential_eq_subdifferential_gammaZeroConjugate f hf
  have h14 :
      u ∈ (∂ f) x ↔ x ∈ (∂ (gammaZeroConjugate f hf)) u := by
    rw [← hinv]
    exact (SetValuedOperator.mem_inverse_iff (∂ f.asEReal) u x).symm
  by_cases hx : x ∈ effectiveDomain f
  · have htfae :=
      subdifferential_normalCone_fenchelYoung_tfae
        f (hf.2 : ConvexOn f (effectiveDomain f)) hf.2.nonempty x u hx
    have h12 :
        u ∈ (∂ f) x ↔
          (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) := by
      simpa using (List.TFAE.out htfae 0 1)
    have h13 :
        u ∈ (∂ f) x ↔
          (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal) := by
      simpa using (List.TFAE.out htfae 0 2)
    tfae_have 1 ↔ 2 := by
      change u ∈ (∂ f) x ↔
        (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal)
      exact h12
    tfae_have 1 ↔ 3 := by
      change u ∈ (∂ f) x ↔
        (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal)
      exact h13
    tfae_have 1 ↔ 4 := by
      change u ∈ (∂ f) x ↔ x ∈ (∂ (gammaZeroConjugate f hf)) u
      exact h14
    tfae_finish
  · have hx_top : (f x : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
    have hx_not_epi : (x, (f x : EReal).toReal) ∉ epigraph f.asEReal := by
      intro hx_epi
      have hfx_lt_top : (f x : EReal) < ⊤ := by
        exact lt_of_le_of_lt ((mem_epigraph_iff f.asEReal x _).1 hx_epi) (EReal.coe_lt_top _)
      exact hx (mem_effectiveDomain_iff.2 hfx_lt_top)
    have h1false : ¬ u ∈ (∂ f) x := by
      intro hu
      have hx_subdom : x ∈ SetValuedOperator.dom (∂ f) := by
        rw [SetValuedOperator.mem_dom_iff]
        exact ⟨u, hu⟩
      exact hx (subdifferential_domain_subset_effectiveDomain f hf.2.nonempty hx_subdom)
    have h2false :
        ¬ (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal) := by
      simp [Set.normalCone_of_not_mem hx_not_epi]
    have h3false :
        ¬ ((f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal)) := by
      have hconj_ne_bot : f.asEReal∗ u ≠ ⊥ :=
        conjugate_ne_bot_of_effectiveDomain_nonempty hf.2.nonempty u
      rw [hx_top, EReal.top_add_of_ne_bot hconj_ne_bot]
      simp
    tfae_have 1 ↔ 2 := by
      change u ∈ (∂ f) x ↔
        (u, (-1 : ℝ)) ∈ N[epigraph f.asEReal] (x, (f x : EReal).toReal)
      constructor
      · intro hu
        exact False.elim (h1false hu)
      · intro hu
        exact False.elim (h2false hu)
    tfae_have 1 ↔ 3 := by
      change u ∈ (∂ f) x ↔
        (f x : EReal) + f.asEReal∗ u = ((⟪x, u⟫_ℝ : ℝ) : EReal)
      constructor
      · intro hu
        exact False.elim (h1false hu)
      · intro hu
        exact False.elim (h3false hu)
    tfae_have 1 ↔ 4 := by
      change u ∈ (∂ f) x ↔ x ∈ (∂ (gammaZeroConjugate f hf)) u
      exact h14
    tfae_finish

end SubdifferentialConjugation

end

end ERealFunction


/-! Source item: Bauschke-lean-project/BauschkeLean/Chap16/Theorem_16_58.lean -/

open scoped InnerProductSpace Pointwise

namespace ERealFunction

section SubdifferentialCalculus

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: translating the base point of a convex function does not change the
subgradient vector; it only shifts the evaluation point. -/
lemma mem_subdifferential_translate_iff
    {f : H → Set.Ioi (⊥ : EReal)} {x0 z u : H} :
    u ∈ (∂ fun w : H ↦ f (x0 + w)) z ↔ u ∈ (∂ f) (x0 + z) := by
  rw [mem_subdifferential_iff, mem_subdifferential_iff]
  constructor
  · intro hu y
    have hshift : y - x0 - z = y - (x0 + z) := by
      abel
    simpa [hshift] using hu (y - x0)
  · intro hu y
    have hshift : x0 + y - (x0 + z) = y - z := by
      abel
    simpa [hshift] using hu (x0 + y)

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: translating a `Γ₀(H)` function by a base point preserves
membership in `Γ₀(H)`. -/
lemma translate_mem_gammaZero
    {f : H → Set.Ioi (⊥ : EReal)} (hf : f ∈ Γ₀(H)) (x0 : H) :
    (fun z : H ↦ f (x0 + z)) ∈ Γ₀(H) := by
  rw [mem_gammaZero_iff] at hf ⊢
  constructor
  · simpa using hf.1.comp (continuous_const.add continuous_id)
  · refine ⟨?_, subset_rfl, ?_⟩
    · rcases hf.2.nonempty with ⟨x, hx⟩
      refine ⟨x - x0, ?_⟩
      change (f (x0 + (x - x0)) : EReal) < ⊤
      simpa using hx
    · intro x hx y hy a ha0 ha1
      have hexpand :
          a • x0 + a • x + ((1 - a) • x0 + (1 - a) • y) =
            x0 + (a • x + (1 - a) • y) := by
        calc
          a • x0 + a • x + ((1 - a) • x0 + (1 - a) • y)
              = (a • x0 + (1 - a) • x0) + (a • x + (1 - a) • y) := by
                abel
          _ = ((a + (1 - a)) • x0) + (a • x + (1 - a) • y) := by
                rw [← add_smul]
          _ = x0 + (a • x + (1 - a) • y) := by
                simp
      simpa [smul_add, hexpand] using
        hf.2.ineq (x := x0 + x) hx (y := x0 + y) hy ha0 ha1

/-- Helper for Theorem 16 58: affine tilting adds the linear perturbation `x ↦ -⟪x, u⟫` to an
`EReal`-valued function. -/
noncomputable def affineTiltEReal (φ : H → EReal) (u : H) : H → EReal :=
  fun x ↦ φ x + (((-⟪x, u⟫_ℝ : ℝ) : EReal))

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: evaluating the affine tilt exposes the added linear term. -/
@[simp] theorem affineTiltEReal_apply
    (φ : H → EReal) (u x : H) :
    affineTiltEReal φ u x = φ x + (((-⟪x, u⟫_ℝ : ℝ) : EReal)) :=
  rfl

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: affine tilting a `Γ₀(H)` function preserves properness. -/
theorem affine_tilt_isProper
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    IsProper (affineTiltEReal f.asEReal u) := by
  have htilt_eq_coe :
      ∀ ⦃x : H⦄, x ∈ effectiveDomain f →
        affineTiltEReal f.asEReal u x =
          (((f.asEReal x).toReal - ⟪x, u⟫_ℝ : ℝ) : EReal) := by
    intro x hx
    have hx_top : f.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : f.asEReal x ≠ ⊥ := ne_of_gt (f x).2
    rw [affineTiltEReal, ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
    simp [sub_eq_add_neg]
  constructor
  · intro x
    by_cases hx : x ∈ effectiveDomain f
    · rw [htilt_eq_coe hx]
      exact EReal.coe_ne_bot _
    · have hx_top : f.asEReal x = ⊤ := by
        exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
      rw [affineTiltEReal, hx_top, EReal.top_add_of_ne_bot (EReal.coe_ne_bot (-⟪x, u⟫_ℝ))]
      simp
  · rcases hf.2.nonempty with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [mem_dom_iff, htilt_eq_coe hx]
    simpa using (EReal.coe_lt_top (((f.asEReal x).toReal - ⟪x, u⟫_ℝ : ℝ)))

/-- Helper for Theorem 16 58: package the affine tilt back into the `]-∞,+∞]` codomain expected
by the convex-analysis API. -/
noncomputable abbrev affineTiltIoi
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    H → Set.Ioi (⊥ : EReal) :=
  properIoi (affineTiltEReal f.asEReal u) (affine_tilt_isProper f hf u)

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: coercing the packaged affine tilt back to `EReal` recovers the raw
tilted function. -/
@[simp] theorem affineTiltIoi_apply
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u x : H) :
    (affineTiltIoi f hf u x : EReal) = affineTiltEReal f.asEReal u x := by
  rfl

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: the affine tilt of a `Γ₀(H)` function again belongs to `Γ₀(H)`. -/
theorem affine_tilt_mem_gammaZero
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    affineTiltIoi f hf u ∈ Γ₀(H) := by
  have hlinear_gamma :
      (fun x : H ↦ (((-⟪x, u⟫_ℝ : ℝ) : EReal))) ∈ Γ(H) := by
    rw [mem_gamma_iff]
    refine ⟨?_, ?_⟩
    · intro x y a ha0 ha1
      change (((-(⟪a • x + (1 - a) • y, u⟫_ℝ) : ℝ) : EReal)) ≤
        (a : EReal) * (((-⟪x, u⟫_ℝ : ℝ) : EReal)) +
          (1 - a : EReal) * (((-⟪y, u⟫_ℝ : ℝ) : EReal))
      have hreal :
          -(⟪a • x + (1 - a) • y, u⟫_ℝ) =
            a * (-⟪x, u⟫_ℝ) + (1 - a) * (-⟪y, u⟫_ℝ) := by
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
        ring
      have hsub : (1 - (a : EReal)) = (((1 - a : ℝ)) : EReal) := by
        norm_num
      rw [hreal, hsub, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    · simpa using
        (continuous_coe_real_ereal.comp
          ((continuous_id.inner continuous_const).neg)).lowerSemicontinuous
  have htilt_gamma : affineTiltEReal f.asEReal u ∈ Γ(H) := by
    have hf_gamma : f.asEReal ∈ Γ(H) := asEReal_mem_gamma_of_mem_gammaZero hf
    rw [mem_gamma_iff] at hf_gamma hlinear_gamma ⊢
    refine ⟨?_, ?_⟩
    · intro x y a ha0 ha1
      have haE_nonneg : (0 : EReal) ≤ (a : EReal) := by
        exact_mod_cast ha0
      have hbE_nonneg : (0 : EReal) ≤ (1 - a : EReal) := by
        exact_mod_cast sub_nonneg.mpr ha1
      have haE_ne_top : (a : EReal) ≠ ⊤ := EReal.coe_ne_top a
      have hbE_ne_top : (1 - a : EReal) ≠ ⊤ := EReal.coe_ne_top (1 - a)
      calc
        affineTiltEReal f.asEReal u (a • x + (1 - a) • y)
            ≤ ((a : EReal) * f.asEReal x + (1 - a : EReal) * f.asEReal y) +
                ((a : EReal) * (((-⟪x, u⟫_ℝ : ℝ) : EReal)) +
                  (1 - a : EReal) * (((-⟪y, u⟫_ℝ : ℝ) : EReal))) := by
              simpa [affineTiltEReal] using
                add_le_add (hf_gamma.1 ha0 ha1) (hlinear_gamma.1 ha0 ha1)
        _ = (a : EReal) * affineTiltEReal f.asEReal u x +
              (1 - a : EReal) * affineTiltEReal f.asEReal u y := by
              simp [affineTiltEReal,
                EReal.left_distrib_of_nonneg_of_ne_top haE_nonneg haE_ne_top,
                EReal.left_distrib_of_nonneg_of_ne_top hbE_nonneg hbE_ne_top,
                add_assoc, add_left_comm]
    · rw [lowerSemicontinuous_iff_le_liminf]
      intro x
      calc
        affineTiltEReal f.asEReal u x
            ≤ Filter.liminf f.asEReal (nhds x) +
                Filter.liminf (fun y : H ↦ (((-⟪y, u⟫_ℝ : ℝ) : EReal))) (nhds x) := by
              simpa [affineTiltEReal] using
                add_le_add (hf_gamma.2.le_liminf x) (hlinear_gamma.2.le_liminf x)
        _ ≤ Filter.liminf (affineTiltEReal f.asEReal u) (nhds x) := by
              simpa [affineTiltEReal] using
                (EReal.le_liminf_add :
                  Filter.liminf f.asEReal (nhds x) +
                      Filter.liminf
                        (fun y : H ↦ (((-⟪y, u⟫_ℝ : ℝ) : EReal)))
                        (nhds x) ≤
                    Filter.liminf
                      (fun y : H ↦
                        f.asEReal y + (((-⟪y, u⟫_ℝ : ℝ) : EReal)))
                      (nhds x))
  exact properIoi_mem_gammaZero_of_mem_gamma (affine_tilt_isProper f hf u) htilt_gamma

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: affine tilting does not change the effective domain. -/
theorem effectiveDomain_affineTiltIoi
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (u : H) :
    effectiveDomain (affineTiltIoi f hf u) = effectiveDomain f := by
  ext x
  by_cases hx : x ∈ effectiveDomain f
  · have hx_top : f.asEReal x ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : f.asEReal x ≠ ⊥ := ne_of_gt (f x).2
    rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff]
    have hvalue :
        affineTiltEReal f.asEReal u x =
          (((f.asEReal x).toReal - ⟪x, u⟫_ℝ : ℝ) : EReal) := by
      rw [affineTiltEReal, ← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_add]
      simp [sub_eq_add_neg]
    rw [affineTiltIoi_apply, hvalue]
    constructor
    · intro _
      exact mem_effectiveDomain_iff.mp hx
    · intro _
      exact EReal.coe_lt_top _
  · rw [mem_effectiveDomain_iff, mem_effectiveDomain_iff]
    have hx_top : f.asEReal x = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
    rw [affineTiltIoi_apply, affineTiltEReal, hx_top,
      EReal.top_add_of_ne_bot (EReal.coe_ne_bot (-⟪x, u⟫_ℝ))]
    simp [hx_top]

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: the `]-∞,+∞]`-valued norm function belongs to `Γ₀(H)`. -/
lemma norm_toEReal_mem_gammaZero :
    ((norm : H → ℝ).toEReal) ∈ Γ₀(H) := by
  refine toEReal_mem_gammaZero_of_mem_gamma ?_
  rw [mem_gamma_iff]
  constructor
  · intro x y a ha hb
    have hnorm :
        ‖a • x + (1 - a) • y‖ ≤ a * ‖x‖ + (1 - a) * ‖y‖ := by
      simpa [smul_eq_mul] using
        (convexOn_univ_norm.2 (by simp) (by simp) ha (sub_nonneg.mpr hb) (by ring) :
          ‖a • x + (1 - a) • y‖ ≤ a • ‖x‖ + (1 - a) • ‖y‖)
    change ((‖a • x + (1 - a) • y‖ : ℝ) : EReal) ≤
      (((a * ‖x‖ + (1 - a) * ‖y‖ : ℝ)) : EReal)
    rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
    exact_mod_cast hnorm
  · simpa using (continuous_coe_real_ereal.comp continuous_norm).lowerSemicontinuous

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: evaluating a conjugate at the origin rewrites it as the negative
infimum of the range. -/
lemma conjugate_zero_eq_neg_sInf_range_local (φ : H → EReal) :
    φ∗ 0 = -sInf (Set.range φ) := by
  calc
    φ∗ 0 = ⨆ x : H, -φ x := by
      simp [conjugate_apply]
    _ = -(⨅ x : H, φ x) := by
      exact (OrderIso.map_iInf EReal.negOrderIso (fun x : H ↦ φ x)).symm
    _ = -sInf (Set.range φ) := by
      rw [sInf_range]

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: subgradients of the affine tilt are shifted by the tilting vector. -/
lemma mem_subdifferential_affineTiltIoi_iff
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (v z u : H) :
    u ∈ (∂ affineTiltIoi f hf v) z ↔ u + v ∈ (∂ f) z := by
  rw [mem_subdifferential_iff, mem_subdifferential_iff]
  constructor
  · intro hu y
    have huy := hu y
    have hadded := add_le_add_right huy (((⟪y, v⟫_ℝ : ℝ) : EReal))
    have hleft :
        (((⟪y, v⟫_ℝ : ℝ) : EReal) +
            ((⟪y - z, u⟫_ℝ : EReal) + affineTiltEReal f.asEReal v z)) =
          (⟪y - z, u + v⟫_ℝ : EReal) + (f z : EReal) := by
      have hreal : ⟪y, v⟫_ℝ + -⟪z, v⟫_ℝ = ⟪y - z, v⟫_ℝ := by
        simpa [sub_eq_add_neg] using (inner_sub_left y z v).symm
      calc
        (((⟪y, v⟫_ℝ : ℝ) : EReal) +
            ((⟪y - z, u⟫_ℝ : EReal) + affineTiltEReal f.asEReal v z))
            = (f z : EReal) +
                (((⟪y, v⟫_ℝ + (-⟪z, v⟫_ℝ) + ⟪y - z, u⟫_ℝ : ℝ) : EReal)) := by
                  rw [affineTiltEReal, EReal.coe_add, EReal.coe_add]
                  simp [add_assoc, add_left_comm, add_comm]
        _ = (f z : EReal) + (((⟪y - z, v⟫_ℝ + ⟪y - z, u⟫_ℝ : ℝ) : EReal)) := by
              rw [hreal]
        _ = (⟪y - z, u + v⟫_ℝ : EReal) + (f z : EReal) := by
              rw [inner_add_right, EReal.coe_add]
              simp [add_comm]
    have hright :
        (((⟪y, v⟫_ℝ : ℝ) : EReal) + affineTiltEReal f.asEReal v y) = (f y : EReal) := by
      calc
        (((⟪y, v⟫_ℝ : ℝ) : EReal) + affineTiltEReal f.asEReal v y)
            = (f y : EReal) +
                (((⟪y, v⟫_ℝ + -⟪y, v⟫_ℝ : ℝ) : EReal)) := by
                  rw [affineTiltEReal, EReal.coe_add]
                  simp [add_left_comm]
        _ = (f y : EReal) := by
              simp
    have hplain : (⟪y - z, u + v⟫_ℝ : EReal) + (f z : EReal) ≤ (f y : EReal) := by
      rw [← hleft, ← hright]
      simpa [affineTiltIoi_apply] using hadded
    exact hplain
  · intro hu y
    have huy := hu y
    have hadded := add_le_add_right huy (((-⟪y, v⟫_ℝ : ℝ) : EReal))
    have hleft :
        (((-⟪y, v⟫_ℝ : ℝ) : EReal) + ((⟪y - z, u + v⟫_ℝ : EReal) + (f z : EReal))) =
          (⟪y - z, u⟫_ℝ : EReal) + affineTiltEReal f.asEReal v z := by
      have hreal : -⟪y, v⟫_ℝ + ⟪y - z, v⟫_ℝ = -⟪z, v⟫_ℝ := by
        rw [inner_sub_left]
        ring
      have hreal' :
          -⟪y, v⟫_ℝ + (⟪y - z, v⟫_ℝ + ⟪y - z, u⟫_ℝ) =
            -⟪z, v⟫_ℝ + ⟪y - z, u⟫_ℝ := by
        rw [← add_assoc, hreal]
      calc
        (((-⟪y, v⟫_ℝ : ℝ) : EReal) + ((⟪y - z, u + v⟫_ℝ : EReal) + (f z : EReal)))
            = (f z : EReal) +
                (((-⟪y, v⟫_ℝ + (⟪y - z, v⟫_ℝ + ⟪y - z, u⟫_ℝ) : ℝ) : EReal)) := by
                  rw [inner_add_right, EReal.coe_add, EReal.coe_add]
                  simp [add_left_comm, add_comm]
        _ = (f z : EReal) + (((-⟪z, v⟫_ℝ + ⟪y - z, u⟫_ℝ : ℝ) : EReal)) := by
              rw [hreal']
        _ = (⟪y - z, u⟫_ℝ : EReal) + affineTiltEReal f.asEReal v z := by
              rw [affineTiltEReal, EReal.coe_add]
              simp [sub_eq_add_neg, add_assoc, add_comm]
    have hright :
        (((-⟪y, v⟫_ℝ : ℝ) : EReal) + (f y : EReal)) = affineTiltEReal f.asEReal v y := by
      simp [affineTiltEReal, add_comm]
    have htilted :
        (⟪y - z, u⟫_ℝ : EReal) + affineTiltEReal f.asEReal v z ≤ affineTiltEReal f.asEReal v y := by
      rw [← hleft, ← hright]
      exact hadded
    simpa [affineTiltIoi_apply] using htilted

omit [CompleteSpace H] in
/-- Helper for Theorem 16 58: the penalty subgradient at the base point of a translated norm has
norm bounded by the scaling factor. -/
lemma norm_le_of_mem_subdifferential_posReal_smul_norm_translate
    (γ : PosReal) (z q : H)
    (hq : q ∈ (∂ fun x : H ↦ (γ • ((norm : H → ℝ).toEReal)) (-z + x)) z) :
    ‖q‖ ≤ (γ : ℝ) := by
  have hq0 :
      q ∈ (∂ ((γ • ((norm : H → ℝ).toEReal) : H → Set.Ioi (⊥ : EReal)))) (0 : H) := by
    simpa using
      (mem_subdifferential_translate_iff
        (f := (γ • ((norm : H → ℝ).toEReal) : H → Set.Ioi (⊥ : EReal)))
        (x0 := -z) (z := z) (u := q)).1 hq
  rw [subdifferential_posReal_smul_eq_smul ((norm : H → ℝ).toEReal) γ] at hq0
  change q ∈ (γ : ℝ) • ((∂ ((norm : H → ℝ).toEReal)) (0 : H)) at hq0
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hq0
  have hnorm_subdifferential :
      (∂ ((norm : H → ℝ).toEReal)) (0 : H) = Metric.closedBall (0 : H) 1 := by
    simpa using subdifferential_norm_eq_singleton_or_closedBall (H := H) (0 : H)
  have hunit :
      (γ : ℝ)⁻¹ • q ∈ Metric.closedBall (0 : H) 1 := by
    simpa [hnorm_subdifferential] using hq0
  have hunit_norm : ‖(γ : ℝ)⁻¹ • q‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hunit
  have hq_scaled :
      ‖(γ : ℝ)⁻¹ • q‖ = (γ : ℝ)⁻¹ * ‖q‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr γ.2.le)]
  have hscaled_le : (γ : ℝ)⁻¹ * ‖q‖ ≤ 1 := by
    simpa [hq_scaled] using hunit_norm
  have hmul_le := mul_le_mul_of_nonneg_left hscaled_le γ.2.le
  simpa [γ.2.ne', hq_scaled, mul_assoc, mul_left_comm, mul_comm] using hmul_le

/- Source/core/bridge triage:
- `source-facing`: Theorem 16.58 is the Brøndsted--Rockafellar approximation statement.
- `core/canonical`: the owner abstractions are the subdifferential `∂ f` and the packaged
  `Γ₀(H)` Fenchel conjugate `f∗[hf]`.
- `bridge/view`: graph language for `∂ f` is derived from the primitive data `z`, `w`, and
  `w ∈ (∂ f) z`, so the public surface keeps the latter and avoids pair-projection bookkeeping.
-/

-- Proof sketch: apply Ekeland's variational principle to the shifted function
-- `x ↦ (f x : EReal) - ⟪x, v⟫`. The gap hypothesis makes `y` an approximate minimizer with error
-- `λ * μ`. Ekeland yields `z` with `‖z - y‖ ≤ λ` such that `z` minimizes the perturbation by
-- `μ ‖· - z‖`. Fermat's rule puts `0` in the subdifferential of that perturbation at `z`, the
-- sum rule splits the subdifferential, and the norm subdifferential formula produces
-- `w ∈ (∂ f) z` with `‖w - v‖ ≤ μ`.
/-- Theorem 16 58: the Brondsted--Rockafellar approximation theorem. For `f ∈ Γ₀(H)`, if the
Fenchel--Young gap at `(y, v)` is at most `λμ`, then there exist `z` and `w ∈ (∂ f) z` with
`z` within distance `λ` of `y` and `w` within distance `μ` of `v`. -/
theorem exists_subgradient_point_close_of_fenchelYoung_gap_le
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ Γ₀(H)) (y v : H) (lam μ : NNReal)
    (hgap :
      (f y : EReal) + (f∗[hf] v : EReal) ≤
        ((⟪y, v⟫_ℝ + ((lam * μ : NNReal) : ℝ) : ℝ) : EReal)) :
    ∃ z w, w ∈ (∂ f) z ∧ ‖z - y‖ ≤ (lam : ℝ) ∧ ‖w - v‖ ≤ (μ : ℝ) := by
  have hexact_case :
      lam = 0 ∨ μ = 0 →
        ∃ z w, w ∈ (∂ f) z ∧ ‖z - y‖ ≤ (lam : ℝ) ∧ ‖w - v‖ ≤ (μ : ℝ) := by
    intro hzero
    have hgap_exact :
        (f y : EReal) + (f∗[hf] v : EReal) ≤ ((⟪y, v⟫_ℝ : ℝ) : EReal) := by
      rcases hzero with hlam | hμ
      · simpa [hlam] using hgap
      · simpa [hμ] using hgap
    have hfy :
        ((⟪y, v⟫_ℝ : ℝ) : EReal) ≤ (f y : EReal) + (f∗[hf] v : EReal) := by
      simpa [gammaZeroConjugate_apply] using
        fenchel_young_inequality (f := f.asEReal) (isProper_of_mem_gammaZero hf) y v
    have hfy_eq :
        (f y : EReal) + (f∗[hf] v : EReal) = ((⟪y, v⟫_ℝ : ℝ) : EReal) :=
      le_antisymm hgap_exact hfy
    have hv : v ∈ (∂ f) y := by
      exact (mem_subdifferential_iff_fenchel_young_eq (f := f) hf.2.nonempty y v).2 hfy_eq
    rcases hzero with hlam | hμ
    · refine ⟨y, v, hv, ?_, ?_⟩
      · simp [hlam]
      · simp
    · refine ⟨y, v, hv, ?_, ?_⟩
      · simp
      · simp [hμ]
  by_cases hlam : lam = 0
  · exact hexact_case (Or.inl hlam)
  by_cases hμ : μ = 0
  · exact hexact_case (Or.inr hμ)
  let ψ : H → Set.Ioi (⊥ : EReal) := affineTiltIoi f hf v
  have hψ : ψ ∈ Γ₀(H) := by
    simpa [ψ] using affine_tilt_mem_gammaZero (f := f) (hf := hf) v
  have hy_dom_f : y ∈ effectiveDomain f := by
    by_contra hy_dom_f
    have hy_top : (f y : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hy_dom_f))
    have hlhs_top : (f y : EReal) + (f∗[hf] v : EReal) = ⊤ := by
      rw [hy_top, EReal.top_add_of_ne_bot (ne_of_gt (f∗[hf] v).2)]
    have hrhs_ne_top :
        (((⟪y, v⟫_ℝ + ((lam * μ : NNReal) : ℝ) : ℝ) : EReal)) ≠ ⊤ := EReal.coe_ne_top _
    exact hrhs_ne_top (le_antisymm le_top (hlhs_top ▸ hgap))
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy_dom_f)
  have hy_bot : (f y : EReal) ≠ ⊥ := ne_of_gt (f y).2
  have hvconj_top : (f∗[hf] v : EReal) ≠ ⊤ := by
    intro hvconj_top
    have hlhs_top : (f y : EReal) + (f∗[hf] v : EReal) = ⊤ := by
      rw [hvconj_top, EReal.add_top_of_ne_bot hy_bot]
    have hrhs_ne_top :
        (((⟪y, v⟫_ℝ + ((lam * μ : NNReal) : ℝ) : ℝ) : EReal)) ≠ ⊤ := EReal.coe_ne_top _
    exact hrhs_ne_top (le_antisymm le_top (hlhs_top ▸ hgap))
  have hvconj_bot : (f∗[hf] v : EReal) ≠ ⊥ := ne_of_gt (f∗[hf] v).2
  have hconj_val :
      (f∗[hf] v : EReal) = ((((f∗[hf] v : EReal).toReal : ℝ) : EReal)) :=
    (EReal.coe_toReal hvconj_top hvconj_bot).symm
  have hψy_eq :
      (ψ y : EReal) = (((f y : EReal).toReal - ⟪y, v⟫_ℝ : ℝ) : EReal) := by
    change (f y : EReal) + (((-⟪y, v⟫_ℝ : ℝ) : EReal)) =
      (((f y : EReal).toReal - ⟪y, v⟫_ℝ : ℝ) : EReal)
    rw [← EReal.coe_toReal hy_top hy_bot, ← EReal.coe_add]
    simp [sub_eq_add_neg]
  have hψy_top : (ψ y : EReal) ≠ ⊤ := by
    rw [hψy_eq]
    exact EReal.coe_ne_top _
  have hψy_bot : (ψ y : EReal) ≠ ⊥ := by
    rw [hψy_eq]
    exact EReal.coe_ne_bot _
  have hgap_real :
      (f y : EReal).toReal + (f∗[hf] v : EReal).toReal ≤
        ⟪y, v⟫_ℝ + (lam : ℝ) * (μ : ℝ) := by
    have hcast :
        ((((f y : EReal).toReal + (f∗[hf] v : EReal).toReal : ℝ) : EReal)) ≤
          (((⟪y, v⟫_ℝ + (lam : ℝ) * (μ : ℝ) : ℝ) : EReal)) := by
      calc
        ((((f y : EReal).toReal + (f∗[hf] v : EReal).toReal : ℝ) : EReal))
            = ((((f y : EReal).toReal : ℝ) : EReal)) +
                ((((f∗[hf] v : EReal).toReal : ℝ) : EReal)) := by
                  rw [EReal.coe_add]
        _ = (f y : EReal) + (f∗[hf] v : EReal) := by
              rw [EReal.coe_toReal hy_top hy_bot, EReal.coe_toReal hvconj_top hvconj_bot]
        _ ≤ (((⟪y, v⟫_ℝ + (lam : ℝ) * (μ : ℝ) : ℝ) : EReal)) := by
              simpa [NNReal.coe_mul] using hgap
    exact EReal.coe_le_coe_iff.mp hcast
  have hψy_toReal :
      (ψ y : EReal).toReal = (f y : EReal).toReal - ⟪y, v⟫_ℝ := by
    rw [hψy_eq]
    exact EReal.toReal_coe _
  have hψgap_real :
      (ψ y : EReal).toReal + (f∗[hf] v : EReal).toReal ≤ (lam : ℝ) * (μ : ℝ) := by
    rw [hψy_toReal]
    nlinarith
  have hlam_pos : 0 < (lam : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hlam)
  have hμ_pos : 0 < (μ : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hμ)
  let γ : PosReal := ⟨(lam : ℝ) / (μ : ℝ), by positivity⟩
  let z : H := Prox[γ, ψ, hψ] y
  have hprox : IsProxPoint (γ • ψ) y z := by
    simpa [z, scaledProximityOperator] using
      proximityOperator_isProxPoint
        (γ • ψ)
        (hasUniqueProxPoint_of_mem_gammaZero (f := γ • ψ) (smul_mem_gammaZero ψ hψ γ))
        y
  have hprox_var :
      ∀ x, (⟪x - z, y - z⟫_ℝ : EReal) + (((γ • ψ) z : Set.Ioi (⊥ : EReal)) : EReal) ≤
        (((γ • ψ) x : Set.Ioi (⊥ : EReal)) : EReal) :=
    (isProxPoint_iff_forall_inner_add_le (γ • ψ) (smul_mem_gammaZero ψ hψ γ).2 y z).1 hprox
  have hz_dom_psi : z ∈ effectiveDomain ψ := by
    rcases hψ.2.nonempty with ⟨q, hq⟩
    by_contra hz_dom_psi
    have hz_top' : (ψ z : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hz_dom_psi))
    have hscaled_top : ((γ • ψ) z : EReal) = ⊤ := by
      rw [posReal_smul_apply, hz_top']
      simpa using (EReal.coe_mul_top_of_pos γ.2 : ((γ : ℝ) : EReal) * ⊤ = ⊤)
    have hq_scaled_ne_top : ((γ • ψ) q : EReal) ≠ ⊤ := by
      rw [posReal_smul_apply, EReal.mul_ne_top]
      exact
        ⟨Or.inl (EReal.coe_ne_bot (γ : ℝ)), Or.inl (EReal.coe_nonneg.mpr γ.2.le),
          Or.inl (EReal.coe_ne_top (γ : ℝ)),
          Or.inr (ne_of_lt (mem_effectiveDomain_iff.mp hq))⟩
    have hsum_top : (⟪q - z, y - z⟫_ℝ : EReal) + ((γ • ψ) z : EReal) = ⊤ := by
      rw [hscaled_top, EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
    have hvar_q := hprox_var q
    rw [hsum_top] at hvar_q
    exact hq_scaled_ne_top (top_le_iff.mp hvar_q)
  have hz_top : (ψ z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_dom_psi)
  have hz_bot : (ψ z : EReal) ≠ ⊥ := ne_of_gt (ψ z).2
  have hz_dom_f : z ∈ effectiveDomain f := by
    rw [← effectiveDomain_affineTiltIoi (f := f) (hf := hf) v]
    exact hz_dom_psi
  have hzf_top : (f z : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hz_dom_f)
  have hzf_bot : (f z : EReal) ≠ ⊥ := ne_of_gt (f z).2
  have hψz_eq :
      (ψ z : EReal) = (((f z : EReal).toReal - ⟪z, v⟫_ℝ : ℝ) : EReal) := by
    change (f z : EReal) + (((-⟪z, v⟫_ℝ : ℝ) : EReal)) =
      (((f z : EReal).toReal - ⟪z, v⟫_ℝ : ℝ) : EReal)
    rw [← EReal.coe_toReal hzf_top hzf_bot, ← EReal.coe_add]
    simp [sub_eq_add_neg]
  have hψz_toReal :
      (ψ z : EReal).toReal = (f z : EReal).toReal - ⟪z, v⟫_ℝ := by
    rw [hψz_eq]
    exact EReal.toReal_coe _
  -- The proximal-point variational inequality is exactly subgradient membership for `γ • ψ`.
  have hscaled_subgrad : y - z ∈ (∂ (γ • ψ)) z := by
    rw [mem_subdifferential_iff]
    exact hprox_var
  rw [subdifferential_posReal_smul_eq_smul ψ γ] at hscaled_subgrad
  change y - z ∈ (γ : ℝ) • ((∂ ψ) z) at hscaled_subgrad
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ γ.2.ne'] at hscaled_subgrad
  let u : H := (γ : ℝ)⁻¹ • (y - z)
  have hu : u ∈ (∂ ψ) z := by
    simpa [u] using hscaled_subgrad
  have hfy_z_real :
      ⟪z, v⟫_ℝ ≤ (f z : EReal).toReal + (f∗[hf] v : EReal).toReal := by
    have hcast :
        (((⟪z, v⟫_ℝ : ℝ) : EReal)) ≤
          ((((f z : EReal).toReal + (f∗[hf] v : EReal).toReal : ℝ) : EReal)) := by
      calc
        (((⟪z, v⟫_ℝ : ℝ) : EReal)) ≤ (f z : EReal) + (f∗[hf] v : EReal) := by
          simpa [gammaZeroConjugate_apply] using
            (fenchel_young_inequality (f := f.asEReal) (isProper_of_mem_gammaZero hf) z v)
        _ = ((((f z : EReal).toReal : ℝ) : EReal)) +
              ((((f∗[hf] v : EReal).toReal : ℝ) : EReal)) := by
                rw [EReal.coe_toReal hzf_top hzf_bot, EReal.coe_toReal hvconj_top hvconj_bot]
        _ = ((((f z : EReal).toReal + (f∗[hf] v : EReal).toReal : ℝ) : EReal)) := by
              rw [EReal.coe_add]
    exact EReal.coe_le_coe_iff.mp hcast
  have htilt_gap_real :
      (ψ y : EReal).toReal - (ψ z : EReal).toReal ≤ (lam : ℝ) * (μ : ℝ) := by
    rw [hψz_toReal]
    nlinarith
  have hdist_cast :
      (((‖y - z‖ ^ 2 + (γ : ℝ) * (ψ z : EReal).toReal : ℝ) : EReal)) ≤
        ((((γ : ℝ) * (ψ y : EReal).toReal : ℝ) : EReal)) := by
    simpa [posReal_smul_apply, EReal.coe_add, EReal.coe_mul, EReal.coe_toReal hz_top hz_bot,
      EReal.coe_toReal hψy_top hψy_bot, real_inner_self_eq_norm_sq] using hprox_var y
  have hdist_real :
      ‖y - z‖ ^ 2 + (γ : ℝ) * (ψ z : EReal).toReal ≤ (γ : ℝ) * (ψ y : EReal).toReal := by
    exact EReal.coe_le_coe_iff.mp hdist_cast
  have hz_close_sq : ‖y - z‖ ^ 2 ≤ (lam : ℝ) ^ 2 := by
    have hdist_bound :
        ‖y - z‖ ^ 2 ≤ (γ : ℝ) * ((ψ y : EReal).toReal - (ψ z : EReal).toReal) := by
      nlinarith [hdist_real]
    have hγ_val : (γ : ℝ) = (lam : ℝ) / (μ : ℝ) := rfl
    rw [hγ_val] at hdist_bound
    have hscaled :
        ‖y - z‖ ^ 2 ≤ ((lam : ℝ) / (μ : ℝ)) * ((lam : ℝ) * (μ : ℝ)) := by
      exact le_trans hdist_bound (mul_le_mul_of_nonneg_left htilt_gap_real (by positivity))
    have hcancel :
        ((lam : ℝ) / (μ : ℝ)) * ((lam : ℝ) * (μ : ℝ)) = (lam : ℝ) ^ 2 := by
      field_simp [hμ_pos.ne']
    rw [hcancel] at hscaled
    exact hscaled
  have hz_close : ‖z - y‖ ≤ (lam : ℝ) := by
    have hyz_sq : ‖z - y‖ ^ 2 ≤ (lam : ℝ) ^ 2 := by
      simpa [norm_sub_rev] using hz_close_sq
    nlinarith [hyz_sq]
  have hu_norm : ‖u‖ ≤ (μ : ℝ) := by
    have hu_norm_eq : ‖u‖ = (γ : ℝ)⁻¹ * ‖y - z‖ := by
      calc
        ‖u‖ = ‖(γ : ℝ)⁻¹ • (y - z)‖ := by rfl
        _ = (γ : ℝ)⁻¹ * ‖y - z‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr γ.2.le)]
    have hγinv : (γ : ℝ)⁻¹ = (μ : ℝ) / (lam : ℝ) := by
      dsimp [γ]
      field_simp [hlam_pos.ne', hμ_pos.ne']
    rw [hu_norm_eq, hγinv]
    have hyz_le : ‖y - z‖ ≤ (lam : ℝ) := by
      simpa [norm_sub_rev] using hz_close
    have hscaled :
        ((μ : ℝ) / (lam : ℝ)) * ‖y - z‖ ≤ ((μ : ℝ) / (lam : ℝ)) * (lam : ℝ) :=
      mul_le_mul_of_nonneg_left hyz_le (by positivity)
    have hcancel : ((μ : ℝ) / (lam : ℝ)) * (lam : ℝ) = (μ : ℝ) := by
      field_simp [hlam_pos.ne']
    simpa [hcancel] using hscaled
  have hw : u + v ∈ (∂ f) z := by
    exact (mem_subdifferential_affineTiltIoi_iff (f := f) (hf := hf) v z u).1 hu
  refine ⟨z, u + v, hw, hz_close, ?_⟩
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hu_norm

end SubdifferentialCalculus

end ERealFunction

/-! Source item:
`TheoremLib/Attouch_Chbani_Riahi_Fast_proximal_methods_via_time_scaling_of_damped_inertial_dynamics_2019_correction/items/ext_def_2` -/

/-- Proximal optimality in subgradient form: for a real-valued objective `Φ`, a point `p` is a
proximal point of `Φ` at `y` with step `l > 0` exactly when the residual `l⁻¹ • (y - p)` belongs
to the subdifferential of `Φ` at `p`.  Equivalently, `p` satisfies the variational inequality
`⟨y - p, z - p⟩ ≤ l (Φ z - Φ p)` for all `z`; the primal (argmin) form of the same notion is
`ERealFunction.IsProxPoint`. -/
def IsProximalPoint {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (Φ : H → ℝ) (l : ℝ) (y p : H) : Prop :=
  0 < l ∧ (l⁻¹ • (y - p)) ∈ ERealFunction.subdifferential (fun x => (Φ x : EReal)) p
