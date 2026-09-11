import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.def_1
import Foundation.Analysis.ExtendedRealFunctions
import Foundation.Convex.ProximalOperator
import Foundation.Convex.Subdifferential
import Foundation.SetValued.Monotone
import Foundation.SetValued.Minty
import Mathlib.Tactic

open scoped InnerProductSpace
open ERealFunction

/-! The subdifferential of an extended-real-valued function is supplied by Foundation
(Bauschke--Combettes, Definition 16.1): `ERealFunction.subdifferential f : SetValuedOperator H H`. -/
recall ERealFunction.subdifferential

namespace BurachikSvaiterRobustnessHPE2001

/-- The epsilon-subdifferential of an extended-real-valued function. -/
def epsilonSubdifferential {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (ε : ℝ) : SetValuedOperator H H :=
  fun x ↦ {v | ∀ z, f z ≥ f x + (inner ℝ v (z - x) - ε : EReal)}

/-- Every epsilon-subgradient is in the corresponding enlargement of the ordinary
subdifferential. -/
theorem epsilonSubdifferential_subset_enlargement
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : ERealFunction.IsProper f) (ε : ℝ) (hε : 0 ≤ ε) (x : H) :
    epsilonSubdifferential f ε x ⊆ epsilonEnlargement (subdifferential f) ε hε x := by
  intro v hv z w hw
  change -ε ≤ inner ℝ (w - v) (z - x)
  rcases hf.2 with ⟨a, ha⟩
  have hfa_lt : f a < ⊤ := ha
  have hfa_top : f a ≠ ⊤ := ne_of_lt hfa_lt
  have hfx_bot : f x ≠ ⊥ := hf.1 x
  have hfz_bot : f z ≠ ⊥ := hf.1 z
  have hfx_top : f x ≠ ⊤ := by
    intro htop
    have h := hv a
    rw [htop] at h
    simp at h
    exact (not_lt_of_ge h) hfa_lt
  have hfz_top : f z ≠ ⊤ := by
    intro htop
    have h := hw a
    rw [htop] at h
    have hle : (⊤ : EReal) ≤ f a := by
      simpa only [EReal.coe_add_top] using h
    exact hfa_top (top_le_iff.mp hle)
  have hvz := hv z
  have hwx := hw x
  rw [← EReal.coe_toReal hfx_top hfx_bot, ← EReal.coe_toReal hfz_top hfz_bot] at hvz
  norm_cast at hvz
  have hwx' : inner ℝ (x - z) w + (f z).toReal ≤ (f x).toReal := by
    have hbot : (⟪x - z, w⟫_ℝ : EReal) + f z ≠ ⊥ :=
      EReal.add_ne_bot_iff.mpr ⟨EReal.coe_ne_bot _, hfz_bot⟩
    have h' := EReal.toReal_le_toReal hwx hbot hfx_top
    erw [EReal.toReal_add (EReal.coe_ne_top _) (EReal.coe_ne_bot _) hfz_top hfz_bot,
      EReal.toReal_coe] at h'
    simpa using h'
  rw [show x - z = -(z - x) by abel, inner_neg_left, real_inner_comm] at hwx'
  rw [inner_sub_left]
  linarith

/-- The subdifferential of a proper extended-real-valued function is monotone. -/
theorem subdifferential_isMonotone
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : ERealFunction.IsProper f) :
    (subdifferential f).IsMonotone := by
  intro x z v hv w hw
  have hvε : v ∈ epsilonSubdifferential f 0 x := by
    intro y
    have h := hv y
    rw [real_inner_comm] at h
    simpa [add_comm] using h
  have henlarge :=
    epsilonSubdifferential_subset_enlargement f hf 0 (le_refl 0) x hvε z w hw
  have hnonneg : 0 ≤ inner ℝ (w - v) (z - x) := by
    simpa [epsilonEnlargement] using henlarge
  calc
    0 ≤ inner ℝ (w - v) (z - x) := hnonneg
    _ = inner ℝ (v - w) (x - z) := by
      rw [show w - v = -(v - w) by abel, show z - x = -(x - z) by abel,
        inner_neg_neg]

/-- A global minimizer of the unit proximal objective satisfies the quantitative
support inequality obtained by expanding the squared norm. -/
theorem proximal_minimizer_quadratic_bound
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : ERealFunction.IsProper f) (y x : H)
    (hmin : ∀ z : H,
      f x + (((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) ≤
        f z + (((1 / 2 : ℝ) * ‖z - y‖ ^ 2 : ℝ) : EReal)) :
    ∀ z, f z ≥ f x +
      ((inner ℝ (y - x) (z - x) - (1 / 2 : ℝ) * ‖z - x‖ ^ 2 : ℝ) : EReal) := by
  rcases hf.2 with ⟨a, ha⟩
  have hfa_top : f a ≠ ⊤ := ne_of_lt ha
  have hfa_bot : f a ≠ ⊥ := hf.1 a
  have hfx_bot : f x ≠ ⊥ := hf.1 x
  have hfx_top : f x ≠ ⊤ := by
    intro htop
    have h := hmin a
    rw [htop] at h
    have htop_le : ⊤ ≤ f a + (((1 / 2 : ℝ) * ‖a - y‖ ^ 2 : ℝ) : EReal) := by
      rw [EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at h
      exact h
    exact (EReal.add_ne_top hfa_top (EReal.coe_ne_top _)) (top_unique htop_le)
  intro z
  by_cases hfz_top : f z = ⊤
  · rw [hfz_top]
    exact le_top
  have hfz_bot : f z ≠ ⊥ := hf.1 z
  have hreal := EReal.toReal_le_toReal (hmin z)
    (EReal.add_ne_bot_iff.mpr ⟨hfx_bot, EReal.coe_ne_bot _⟩)
    (EReal.add_ne_top hfz_top (EReal.coe_ne_top _))
  have hreal' :
      (f x).toReal + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 ≤
        (f z).toReal + (1 / 2 : ℝ) * ‖z - y‖ ^ 2 := by
    rw [EReal.toReal_add hfx_top hfx_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _),
      EReal.toReal_add hfz_top hfz_bot (EReal.coe_ne_top _) (EReal.coe_ne_bot _)] at hreal
    norm_num at hreal ⊢
    exact hreal
  have hsq :
      ‖z - y‖ ^ 2 = ‖x - y‖ ^ 2 + 2 * inner ℝ (x - y) (z - x) + ‖z - x‖ ^ 2 := by
    rw [show z - y = (x - y) + (z - x) by abel, norm_add_sq_real]
  rw [hsq] at hreal'
  have hnorm : 0 ≤ ‖z - x‖ ^ 2 := sq_nonneg _
  have hsub :
      (f x).toReal + inner ℝ (y - x) (z - x) - (1 / 2 : ℝ) * ‖z - x‖ ^ 2 ≤
        (f z).toReal := by
    rw [show x - y = -(y - x) by abel, inner_neg_left] at hreal'
    simp only [norm_neg] at hreal'
    norm_num at hreal'
    linarith
  rw [← EReal.coe_toReal hfx_top hfx_bot, ← EReal.coe_toReal hfz_top hfz_bot]
  norm_cast
  linarith

/-- Completing the square after adding a quadratic proximal term to an affine
minorant.  This estimate is useful independently of the maximality argument. -/
theorem subdifferential_moreau_coercive
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (a : H) (b : ℝ)
    (haff : ∀ x : H, ((inner ℝ a x + b : ℝ) : EReal) ≤ f x) (y x : H) :
    (((1 / 2 : ℝ) * ‖x - (y - a)‖ ^ 2 +
        (inner ℝ a y + b - (1 / 2 : ℝ) * ‖a‖ ^ 2 : ℝ) : ℝ) : EReal) ≤
      f x + (((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
  have hsq :
      inner ℝ a x + b + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 =
        (1 / 2 : ℝ) * ‖x - (y - a)‖ ^ 2 +
          (inner ℝ a y + b - (1 / 2 : ℝ) * ‖a‖ ^ 2) := by
    have hnorm :
        ‖x - y‖ ^ 2 = ‖x - (y - a)‖ ^ 2 -
          2 * inner ℝ (x - (y - a)) a + ‖a‖ ^ 2 := by
      rw [show x - y = (x - (y - a)) - a by abel, norm_sub_sq_real]
    rw [hnorm]
    have hsplit : x = (x - (y - a)) + y - a := by abel
    have hinner :
        inner ℝ a x = inner ℝ a (x - (y - a)) + inner ℝ a y - inner ℝ a a := by
      conv_lhs => rw [hsplit]
      rw [inner_sub_right, inner_add_right]
    rw [hinner, real_inner_self_eq_norm_sq]
    rw [real_inner_comm a (x - (y - a))]
    ring
  have hadd := add_le_add_right (haff x)
    (((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal)
  have hadd' :
      ((inner ℝ a x + b + (1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) ≤
        f x + (((1 / 2 : ℝ) * ‖x - y‖ ^ 2 : ℝ) : EReal) := by
    simpa [EReal.coe_add, EReal.coe_mul, add_comm, add_left_comm, add_assoc] using hadd
  rwa [hsq] at hadd'

/-- Exact expansion of the quadratic term along a segment. -/
theorem subdifferential_moreau_quadratic_direction
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (z p y : H) {t : ℝ} (ht : 0 ≤ t) :
    (1 / 2 : ℝ) * ‖(1 - t) • p + t • y - z‖ ^ 2 =
      (1 / 2 : ℝ) * ‖p - z‖ ^ 2 +
        t * inner ℝ (p - z) (y - p) +
        (1 / 2 : ℝ) * t ^ 2 * ‖y - p‖ ^ 2 := by
  have hvec :
      (1 - t) • p + t • y - z = (p - z) + t • (y - p) := by
    module
  rw [hvec, norm_add_sq_real, inner_smul_right, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg ht]
  ring

/-- The epigraph formulation of convexity gives the usual extended-real Jensen
inequality.  Keeping this conversion separate avoids reopening epigraph
membership in the proximal argument below. -/
private theorem subdifferential_epigraph_convex
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (hf : ERealFunction.IsProper f)
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) :
    ∀ x z : H, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
      f (a • x + b • z) ≤ (a : EReal) * f x + (b : EReal) * f z := by
  intro x z a b ha hb hab
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simp [ha0, hb1]
  by_cases hb0 : b = 0
  · have ha1 : a = 1 := by linarith
    simp [hb0, ha1]
  by_cases hxa_top : f x = ⊤
  · rw [hxa_top]
    have hterm : (b : EReal) * f z ≠ ⊥ :=
      (EReal.mul_ne_bot _ _).2 ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (hf.1 z),
        Or.inl (EReal.coe_ne_top _), Or.inl (EReal.coe_nonneg.mpr hb)⟩
    rw [EReal.coe_mul_top_of_pos (lt_of_le_of_ne ha (Ne.symm ha0)),
      EReal.top_add_of_ne_bot hterm]
    exact (le_top : f (a • x + b • z) ≤ (⊤ : EReal))
  by_cases hza_top : f z = ⊤
  · rw [hza_top]
    have hterm : (a : EReal) * f x ≠ ⊥ :=
      (EReal.mul_ne_bot _ _).2 ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (hf.1 x),
        Or.inl (EReal.coe_ne_top _), Or.inl (EReal.coe_nonneg.mpr ha)⟩
    rw [EReal.coe_mul_top_of_pos (lt_of_le_of_ne hb (Ne.symm hb0)),
      EReal.add_top_of_ne_bot hterm]
    exact (le_top : f (a • x + b • z) ≤ (⊤ : EReal))
  have hxe : (x, (f x).toReal) ∈ ERealFunction.epigraph f := by
    rw [ERealFunction.mem_epigraph_iff]
    exact le_of_eq (EReal.coe_toReal hxa_top (hf.1 x)).symm
  have hze : (z, (f z).toReal) ∈ ERealFunction.epigraph f := by
    rw [ERealFunction.mem_epigraph_iff]
    exact le_of_eq (EReal.coe_toReal hza_top (hf.1 z)).symm
  have hmem := hconvex hxe hze ha hb hab
  change f (a • x + b • z) ≤
    (((a * (f x).toReal + b * (f z).toReal : ℝ) : EReal)) at hmem
  rw [← EReal.coe_toReal hxa_top (hf.1 x),
    ← EReal.coe_toReal hza_top (hf.1 z),
    ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
  exact hmem

/-- Remark 1: a proper closed convex function has a maximal monotone subdifferential, and its
epsilon-subdifferential is included in the corresponding operator enlargement. -/
theorem subdifferential_enlargement_remark
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → EReal) (hf : ERealFunction.IsProper f)
    (hclosed : IsClosed (ERealFunction.epigraph f))
    (hconvex : Convex ℝ (ERealFunction.epigraph f)) (ε : ℝ) (hε : 0 ≤ ε) :
    (subdifferential f).IsMaximalMonotone ∧
      ∀ x, epsilonSubdifferential f ε x ⊆ epsilonEnlargement (subdifferential f) ε hε x := by
  constructor
  · apply maximal_monotone_of_minty_surjective (subdifferential_isMonotone f hf)
    intro y
    let g : H → EReal := fun z ↦
      f z + (((1 / 2 : ℝ) * ‖z - y‖ ^ 2 : ℝ) : EReal)
    have h_lsc : LowerSemicontinuous f :=
      (ERealFunction.lowerSemicontinuous_iff_isClosed_epigraph f).2 hclosed
    have hg_proper : ERealFunction.IsProper g := by
      constructor
      · intro z
        exact EReal.add_ne_bot_iff.mpr ⟨hf.1 z, EReal.coe_ne_bot _⟩
      · rcases hf.2 with ⟨z, hz⟩
        refine ⟨z, ?_⟩
        change g z < ⊤
        exact EReal.add_lt_top (ne_of_lt hz) (EReal.coe_ne_top _)
    have hres_of_variational_inequality : ∀ (p : H),
        (∀ z, f z ≥ f p + (inner ℝ (y - p) (z - p) : EReal)) →
          ∃ u ∈ subdifferential f p, y = p + u := by
      intro p hp
      refine ⟨y - p, ?_, ?_⟩
      · intro z
        have h := hp z
        rw [real_inner_comm] at h
        simpa [add_comm] using h
      · abel
    have hf_convex : ERealFunction.IsConvex f :=
      ERealFunction.isConvex_of_convex_epigraph hf hconvex
    have hf_gamma : f ∈ ERealFunction.gamma H := ⟨hf_convex, h_lsc⟩
    let fI : H → Set.Ioi (⊥ : EReal) := ERealFunction.properIoi f hf
    have hfI : fI ∈ ERealFunction.gammaZero H := by
      exact ERealFunction.properIoi_mem_gammaZero_of_mem_gamma hf hf_gamma
    obtain ⟨p, hp, _⟩ :=
      ERealFunction.hasUniqueProxPoint_of_mem_gammaZero (f := fI) hfI y
    have hvarI :=
      (ERealFunction.isProxPoint_iff_forall_inner_add_le fI hfI.2 y p).1 hp
    have hvar : ∀ z, f z ≥ f p + (inner ℝ (y - p) (z - p) : EReal) := by
      intro z
      have hz := hvarI z
      simpa [fI, ERealFunction.properIoi_apply, add_comm, real_inner_comm] using hz
    exact ⟨p, hres_of_variational_inequality p hvar⟩
  · exact fun x => epsilonSubdifferential_subset_enlargement f hf ε hε x

end BurachikSvaiterRobustnessHPE2001
