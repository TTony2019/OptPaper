import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_4
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_3
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_5
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_thm_2

open ERealFunction

/-- Lemma 3.1: objective-gap bounds for an A'-approximate proximal minimizer. -/
theorem approximation_minimizer_gap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) {lam ε : ℝ} {y x p : H} (hlam : 0 < lam)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hp : p ∈ proximalPoints f lam y)
    (hstrong : IsStronglyConvexWith (_root_.proximalObjective f lam y) (1 / lam))
    (hx : ∃ w : H, w ∈ subdifferential (fun z => (_root_.proximalObjective f lam y z : EReal)) x ∧
      ‖w‖ ≤ ε / lam) :
    ‖x - p‖ ^ 2 / (2 * lam) ≤ _root_.proximalObjective f lam y x - _root_.proximalObjective f lam y p ∧
      _root_.proximalObjective f lam y x - _root_.proximalObjective f lam y p ≤ ε ^ 2 / (2 * lam) := by
  let g := _root_.proximalObjective f lam y
  rcases hp with ⟨_, hpmin_raw⟩
  have hpmin : IsMinOn g Set.univ p := by
    simpa [g, _root_.proximalObjective] using hpmin_raw
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have hden_pos : 0 < 2 * lam := by positivity
  have hcoef : lam⁻¹ / 2 = 1 / (2 * lam) := by
    field_simp [hlam_ne]
  have hzero : (0 : H) ∈ subdifferential (fun y => (g y : EReal)) p := by
    rw [mem_convexSubdifferential_iff]
    intro z
    simpa using hpmin (Set.mem_univ z)
  have hlower_raw := stronglyConvex_subgradient_inequality g (by simpa [g] using hstrong)
    hzero (z := x)
  have hlower : ‖x - p‖ ^ 2 / (2 * lam) ≤ g x - g p := by
    rw [hcoef] at hlower_raw
    simp only [inner_zero_left] at hlower_raw
    ring_nf at hlower_raw ⊢
    linarith
  rcases hx with ⟨w, hw, hwnorm⟩
  have hw' : w ∈ subdifferential (fun y => (g y : EReal)) x := by simpa [g] using hw
  have hupper_raw := stronglyConvex_subgradient_inequality g (by simpa [g] using hstrong)
    hw' (z := p)
  rw [hcoef] at hupper_raw
  have hinter : -(‖w‖ * ‖p - x‖) ≤ inner ℝ w (p - x) := by
    have hcs := real_inner_le_norm (-w) (p - x)
    rw [inner_neg_left, norm_neg] at hcs
    linarith
  have hr_nonneg : 0 ≤ ‖p - x‖ := norm_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hwnorm hr_nonneg
  have hinner : -(ε / lam) * ‖p - x‖ ≤ inner ℝ w (p - x) := by
    calc
      -(ε / lam) * ‖p - x‖ = -((ε / lam) * ‖p - x‖) := by ring
      _ ≤ -(‖w‖ * ‖p - x‖) := neg_le_neg hmul
      _ ≤ inner ℝ w (p - x) := hinter
  have hgap : -(ε / lam) * ‖p - x‖ + ‖p - x‖ ^ 2 / (2 * lam) ≤ g p - g x := by
    ring_nf at hupper_raw hinner ⊢
    linarith
  have hsq : 0 ≤ (‖p - x‖ - ε) ^ 2 := sq_nonneg _
  have hscalar : -ε ^ 2 / (2 * lam) ≤
      -(ε / lam) * ‖p - x‖ + ‖p - x‖ ^ 2 / (2 * lam) := by
    field_simp [hlam_ne]
    nlinarith
  have hupper : g x - g p ≤ ε ^ 2 / (2 * lam) := by
    ring_nf at hscalar hgap ⊢
    linarith [hscalar, hgap]
  constructor
  · simpa [g] using hlower
  · simpa [g] using hupper
