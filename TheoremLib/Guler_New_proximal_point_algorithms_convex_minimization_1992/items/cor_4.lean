import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_4
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.lem_3
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_3

open ERealFunction

/-- Corollary 3.1: an A'-approximate point is within `ε_k` of the exact proximal point. -/
theorem approximation_minimizer_distance {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) {lam ε : ℝ} {y x p : H} (hlam : 0 < lam)
    (hconvex : ConvexOn ℝ Set.univ f)
    (hp : p ∈ proximalPoints f lam y)
    (hstrong : IsStronglyConvexWith (_root_.proximalObjective f lam y) (1 / lam))
    (hx : ∃ w : H, w ∈ subdifferential (fun z => (_root_.proximalObjective f lam y z : EReal)) x ∧
      ‖w‖ ≤ ε / lam) :
    ‖x - p‖ ≤ ε := by
  rcases hx with ⟨w, hwsub, hw_bound⟩
  have hgap := approximation_minimizer_gap f hlam hconvex hp hstrong
    ⟨w, hwsub, hw_bound⟩
  have hdiv := hgap.1.trans hgap.2
  have hden_pos : 0 < 2 * lam := by positivity
  have hsq : ‖x - p‖ ^ 2 ≤ ε ^ 2 :=
    (div_le_div_iff_of_pos_right hden_pos).mp hdiv
  have heps_div : 0 ≤ ε / lam := le_trans (norm_nonneg w) hw_bound
  have hlam_ne : lam ≠ 0 := ne_of_gt hlam
  have heq : (ε / lam) * lam = ε := by
    field_simp [hlam_ne]
  have heps_nonneg : 0 ≤ ε := by
    rw [← heq]
    exact mul_nonneg heps_div (le_of_lt hlam)
  nlinarith [norm_nonneg (x - p), heps_nonneg, hsq]
