import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_3
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.cor_1

/-- Corollary 2.2: the tuned update lowers the estimate minimum below the new objective value. -/
theorem tuned_proximal_step_bound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (f : H → ℝ)
    {x ν y xnext : H} {lam A_next φnext α : ℝ} (hlam : 0 < lam)
    (hA : 0 < A_next) (hy : y = (1 - α) • x + α • ν)
    (hα : α ^ 2 = A_next * lam) (hp : xnext ∈ proximalPoints f lam y)
    (hbound : φnext ≥ f xnext + (1 / (2 * lam)) *
      (2 - α ^ 2 / (A_next * lam)) * ‖y - xnext‖ ^ 2) :
    φnext ≥ f xnext + ‖y - xnext‖ ^ 2 / (2 * lam) ∧
      f xnext + ‖y - xnext‖ ^ 2 / (2 * lam) ≥ f xnext := by
  have hden_pos : 0 < A_next * lam := mul_pos hA hlam
  have hden : A_next * lam ≠ 0 := ne_of_gt hden_pos
  have hcoef : 2 - α ^ 2 / (A_next * lam) = 1 := by
    rw [hα, div_self hden]
    norm_num
  have hfirst : φnext ≥ f xnext + ‖y - xnext‖ ^ 2 / (2 * lam) := by
    calc
      φnext ≥ f xnext + (1 / (2 * lam)) *
          (2 - α ^ 2 / (A_next * lam)) * ‖y - xnext‖ ^ 2 := hbound
      _ = f xnext + ‖y - xnext‖ ^ 2 / (2 * lam) := by
        rw [hcoef]
        ring
  have hsq : 0 ≤ ‖y - xnext‖ ^ 2 := sq_nonneg _
  have htwo_lam : 0 ≤ 2 * lam := le_of_lt (mul_pos (by norm_num) hlam)
  have hterm : 0 ≤ ‖y - xnext‖ ^ 2 / (2 * lam) := div_nonneg hsq htwo_lam
  exact ⟨hfirst, le_add_of_nonneg_right hterm⟩
