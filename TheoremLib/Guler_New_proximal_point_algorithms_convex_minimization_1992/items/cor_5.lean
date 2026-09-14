import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_3
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.lem_4
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_3

/-- Corollary 3.2: the tuned inexact bound equals the proximal minimum. -/
theorem inexact_tuned_proximal_bound {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : H → ℝ) {x ν y p : H} {lam A_next φnext δ α : ℝ} (hlam : 0 < lam)
    (hA_next : 0 < A_next)
    (hy : y = (1 - α) • x + α • ν) (hα : α ^ 2 = A_next * lam)
    (hp : p ∈ proximalPoints f lam y)
    (hbound : φnext + (1 - α) * δ ≥ f p + (1 / (2 * lam)) *
      (2 - α ^ 2 / (A_next * lam)) * ‖y - p‖ ^ 2) :
    φnext + (1 - α) * δ ≥ f p + ‖p - y‖ ^ 2 / (2 * lam) ∧
      f p + ‖p - y‖ ^ 2 / (2 * lam) = proximalObjective f lam y p := by
  constructor
  · have hden : A_next * lam ≠ 0 :=
      mul_ne_zero (ne_of_gt hA_next) (ne_of_gt hlam)
    have hfrac : α ^ 2 / (A_next * lam) = (1 : ℝ) := by
      rw [hα]
      exact div_self hden
    have hcoeff : 2 - α ^ 2 / (A_next * lam) = (1 : ℝ) := by
      rw [hfrac]
      norm_num
    have hbound_y : f p + ‖y - p‖ ^ 2 / (2 * lam) ≤ φnext + (1 - α) * δ := by
      calc
        f p + ‖y - p‖ ^ 2 / (2 * lam) =
            f p + (1 / (2 * lam)) * (2 - α ^ 2 / (A_next * lam)) * ‖y - p‖ ^ 2 := by
              rw [hcoeff]
              ring
        _ ≤ φnext + (1 - α) * δ := hbound
    rw [norm_sub_rev]
    exact hbound_y
  · rfl
