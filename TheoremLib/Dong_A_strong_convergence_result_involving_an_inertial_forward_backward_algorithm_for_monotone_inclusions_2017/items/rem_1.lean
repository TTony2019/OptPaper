import Mathlib.Tactic
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.algo_1
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.def_2
import Foundation.Hilbert.WeakTopology

/-! Remark 3.1: the sets in (3.1) are affine half-spaces. -/

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem inertial_constraint_iff_halfspace (xPrev x z u : H) (a : ℝ)
    (y : H) (hy : y = x + a • (x - xPrev)) :
    ‖z - u‖ ^ 2 ≤ ‖x - u‖ ^ 2 - 2 * a * inner ℝ (x - u) (xPrev - x) +
        a ^ 2 * ‖xPrev - x‖ ^ 2 ↔
      inner ℝ u (y - z) ≤ (‖x‖ ^ 2 - ‖z‖ ^ 2 -
        2 * a * inner ℝ x (xPrev - x) + a ^ 2 * ‖xPrev - x‖ ^ 2) / 2 := by
  have hyz : y - z = x - z - a • (xPrev - x) := by
    rw [hy]
    module
  rw [hyz]
  rw [norm_sub_sq_real z u, norm_sub_sq_real x u, inner_sub_left]
  rw [← real_inner_comm z u, ← real_inner_comm x u]
  simp only [inner_sub_right, real_inner_smul_right]
  constructor <;> intro h <;> nlinarith

theorem q_constraint_iff_halfspace (x0 x u : H) :
    inner ℝ (u - x) (x0 - x) ≤ 0 ↔ inner ℝ u (x0 - x) ≤ inner ℝ x (x0 - x) := by
  rw [inner_sub_left]
  constructor <;> intro h <;> linarith
