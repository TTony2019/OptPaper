import Mathlib.Tactic
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.def_2
import Foundation.Projection.BestApproximation

/-! Lemma 2.4: the Pythagorean inequality for metric projections. -/

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

theorem metric_projection_pythagorean {C : Set H} (hC : C.Nonempty) (hClosed : IsClosed C)
    (hConvex : Convex ℝ C) (x : H) (y : H) (hy : y ∈ C) :
    ‖y - projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC hClosed hConvex) x‖ ^ 2 +
      ‖x - projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC hClosed hConvex) x‖ ^ 2 ≤
        ‖x - y‖ ^ 2 := by
  let p : H := projectionPoint C (isChebyshev_of_nonempty_isClosed_convex hC hClosed hConvex) x
  have hp_char : p ∈ C ∧ ∀ z ∈ C, ⟪z - p, x - p⟫_ℝ ≤ 0 := by
    simpa [p] using
      (eq_projectionPoint_iff_mem_and_inner_sub_right_nonpos_of_nonempty_isClosed_convex
        hC hClosed hConvex).mp rfl
  have hinner : ⟪x - p, y - p⟫_ℝ ≤ 0 := by
    simpa [real_inner_comm] using hp_char.2 y hy
  have hvec : (x - p) - (y - p) = x - y := by
    abel_nf
  have hsq : ‖x - y‖ ^ 2 =
      ‖x - p‖ ^ 2 - 2 * ⟪x - p, y - p⟫_ℝ + ‖y - p‖ ^ 2 := by
    calc
      ‖x - y‖ ^ 2 = ‖(x - p) - (y - p)‖ ^ 2 := by
        rw [hvec]
      _ = ‖x - p‖ ^ 2 - 2 * ⟪x - p, y - p⟫_ℝ + ‖y - p‖ ^ 2 :=
        norm_sub_sq_real (x - p) (y - p)
  simpa only [p] using (show ‖y - p‖ ^ 2 + ‖x - p‖ ^ 2 ≤ ‖x - y‖ ^ 2 by
    nlinarith [hsq, hinner])
