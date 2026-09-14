import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_3

/-- Canonical scalar and center recurrences for the estimate quadratics. -/
structure EstimateQuadraticParameters {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] where
  A : ℝ
  alpha : ℕ → ℝ
  lam : ℕ → ℝ
  y : ℕ → H
  p : ℕ → H
  nu : ℕ → H
  curvature : ℕ → ℝ
  phi : ℕ → H → ℝ
  phi_star : ℕ → ℝ
  curvature_zero : curvature 0 = A
  curvature_succ : ∀ k, curvature (k + 1) = (1 - alpha k) * curvature k
  curvature_eq_beta : ∀ k, curvature k = betaSequence alpha k * A
  quadratic_representation : ∀ k x, phi k x = phi_star k + (curvature k / 2) * ‖x - nu k‖ ^ 2
  center_minimizes : ∀ k x, phi_star k ≤ phi k x
  center_succ : ∀ k, nu (k + 1) = nu k - (alpha k / (curvature (k + 1) * lam k)) • (y k - p k)
