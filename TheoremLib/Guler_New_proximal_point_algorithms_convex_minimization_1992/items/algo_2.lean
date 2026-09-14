import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_3
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.algo_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_6
import Foundation.Analysis.ExtendedRealFunctions

/-- The monotonic proximal point algorithm, including the comparison choice of `x_{k+1}`. -/
structure MonotonicProximalPointAlgorithm {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : H → ℝ) where
  A : ℝ
  x : ℕ → H
  y : ℕ → H
  nu : ℕ → H
  p : ℕ → H
  lam : ℕ → ℝ
  alpha : ℕ → ℝ
  curvature : ℕ → ℝ
  A_pos : 0 < A
  f_proper : ERealFunction.IsProper (fun z => (f z : EReal))
  f_lowerSemicontinuous : LowerSemicontinuous f
  f_convex : ConvexOn ℝ Set.univ f
  x0_feasible : IsFeasible (fun z => (f z : EReal)) (x 0)
  lam_pos : ∀ k, 0 < lam k
  alpha_formula : ∀ k, alpha k = (Real.sqrt ((curvature k * lam k) ^ 2 + 4 * curvature k * lam k) -
    curvature k * lam k) / 2
  /-- The positive root required by the algorithm and by the `1 / alpha` update. -/
  alpha_pos : ∀ k, 0 < alpha k
  alpha_mem : ∀ k, alpha k ∈ Set.Ico (0 : ℝ) 1
  initial_center : nu 0 = x 0
  initial_curvature : curvature 0 = A
  y_step : ∀ k, y k = (1 - alpha k) • x k + alpha k • nu k
  proximal_step : ∀ k, p (k + 1) ∈ proximalPoints f (lam k) (y k)
  monotone_step : ∀ k, f (x (k + 1)) = min (f (p (k + 1))) (f (x k))
  /-- `arg min {f(p_{k+1}), f(x_k)}` selects one of the two candidate points. -/
  choice_step : ∀ k, x (k + 1) = p (k + 1) ∨ x (k + 1) = x k
  nu_step : ∀ k, nu (k + 1) = nu k + (1 / alpha k) • (x (k + 1) - y k)
  curvature_step : ∀ k, curvature (k + 1) = (1 - alpha k) * curvature k
