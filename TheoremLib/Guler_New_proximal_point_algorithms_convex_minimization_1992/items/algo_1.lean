import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_3
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.cor_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_6
import Foundation.Analysis.ExtendedRealFunctions

/-- Data and recurrences of the proximal point algorithm (2.23)--(2.24).

The algorithm record is the paper's finite-valued specialization; the extended
real objective assumptions are retained as fields but `f` itself has type
`H → ℝ`. -/
structure ProximalPointAlgorithm {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (f : H → ℝ) where
  A : ℝ
  x : ℕ → H
  y : ℕ → H
  nu : ℕ → H
  lam : ℕ → ℝ
  alpha : ℕ → ℝ
  curvature : ℕ → ℝ
  A_pos : 0 < A
  f_proper : ERealFunction.IsProper (fun z => (f z : EReal))
  f_lowerSemicontinuous : LowerSemicontinuous f
  f_convex : ConvexOn ℝ Set.univ f
  x0_feasible : IsFeasible (fun z => (f z : EReal)) (x 0)
  lam_pos : ∀ k, 0 < lam k
  alpha_eq : ∀ k, alpha k ^ 2 = (1 - alpha k) * curvature k * lam k
  alpha_formula : ∀ k, alpha k =
    (Real.sqrt ((curvature k * lam k) ^ 2 + 4 * curvature k * lam k) - curvature k * lam k) / 2
  /-- The algorithm chooses the positive root in (2.23); this is needed by `nu_step`. -/
  alpha_pos : ∀ k, 0 < alpha k
  alpha_mem : ∀ k, alpha k ∈ Set.Ico (0 : ℝ) 1
  initial_center : nu 0 = x 0
  initial_curvature : curvature 0 = A
  y_step : ∀ k, y k = (1 - alpha k) • x k + alpha k • nu k
  x_step : ∀ k, x (k + 1) ∈ proximalPoints f (lam k) (y k)
  nu_step : ∀ k, nu (k + 1) = nu k + (1 / alpha k) • (x (k + 1) - y k)
  curvature_step : ∀ k, curvature (k + 1) = (1 - alpha k) * curvature k
