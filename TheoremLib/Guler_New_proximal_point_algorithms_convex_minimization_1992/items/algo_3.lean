import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_1
import Foundation.Analysis.ExtendedRealFunctions

/-- Data and update rules for the second proximal point algorithm (6.1)--(6.3). -/
structure SecondProximalPointAlgorithm {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (f : H → ℝ) where
  x : ℕ → H
  y : ℕ → H
  lam : ℕ → ℝ
  beta : ℕ → ℝ
  f_proper : ERealFunction.IsProper (fun z => (f z : EReal))
  f_lowerSemicontinuous : LowerSemicontinuous f
  f_convex : ConvexOn ℝ Set.univ f
  lam_initial : 0 < lam 1
  beta_initial : beta 1 = 1
  y_initial : y 1 = x 0
  /-- The paper chooses `lambda_k >= lambda_(k-1)` for `k >= 2`; equivalently
      the used tail satisfies `lambda_i <= lambda_(i+1)` for `i >= 1`. -/
  lam_monotone : ∀ k, 1 ≤ k → lam k ≤ lam (k + 1)
  beta_step : ∀ k, 1 ≤ k → beta (k + 1) = (1 + Real.sqrt (1 + 4 * beta k ^ 2)) / 2
  proximal_step : ∀ k, 1 ≤ k → x k ∈ proximalPoints f (lam k) (y k)
  y_step : ∀ k, 1 ≤ k → y (k + 1) = x k + ((beta k - 1) / beta (k + 1)) • (x k - x (k - 1)) +
    (beta k / beta (k + 1)) • (x k - y k)
