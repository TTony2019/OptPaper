import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_3
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_4
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.lem_3
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.cor_5
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.algo_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_3
import Foundation.Analysis.ExtendedRealFunctions

open ERealFunction

/-- The Section 3 variant, where proximal points are computed only by criterion A'.

As in the exact algorithm record, this Lean interface specializes the paper's
extended-real objective to a finite-valued `f : H → ℝ`; `approximate_witness`
records the attainment needed by the quantitative proof. -/
structure InexactProximalPointAlgorithm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (ε : ℕ → ℝ) where
  A : ℝ
  x : ℕ → H
  y : ℕ → H
  p : ℕ → H
  nu : ℕ → H
  lam : ℕ → ℝ
  alpha : ℕ → ℝ
  curvature : ℕ → ℝ
  /-- Error tolerances are magnitudes, hence nonnegative. -/
  epsilon_nonneg : ∀ k, 0 ≤ ε k
  A_pos : 0 < A
  f_proper : ERealFunction.IsProper (fun z => (f z : EReal))
  f_lowerSemicontinuous : LowerSemicontinuous f
  f_convex : ConvexOn ℝ Set.univ f
  x0_feasible : IsFeasible (fun z => (f z : EReal)) (x 0)
  lam_pos : ∀ k, 0 < lam k
  alpha_eq : ∀ k, alpha k ^ 2 = (1 - alpha k) * curvature k * lam k
  /-- The inexact method keeps the same positive-root choice (2.23) as Section 2. -/
  alpha_formula : ∀ k, alpha k =
    (Real.sqrt ((curvature k * lam k) ^ 2 + 4 * curvature k * lam k) -
      curvature k * lam k) / 2
  /-- Criterion A' is used with the positive root from (2.23). -/
  alpha_pos : ∀ k, 0 < alpha k
  alpha_mem : ∀ k, alpha k ∈ Set.Ico (0 : ℝ) 1
  initial_center : nu 0 = x 0
  initial_curvature : curvature 0 = A
  y_step : ∀ k, y k = (1 - alpha k) • x k + alpha k • nu k
  approximate_step : ∀ k, IsApproximationMinimizer f (lam k) (ε k) (y k) (x (k + 1))
  /-- Attainment of the residual bound, needed by the proof of Lemma 3.1. -/
  approximate_witness : ∀ k,
    IsApproximationMinimizerWitness f (lam k) (ε k) (y k) (x (k + 1))
  proximal_step : ∀ k, p k ∈ proximalPoints f (lam k) (y k)
  nu_step : ∀ k, nu (k + 1) = nu k + (1 / alpha k) • (x (k + 1) - y k)
  curvature_step : ∀ k, curvature (k + 1) = (1 - alpha k) * curvature k

/-- Theorem 3.1: accumulated inexactness obeys recurrence (3.10).

The estimate-minimum and strong-convexity steps from Lemma 3.1/Corollary 3.2
are explicit premises here; this keeps the recurrence theorem independent of a
particular encoding of the estimate-quadratic minimum. -/
theorem inexact_error_recurrence {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (ε : ℕ → ℝ) (alg : InexactProximalPointAlgorithm f ε)
    (δ φStar : ℕ → ℝ) (hδ : δ 0 = 0)
    (hrec : ∀ k, δ (k + 1) = (1 - alg.alpha k) * δ k +
      ε k ^ 2 / (2 * alg.lam k))
    (hbase : f (alg.x 0) = φStar 0)
    (hphi_step : ∀ k, φStar (k + 1) + (1 - alg.alpha k) * δ k ≥
      _root_.proximalObjective f (alg.lam k) (alg.y k) (alg.p k))
    (hstrong : ∀ k, IsStronglyConvexWith
      (_root_.proximalObjective f (alg.lam k) (alg.y k)) (1 / alg.lam k))
    :
    ∀ k, f (alg.x k) ≤ φStar k + δ k := by
  intro k
  induction k with
  | zero =>
      simpa [hδ] using le_of_eq hbase
  | succ k ih =>
      have hwitness : ∃ w : H, w ∈ subdifferential
          (fun z => (_root_.proximalObjective f (alg.lam k) (alg.y k) z : EReal))
          (alg.x (k + 1)) ∧ ‖w‖ ≤ ε k / alg.lam k := by
        exact (alg.approximate_witness k).2
      have hgap := approximation_minimizer_gap f (alg.lam_pos k) alg.f_convex
        (alg.proximal_step k) (hstrong k) hwitness
      have hgap_upper := hgap.2
      have hstar := hphi_step k
      have hprox_bound : _root_.proximalObjective f (alg.lam k) (alg.y k) (alg.x (k + 1)) ≤
          φStar (k + 1) + (1 - alg.alpha k) * δ k + ε k ^ 2 / (2 * alg.lam k) := by
        linarith
      have hprox_succ : _root_.proximalObjective f (alg.lam k) (alg.y k) (alg.x (k + 1)) ≤
          φStar (k + 1) + δ (k + 1) := by
        rw [hrec k]
        linarith
      have hden_pos : 0 < 2 * alg.lam k := by
        exact mul_pos (by norm_num) (alg.lam_pos k)
      have hquad : 0 ≤ ‖alg.x (k + 1) - alg.y k‖ ^ 2 / (2 * alg.lam k) :=
        div_nonneg (sq_nonneg _) (le_of_lt hden_pos)
      have hf_le_prox : f (alg.x (k + 1)) ≤
          _root_.proximalObjective f (alg.lam k) (alg.y k) (alg.x (k + 1)) := by
        rw [_root_.proximalObjective]
        linarith
      exact hf_le_prox.trans hprox_succ
