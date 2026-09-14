import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_3
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.thm_1

open scoped InnerProductSpace

/-- Corollary 2.1, obtained by choosing `y = (1-α)x + αν` in Theorem 2.1. -/
theorem estimateQuadratic_minimum_lower_bound_choice {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (params : EstimateQuadraticParameters)
    (k : ℕ) (x : H) (hconvex : ConvexOn ℝ Set.univ f)
    (hlam : 0 < params.lam k) (hα : params.alpha k ∈ Set.Ico (0 : ℝ) 1)
    (hA : 0 < params.curvature (k + 1)) (hx : f x ≤ params.phi_star k)
    (hp : params.p k ∈ proximalPoints f (params.lam k) (params.y k))
    (hupdate : ∀ z, params.phi (k + 1) z =
      (1 - params.alpha k) * params.phi k z + params.alpha k *
        (f (params.p k) + inner ℝ ((1 / params.lam k) •
          (params.y k - params.p k)) (z - params.p k)))
    (hy : params.y k = (1 - params.alpha k) • x + params.alpha k • params.nu k) :
    params.phi_star (k + 1) ≥ f (params.p k) +
      (1 / (2 * params.lam k)) *
        (2 - params.alpha k ^ 2 /
          (params.curvature (k + 1) * params.lam k)) *
        ‖params.y k - params.p k‖ ^ 2 := by
  have hmain := estimateQuadratic_minimum_lower_bound f params k x
    hconvex hlam hα hA hx hp hupdate
  simpa [hy] using hmain
