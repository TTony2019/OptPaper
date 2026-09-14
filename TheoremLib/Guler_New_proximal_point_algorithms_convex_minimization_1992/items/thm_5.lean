import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_2
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_3
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.lem_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.thm_4
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_4

open ERealFunction

/-- Theorem 3.2: rate estimate for the inexact proximal point algorithm. -/
theorem inexact_proximal_global_rate {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (f : H → ℝ) (ε : ℕ → ℝ)
    (alg : InexactProximalPointAlgorithm f ε) (δ : ℕ → ℝ) (z : H) (k : ℕ)
    (hδ : δ 0 = 0)
    (hrec : ∀ i, δ (i + 1) = (1 - alg.alpha i) * δ i + ε i ^ 2 / (2 * alg.lam i))
    (φStar : ℕ → ℝ)
    (hbase : f (alg.x 0) = φStar 0)
    (hphi_step : ∀ i, φStar (i + 1) + (1 - alg.alpha i) * δ i ≥
      _root_.proximalObjective f (alg.lam i) (alg.y i) (alg.p i))
    (hstrong : ∀ i, IsStronglyConvexWith
      (_root_.proximalObjective f (alg.lam i) (alg.y i)) (1 / alg.lam i))
    (hphi_min : ∀ i w, φStar i ≤
      estimateQuadratic f alg.A (alg.x 0) alg.alpha alg.lam alg.y alg.p i w) :
    f (alg.x k) - f z ≤ betaSequence alg.alpha k *
      (estimateQuadratic f alg.A (alg.x 0) alg.alpha alg.lam alg.y alg.p 0 z - f z) + δ k := by
  let φ := estimateQuadratic f alg.A (alg.x 0) alg.alpha alg.lam alg.y alg.p
  have hstep : ∀ i w, φ (i + 1) w - f w ≤
      (1 - alg.alpha i) * (φ i w - f w) := by
    intro i w
    simpa [φ] using estimateQuadratic_step_le f alg.A (alg.x 0) alg.alpha alg.lam alg.y alg.p
      alg.f_convex alg.alpha_mem alg.proximal_step i w
  have hbeta : φ k z - f z ≤ betaSequence alg.alpha k * (φ 0 z - f z) :=
    betaSequence_estimate alg.alpha φ f hstep alg.alpha_mem k z
  have herror : ∀ i, f (alg.x i) ≤ φStar i + δ i :=
    inexact_error_recurrence f ε alg δ φStar hδ hrec hbase hphi_step hstrong
  have hfx_le_phiδ : f (alg.x k) ≤ φ k z + δ k :=
    (herror k).trans (by
      simpa [add_comm] using add_le_add_right (hphi_min k z) (δ k))
  calc
    f (alg.x k) - f z ≤ (φ k z + δ k) - f z := sub_le_sub_right hfx_le_phiδ (f z)
    _ = (φ k z - f z) + δ k := by ring
    _ ≤ betaSequence alg.alpha k * (φ 0 z - f z) + δ k := by
      simpa [add_comm] using add_le_add_right hbeta (δ k)
    _ = betaSequence alg.alpha k *
        (estimateQuadratic f alg.A (alg.x 0) alg.alpha alg.lam alg.y alg.p 0 z - f z) + δ k := by
      rfl
