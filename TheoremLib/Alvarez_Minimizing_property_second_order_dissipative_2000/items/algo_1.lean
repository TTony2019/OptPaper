import TheoremLib.Alvarez_Minimizing_property_second_order_dissipative_2000.items.ext_def_3
import Foundation.Analysis.ExtendedRealFunctions

namespace Alvarez2000

open scoped InnerProductSpace

/-- Data and update inclusion for the inertial epsilon-proximal method (1.2). -/
structure InertialProximalMethod {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) where
  u : ℕ → H
  eps : ℕ → ℝ
  lam : ℕ → ℝ
  alpha : ℕ → ℝ
  proper : ERealFunction.IsProper f
  closed_epigraph : IsClosed (ERealFunction.epigraph f)
  convex : Convex ℝ (ERealFunction.epigraph f)
  eps_pos : ∀ k, 0 < eps k
  lam_pos : ∀ k, 0 < lam k
  alpha_range : ∀ k, 0 ≤ alpha k ∧ alpha k < 1
  update : ∀ k : ℕ, 0 < k → 0 ∈ (fun p =>
    (lam k)⁻¹ • (u (k + 1) - (1 + alpha k) • u k + alpha k • u (k - 1)) + p) ''
      epsilonSubdifferential f (eps k) (u (k + 1))

end Alvarez2000
