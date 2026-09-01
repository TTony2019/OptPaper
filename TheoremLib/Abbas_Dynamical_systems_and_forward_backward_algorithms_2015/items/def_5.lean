import Mathlib
import Foundation.Convex.ProximalOperator

namespace AbbasDynamical2015

/-- Proximal-gradient dynamics (87). -/
structure ProximalGradientDynamics {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (Phi : H → Set.Ioi (⊥ : EReal)) (hPhi : Phi ∈ ERealFunction.gammaZero H)
    (B : H → H) (mu : ℝ) where
  mu_pos : 0 < mu
  x : ℝ → H
  differential_equation : ∀ t,
    deriv x t + x t - ERealFunction.scaledProximityOperator Phi hPhi ⟨mu, mu_pos⟩
      (x t - mu • B (x t)) = 0

end AbbasDynamical2015
