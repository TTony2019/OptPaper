import Mathlib
import Foundation.Convex.ProximalOperator

namespace AbbasDynamical2015

/-- The backward-forward discretization (BF). -/
structure BackwardForwardAlgorithm {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H]
    [CompleteSpace H] (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ ERealFunction.gammaZero H)
    (B : H → H) (mu h : ℝ) where
  mu_pos : 0 < mu
  h_pos : 0 < h
  x : ℕ → H
  y : ℕ → H
  prox_step : ∀ k, x k = ERealFunction.scaledProximityOperator f hf
    ⟨mu, mu_pos⟩ (y k)
  forward_step : ∀ k, y (k + 1) = (1 - h) • y k + h • (x k - mu • B (x k))

/-- Backward-forward iteration with a sequence of relaxation parameters. -/
structure VariableRelaxationBackwardForwardAlgorithm {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ ERealFunction.gammaZero H)
    (B : H → H) (mu : ℝ) (h : ℕ → ℝ) where
  mu_pos : 0 < mu
  x : ℕ → H
  y : ℕ → H
  prox_step : ∀ k, x k = ERealFunction.scaledProximityOperator f hf
    ⟨mu, mu_pos⟩ (y k)
  forward_step : ∀ k, y (k + 1) = (1 - h k) • y k + h k • (x k - mu • B (x k))

end AbbasDynamical2015
