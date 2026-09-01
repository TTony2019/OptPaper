import Mathlib
import Foundation.Convex.ProximalOperator

namespace AbbasDynamical2015

/-- The backward-forward scheme (39), including its `h = 1` specialization. -/
structure BackwardForwardDiscretization {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ ERealFunction.gammaZero H)
    (B : H → H) (mu h : ℝ) where
  mu_pos : 0 < mu
  h_pos : 0 < h
  x : ℕ → H
  y : ℕ → H
  prox_step : ∀ k, x k = ERealFunction.scaledProximityOperator f hf
    ⟨mu, mu_pos⟩ (y k)
  equation_step : ∀ k, y (k + 1) = (1 - h) • y k + h • (x k - mu • B (x k))

/-- At unit relaxation, (39) is the classical forward-backward iteration. -/
theorem backward_forward_unit_step {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H]
    (f : H → Set.Ioi (⊥ : EReal)) (hf : f ∈ ERealFunction.gammaZero H)
    (B : H → H) (mu : ℝ) (alg : BackwardForwardDiscretization f hf B mu 1) :
    ∀ k, alg.x (k + 1) =
      ERealFunction.scaledProximityOperator f hf ⟨mu, alg.mu_pos⟩
        (alg.x k - mu • B (alg.x k)) := by
  intro k
  calc
    alg.x (k + 1) = ERealFunction.scaledProximityOperator f hf ⟨mu, alg.mu_pos⟩
        (alg.y (k + 1)) := alg.prox_step (k + 1)
    _ = ERealFunction.scaledProximityOperator f hf ⟨mu, alg.mu_pos⟩
        ((1 - (1 : ℝ)) • alg.y k + (1 : ℝ) • (alg.x k - mu • B (alg.x k))) := by
      rw [alg.equation_step]
    _ = ERealFunction.scaledProximityOperator f hf ⟨mu, alg.mu_pos⟩
        (alg.x k - mu • B (alg.x k)) := by simp

end AbbasDynamical2015
