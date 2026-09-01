import Mathlib

namespace AttouchAdlyDryFrictionDynamics2023

/-- Time scaling `y(s)=z(τ(s))`. -/
def timeScaledTrajectory {H : Type*} (z : ℝ → H) (τ : ℝ → ℝ) : ℝ → H := fun s => z (τ s)

def IsIncreasingC1TimeScale (τ dτ : ℝ → ℝ) : Prop :=
  StrictMono τ ∧ ∀ s, HasDerivAt τ (dτ s) s

/-- The weighted-average trajectory satisfies `ẋ + τ̇⁻¹ • (x-y) = 0` and `x(s₀)=y(s₀)`. -/
def IsWeightedAverage {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (τ dτ : ℝ → ℝ) (x y dx : ℝ → H) (s₀ : ℝ) : Prop :=
  IsIncreasingC1TimeScale τ dτ ∧ x s₀ = y s₀ ∧
    ∀ s ∈ Set.Ici s₀, HasDerivAt x (dx s) s ∧ dx s + (dτ s)⁻¹ • (x s - y s) = 0

end AttouchAdlyDryFrictionDynamics2023
