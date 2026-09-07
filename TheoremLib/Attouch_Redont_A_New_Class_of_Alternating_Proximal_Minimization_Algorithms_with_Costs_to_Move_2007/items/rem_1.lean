import Mathlib

/-!
# Remark 1: Classical Nash Equilibrium

When α = ν = 0, INE(0, β, μ, 0) reduces to the usual notion of Nash equilibrium:
x̄ ∈ argmin_{ξ} {f(ξ) + β c(ξ, ȳ)} and ȳ ∈ argmin_{η} {g(η) + μ c(x̄, η)}.

Depends on: def_1 (IsINE).

From: H. Attouch, P. Redont, A. Soubeyran (2007).
-/

/-- Inertial Nash Equilibrium (duplicated for self-containment; see def_1). -/
def IsINE {X Y : Type*} (f : X → ℝ) (g : Y → ℝ)
    (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (α β μ ν : ℝ) (xbar : X) (ybar : Y) : Prop :=
  (∀ (ξ : X), f xbar + β * c xbar ybar + α * h xbar xbar ≤ f ξ + β * c ξ ybar + α * h xbar ξ) ∧
  (∀ (η : Y), g ybar + μ * c xbar ybar + ν * k ybar ybar ≤ g η + μ * c xbar η + ν * k ybar η)

/-- Remark 1: When α = ν = 0, INE reduces to the classical Nash equilibrium
with payoff functions F(ξ, η) = f(ξ) + β c(ξ, η) and G(ξ, η) = g(η) + μ c(ξ, η). -/
theorem remark_1_INE_reduces_to_Nash {X Y : Type*} (f : X → ℝ) (g : Y → ℝ)
    (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (β μ : ℝ) (xbar : X) (ybar : Y) :
    IsINE f g h k c 0 β μ 0 xbar ybar ↔
    ((∀ (ξ : X), f xbar + β * c xbar ybar ≤ f ξ + β * c ξ ybar) ∧
     (∀ (η : Y), g ybar + μ * c xbar ybar ≤ g η + μ * c xbar η)) := by
  dsimp [IsINE]
  simp
