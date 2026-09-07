import Mathlib

/-!
# Definition 1.1: Inertial Nash Equilibrium (INE)

Given nonnegative constants α, β, μ, ν, an inertial Nash equilibrium INE(α, β, μ, ν)
is a couple (x̄, ȳ) ∈ X × Y satisfying the coupled argmin conditions.

From: H. Attouch, P. Redont, A. Soubeyran (2007).
-/

open Set

/-- An Inertial Nash Equilibrium INE(α, β, μ, ν) on abstract spaces X, Y.

Given objective functions f, g, cost to change h, k, coupling function c, and
nonnegative parameters α, β, μ, ν, a point (x̄, ȳ) ∈ X × Y is an INE(α, β, μ, ν) if:
- x̄ ∈ argmin_{ξ∈X} {f(ξ) + β c(ξ, ȳ) + α h(x̄, ξ)}
- ȳ ∈ argmin_{η∈Y} {g(η) + μ c(x̄, η) + ν k(ȳ, η)} -/
def IsINE {X Y : Type*} (f : X → ℝ) (g : Y → ℝ)
    (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (α β μ ν : ℝ) (xbar : X) (ybar : Y) : Prop :=
  (∀ (ξ : X), f xbar + β * c xbar ybar + α * h xbar xbar ≤ f ξ + β * c ξ ybar + α * h xbar ξ) ∧
  (∀ (η : Y), g ybar + μ * c xbar ybar + ν * k ybar ybar ≤ g η + μ * c xbar η + ν * k ybar η)

/-- The set of Inertial Nash Equilibria INE(α, β, μ, ν). -/
def INESet {X Y : Type*} (f : X → ℝ) (g : Y → ℝ)
    (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (α β μ ν : ℝ) : Set (X × Y) :=
  {p | IsINE f g h k c α β μ ν p.1 p.2}
