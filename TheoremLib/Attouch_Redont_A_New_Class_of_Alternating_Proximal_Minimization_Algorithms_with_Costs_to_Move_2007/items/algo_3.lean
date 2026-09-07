import Mathlib

/-!
# Joint proximal algorithm (paper Section 3.2)

The paper observes that the alternating CA² updates are coordinate minimizations
of the joint proximal objective below.  This file records that joint objective
and its exact argmin formulation for the finite-valued specialization used by
the other files in this item.

From: H. Attouch, P. Redont, A. Soubeyran (2007), equation (3.2).
-/

/-- The joint proximal objective minimized at iteration `n` in equation (3.2). -/
def jointProximalObjective {X Y : Type*}
    (f : X → ℝ) (g : Y → ℝ) (h : X → X → ℝ) (k : Y → Y → ℝ)
    (c : X → Y → ℝ) (α β μ ν : ℕ → ℝ)
    (x : ℕ → X) (y : ℕ → Y) (n : ℕ) (ξ : X) (η : Y) : ℝ :=
  μ n * f ξ + β n * g η + (μ n * β n) * c ξ η +
    μ n * α n * h (x n) ξ + β n * ν n * k (y n) η

/-- Exact joint proximal minimization associated with equation (3.2). -/
structure JointProximalAlgorithm (X Y : Type*)
    (f : X → ℝ) (g : Y → ℝ) (h : X → X → ℝ) (k : Y → Y → ℝ)
    (c : X → Y → ℝ) (α β μ ν : ℕ → ℝ) where
  x : ℕ → X
  y : ℕ → Y
  step (n : ℕ) (ξ : X) (η : Y) :
    jointProximalObjective f g h k c α β μ ν x y n (x (n+1)) (y (n+1)) ≤
      jointProximalObjective f g h k c α β μ ν x y n ξ η
