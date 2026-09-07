import Mathlib

/-!
# Algorithm (ACA²)

The approximate version of (CA²), denoted (ACA²), with tolerance ε_n > 0.
Depends on: algo_1 (CA2 structure), ext_def_5 (ε-argmin).

From: H. Attouch, P. Redont, A. Soubeyran (2007).
-/

/-- The Approximate Cognitive Alternating Algorithm (ACA²) on abstract spaces X and Y.

Given objective functions f : X → ℝ, g : Y → ℝ, cost-to-change functions
h : X → X → ℝ, k : Y → Y → ℝ, coupling function c : X → Y → ℝ,
nonnegative parameters α_n, β_n, μ_n, ν_n, tolerance ε_n > 0, and initial points,
the algorithm generates the sequence via alternating ε-argmin steps. -/
structure ACA2 (X Y : Type*) (f : X → ℝ) (g : Y → ℝ)
    (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (α β μ ν : ℕ → ℝ) (ε : ℕ → ℝ) where
  /-- The sequence in X. -/
  x : ℕ → X
  /-- The sequence in Y. -/
  y : ℕ → Y
  /-- Tolerance positivity. -/
  eps_pos (n : ℕ) : ε n > 0
  /-- The x-update: x_{n+1} is an ε_n-approximate argmin.
      f(x_{n+1}) + α_n h(x_n, x_{n+1}) + β_n c(x_{n+1}, y_n)
      ≤ f(ξ) + α_n h(x_n, ξ) + β_n c(ξ, y_n) + ε_n for all ξ. -/
  step_x (n : ℕ) (ξ : X) :
    f (x (n+1)) + α n * h (x n) (x (n+1)) + β n * c (x (n+1)) (y n) ≤
    f ξ + α n * h (x n) ξ + β n * c ξ (y n) + ε n
  /-- The y-update: y_{n+1} is an ε_n-approximate argmin. -/
  step_y (n : ℕ) (η : Y) :
    g (y (n+1)) + μ n * c (x (n+1)) (y (n+1)) + ν n * k (y n) (y (n+1)) ≤
    g η + μ n * c (x (n+1)) η + ν n * k (y n) η + ε n
