import Mathlib

/-!
# Algorithm (CA²)

Cognitive Alternating Algorithm — the exact version.
From: H. Attouch, P. Redont, A. Soubeyran (2007).
-/

/-- The Cognitive Alternating Algorithm (CA²) on abstract spaces `X` and `Y`.

Given objective functions `f : X → ℝ`, `g : Y → ℝ`, cost-to-change functions
`h : X → X → ℝ`, `k : Y → Y → ℝ`, a coupling function `c : X → Y → ℝ`,
nonnegative parameters `α_n, β_n, μ_n, ν_n`, and an initial point `(x₀, y₀) ∈ X × Y`,
the algorithm generates the sequence via alternating argmin steps. -/
structure CA2 (X Y : Type*) (f : X → ℝ) (g : Y → ℝ)
    (h : X → X → ℝ) (k : Y → Y → ℝ) (c : X → Y → ℝ)
    (α β μ ν : ℕ → ℝ) where
  /-- The sequence in X. -/
  x : ℕ → X
  /-- The sequence in Y. -/
  y : ℕ → Y
  /-- The x-update inequality from the argmin definition:
      f(x_{n+1}) + α_n h(x_n, x_{n+1}) + β_n c(x_{n+1}, y_n) ≤ f(ξ) + α_n h(x_n, ξ) + β_n c(ξ, y_n)
      for all ξ ∈ X. -/
  step_x (n : ℕ) (ξ : X) :
    f (x (n+1)) + α n * h (x n) (x (n+1)) + β n * c (x (n+1)) (y n) ≤
    f ξ + α n * h (x n) ξ + β n * c ξ (y n)
  /-- The y-update inequality from the argmin definition:
      g(y_{n+1}) + μ_n c(x_{n+1}, y_{n+1}) + ν_n k(y_n, y_{n+1}) ≤ g(η) + μ_n c(x_{n+1}, η) + ν_n k(y_n, η)
      for all η ∈ Y. -/
  step_y (n : ℕ) (η : Y) :
    g (y (n+1)) + μ n * c (x (n+1)) (y (n+1)) + ν n * k (y n) (y (n+1)) ≤
    g η + μ n * c (x (n+1)) η + ν n * k (y n) η
