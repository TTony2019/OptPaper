import Mathlib.Tactic
import Foundation.SetValued.Monotone
import Foundation.Hilbert.WeakTopology
import Foundation.Projection.BestApproximation

/-!
# Algorithm `(A_1^ρ)`-`(A_2^ρ)`
-/

open SetValuedOperator
open scoped Pointwise InnerProductSpace

recall innerProductLevelSet
recall isChebyshev_of_nonempty_isClosed_convex

namespace Alvarez2004

variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The hyperplane `H_k` from (2.3). -/
def algorithmHyperplane (v z y : H) (rho : ℝ) : Set H :=
  {x : H | ⟪v, x - z⟫_ℝ = (1 - rho⁻¹) * ⟪v, y - z⟫_ℝ}

/-- One run of Alvarez's relaxed inertial hybrid projection-proximal algorithm. -/
structure RelaxedInertialHPPA
    (A : SetValuedOperator H H) (lam alpha rho : ℕ → ℝ) (sigma : ℝ) where
  x : ℕ → H
  y : ℕ → H
  z : ℕ → H
  v : ℕ → H
  eta : ℕ → H
  /-- The natural-number encoding uses the standard initialization `x⁻¹ = x⁰`.
  Thus the paper's first inertial step is represented by the `k = 0` case. -/
  y_def : ∀ k : ℕ, y k = x k + alpha k • (x k - x (k - 1))
  step_inclusion :
    ∀ k : ℕ,
      v k ∈ (rho k) • A ((rho k)⁻¹ • z k + (1 - (rho k)⁻¹) • y k)
  residual_bound :
    ∀ k : ℕ,
      ‖eta k‖ ≤ sigma *
        max (‖z k - y k‖ / lam k) (‖v k‖)
  equation :
    ∀ k : ℕ,
      (lam k)⁻¹ • (z k - y k) + v k = eta k
  finite_stop_if_zero :
    ∀ k : ℕ, v k = 0 →
      ∀ n : ℕ, k + 1 ≤ n → x n = y k ∧ y n = y k ∧ z n = y k ∧ v n = 0
  update_if_nonzero :
    ∀ k : ℕ, v k ≠ 0 →
      x (k + 1) =
        y k - (⟪v k, y k - z k⟫_ℝ / ‖v k‖ ^ 2) • v k

end Alvarez2004
