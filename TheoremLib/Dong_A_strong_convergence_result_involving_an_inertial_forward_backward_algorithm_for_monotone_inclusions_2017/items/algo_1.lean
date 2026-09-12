import Mathlib.Tactic
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.def_2
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.def_4
import TheoremLib.Dong_A_strong_convergence_result_involving_an_inertial_forward_backward_algorithm_for_monotone_inclusions_2017.items.ext_def_1
import Foundation.SetValued.Resolvent
import Foundation.Projection.BestApproximation

/-! Iterative method (3.1). -/

open SetValuedOperator
open scoped InnerProductSpace
open scoped Pointwise

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

def inertialForwardBackwardC (x z : ℕ → H) (inertia : ℕ → ℝ) (n : ℕ) : Set H :=
  {u | ‖z n - u‖ ^ 2 ≤ ‖x n - u‖ ^ 2 -
    2 * inertia n * inner ℝ (x n - u) (x (n - 1) - x n) +
      inertia n ^ 2 * ‖x (n - 1) - x n‖ ^ 2}

def inertialForwardBackwardQ (x : ℕ → H) (x0 : H) (n : ℕ) : Set H :=
  {u | inner ℝ (u - x n) (x0 - x n) ≤ 0}

structure InertialForwardBackward (A : H → H) (B : SetValuedOperator H H) where
  inertia : ℕ → ℝ
  stepSize : ℕ → ℝ
  x : ℕ → H
  y : ℕ → H
  z : ℕ → H
  x0 : H
  x1 : H
  initial_zero : x 0 = x0
  initial_one : x 1 = x1
  stepSize_pos : ∀ n, 1 ≤ n → 0 < stepSize n
  inertial_step : ∀ n, 1 ≤ n →
    y n = x n + inertia n • (x n - x (n - 1))
  resolvent_step : ∀ n, 1 ≤ n →
    z n ∈ J[(stepSize n • B)] (y n - stepSize n • A (y n))
  projection_step : ∀ n, 1 ≤ n →
    x (n + 1) ∈ setValuedProjector
      (inertialForwardBackwardC x z inertia n ∩ inertialForwardBackwardQ x x0 n) x0

/-- The next iterate prescribed by (3.1), once its two defining half-spaces are Chebyshev. -/
noncomputable def inertialForwardBackwardNext (x z : ℕ → H) (inertia : ℕ → ℝ) (x0 : H)
    (n : ℕ) (h : IsChebyshev
      (inertialForwardBackwardC x z inertia n ∩ inertialForwardBackwardQ x x0 n)) : H :=
  projectionPoint (inertialForwardBackwardC x z inertia n ∩ inertialForwardBackwardQ x x0 n) h x0
