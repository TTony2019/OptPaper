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
  if n = 0 then Set.univ else
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
  projection_step : ∀ n,
    x (n + 1) ∈ setValuedProjector
      (inertialForwardBackwardC x z inertia n ∩ inertialForwardBackwardQ x x0 n) x0

/-- The zero-th projection initializes the iteration at `x₁ = x₀`, since `C₀ = Q₀ = H`. -/
theorem InertialForwardBackward.initial_one_eq_x0
    {A : H → H} {B : SetValuedOperator H H}
    (alg : InertialForwardBackward A B) : alg.x 1 = alg.x0 := by
  have hp := (mem_setValuedProjector_iff.mp (alg.projection_step 0))
  have hx0mem : alg.x0 ∈
      inertialForwardBackwardC alg.x alg.z alg.inertia 0 ∩
        inertialForwardBackwardQ alg.x alg.x0 0 := by
    simp [inertialForwardBackwardC, inertialForwardBackwardQ, alg.initial_zero]
  have hinf := Metric.infDist_le_dist_of_mem (x := alg.x0) hx0mem
  have hdist : dist alg.x0 (alg.x 1) = 0 := by
    rw [hp.2]
    exact le_antisymm (by simpa using hinf) (Metric.infDist_nonneg)
  exact (dist_eq_zero.mp hdist).symm

/-- The next iterate prescribed by (3.1), once its two defining half-spaces are Chebyshev. -/
noncomputable def inertialForwardBackwardNext (x z : ℕ → H) (inertia : ℕ → ℝ) (x0 : H)
    (n : ℕ) (h : IsChebyshev
      (inertialForwardBackwardC x z inertia n ∩ inertialForwardBackwardQ x x0 n)) : H :=
  projectionPoint (inertialForwardBackwardC x z inertia n ∩ inertialForwardBackwardQ x x0 n) h x0
