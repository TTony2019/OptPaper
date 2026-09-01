import Mathlib
import Foundation.FixedPoint.FAlpha

/-!
# Inertial Iteration Framework

The inertial iteration scheme introduced by Maingé (2007): given a family of operators
`(T_n)` and a target set `S`, the iteration is

`x_{n+1} = T_n (x_n + θ_n (x_n - x_{n-1}))`

where the inertial parameter `θ_n ∈ [0, 1)` adds momentum from the previous step.

The operators must satisfy three conditions:
- (C1): Each `T_n` belongs to the class `ℱ_α` for some `α ∈ (0, 1)`.
- (C2): The target set `S` is contained in `Fix(T_n)` for all `n`.
- (C3): A demiclosedness-type condition: weak cluster points of sequences with
  vanishing residuals belong to `S`.

Reference: P.-E. Maingé, "Inertial Iterative Process for Fixed Points of Certain
Quasi-nonexpansive Mappings", Set-Valued Anal. 15 (2007), 67–79.
-/

open Set
open Filter
open Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- Configuration for the inertial iteration scheme (1.1): a family of operators
`(T_n)` and a target set `S` satisfying conditions (C1)–(C3). -/
structure InertialIterationConfig (α : ℝ) where
  /-- `α ∈ (0, 1)` as required by condition (C1). -/
  hα : α ∈ Set.Ioo (0 : ℝ) 1
  /-- The family of operators. -/
  T : ℕ → H → H
  /-- The target set (nonempty). -/
  S : Set H
  /-- `S` is nonempty. -/
  hS_nonempty : S.Nonempty
  /-- (C1): Each `T_n` belongs to `ℱ_α`. -/
  hC1 : ∀ n, IsInFAlpha α (T n)
  /-- (C2): For all `n`, `S ⊆ Fix(T_n)`. -/
  hC2 : ∀ n, S ⊆ Function.fixedPoints (T n)
  /-- (C3): Demiclosedness-type condition: if a sequence `(ξ_n)` has a weak cluster
  point `ξ∞` and `ξ_n - T_n(ξ_n) → 0` strongly, then `ξ∞ ∈ S`. -/
  hC3 : ∀ (ξ : ℕ → H) (ξ_limit : H),
    (∃ (φ : ℕ → ℕ), StrictMono φ ∧
      Tendsto (fun k => toWeakSpace ℝ H (ξ (φ k))) atTop (𝓝 (toWeakSpace ℝ H ξ_limit))) →
    Tendsto (fun n => ξ n - T n (ξ n)) atTop (𝓝 (0 : H)) →
    ξ_limit ∈ S

/-- The inertial iteration scheme (1.1):
`x_{n+1} = T_n (x_n + θ_n (x_n - x_{n-1}))` for all `n ≥ 1`,
where `θ_n ∈ [0, 1)`. -/
def isInertialIteration (T : ℕ → H → H) (θ : ℕ → ℝ) (x : ℕ → H) : Prop :=
  (∀ n, θ n ∈ Set.Ico (0 : ℝ) 1) ∧
  ∀ n, n ≥ 1 → x (n + 1) = T n (x n + (θ n) • (x n - x (n - 1)))

/-! Source item: Attouch_Convergence_of_a_Relaxed_Inertial_Forward_Backward_Algorithm_for
_Structured_Monotone_Inclusions_2019 items/lem_3 -/

/-- A lower bound for the norm of the inertial displacement `a - r • b` for `0 ≤ r`:
`(1 - r) ^ 2 * ‖b‖ ^ 2 + (1 - r) * (‖a‖ ^ 2 - ‖b‖ ^ 2) ≤ ‖a - r • b‖ ^ 2`.

The algebraic core of inertial energy estimates. -/
theorem norm_inertial_lower {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (a b : H) (r : ℝ) (hr : 0 ≤ r) :
    (1 - r) ^ 2 * ‖b‖ ^ 2 + (1 - r) * (‖a‖ ^ 2 - ‖b‖ ^ 2) ≤ ‖a - r • b‖ ^ 2 := by
  have hsplit : a - r • b = (a - b) + (1 - r) • b := by
    module
  have hsum : a = (a - b) + b := by
    module
  have hfirst :
      ‖a - r • b‖ ^ 2 = ‖a - b‖ ^ 2 + 2 * (1 - r) * inner ℝ (a - b) b +
        (1 - r) ^ 2 * ‖b‖ ^ 2 := by
    rw [hsplit, norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs]
    rw [mul_pow, sq_abs]
    ring
  have hsecond :
      ‖a‖ ^ 2 = ‖a - b‖ ^ 2 + 2 * inner ℝ (a - b) b + ‖b‖ ^ 2 := by
    nth_rewrite 1 [hsum]
    exact norm_add_sq_real _ _
  have hnonneg : 0 ≤ r * ‖a - b‖ ^ 2 :=
    mul_nonneg hr (sq_nonneg _)
  nlinarith [hfirst, hsecond]
