import TheoremLib.Burachik_Svaiter_Robustness_HPE_2001.items.def_1

open scoped InnerProductSpace

namespace BurachikSvaiterRobustnessHPE2001

/-- Algorithm 2.1 data and its inexact HPE conditions. -/
structure HPEIterates (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (T : SetValuedOperator H H) where
  x : ℕ → H
  y : ℕ → H
  v : ℕ → H
  c : ℕ → ℝ
  δ : ℕ → ℝ
  σ : ℕ → ℝ
  α : ℕ → ℝ
  ε : ℕ → ℝ
  c_pos : ∀ k, 0 < c k
  δ_nonneg : ∀ k, 0 ≤ δ k
  σ_nonneg : ∀ k, 0 ≤ σ k
  α_nonneg : ∀ k, 0 ≤ α k
  ε_nonneg : ∀ k, 0 ≤ ε k
  enlargement_mem : ∀ k, v k ∈ epsilonEnlargement T (ε k) (ε_nonneg k) (y k)
  residual_bound : ∀ k,
    ‖c k • v k + y k - x k‖ ^ 2 + 2 * c k * ε k ≤
      δ k + (σ k) ^ 2 * ‖y k - x k‖ ^ 2
  update_error : ∀ k, ‖x (k + 1) - (x k - c k • v k)‖ ≤ α k
  summable_delta : Summable δ
  summable_alpha : Summable α
  sigma_bound : ∃ σbar, 0 < σbar ∧ σbar < 1 ∧ ∀ k, 0 < σ k ∧ σ k ≤ σbar
  c_lower_bound : ∃ cbar, 0 < cbar ∧ ∀ k, cbar ≤ c k

end BurachikSvaiterRobustnessHPE2001
