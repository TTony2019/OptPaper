import Mathlib.Tactic

/-!
# Parameter assumptions (1.3)-(1.6)
-/

open Filter
open scoped Topology

namespace Alvarez2004

variable {H : Type _} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The parameter hypotheses used in Theorem 2.2(i), namely (1.4)-(1.6).
The lower bound on `lam` from (1.3) is intentionally absent: it is only
needed for the residual and weak-convergence conclusions in part (ii). -/
structure ParameterAssumptionsPartI (x : ℕ → H) where
  lam : ℕ → ℝ
  alpha : ℕ → ℝ
  rho : ℕ → ℝ
  lam_pos : ∀ k : ℕ, 0 < lam k
  alpha_mem : ∀ k : ℕ, 0 ≤ alpha k ∧ alpha k < 1
  alpha_upper : ∃ alpha0 : ℝ, alpha0 < 1 ∧ ∀ k : ℕ, alpha k ≤ alpha0
  alpha_summable : Summable fun k : ℕ ↦ alpha k * ‖x k - x (k - 1)‖ ^ 2
  rho_lower : ∃ R1 : ℝ, 0 < R1 ∧ ∀ k : ℕ, R1 ≤ rho k
  rho_upper : ∃ R2 : ℝ, R2 < 2 ∧ ∀ k : ℕ, rho k ≤ R2

/-- The full parameter hypotheses (1.3)-(1.6), used for Theorem 2.2(ii)
and Theorem 3.1. -/
structure ParameterAssumptions (x : ℕ → H) where
  lam : ℕ → ℝ
  alpha : ℕ → ℝ
  rho : ℕ → ℝ
  lam_lower : ∃ lam0 : ℝ, 0 < lam0 ∧ ∀ k : ℕ, lam0 ≤ lam k
  alpha_mem : ∀ k : ℕ, 0 ≤ alpha k ∧ alpha k < 1
  alpha_upper : ∃ alpha0 : ℝ, alpha0 < 1 ∧ ∀ k : ℕ, alpha k ≤ alpha0
  alpha_summable : Summable fun k : ℕ ↦ alpha k * ‖x k - x (k - 1)‖ ^ 2
  rho_lower : ∃ R1 : ℝ, 0 < R1 ∧ ∀ k : ℕ, R1 ≤ rho k
  rho_upper : ∃ R2 : ℝ, R2 < 2 ∧ ∀ k : ℕ, rho k ≤ R2

noncomputable def ParameterAssumptions.partI {x : ℕ → H} (p : ParameterAssumptions x) :
    ParameterAssumptionsPartI x := by
  let lam0 := Classical.choose p.lam_lower
  have hlam0 := Classical.choose_spec p.lam_lower
  exact
    { lam := p.lam
      alpha := p.alpha
      rho := p.rho
      lam_pos := fun k => lt_of_lt_of_le hlam0.1 (hlam0.2 k)
      alpha_mem := p.alpha_mem
      alpha_upper := p.alpha_upper
      alpha_summable := p.alpha_summable
      rho_lower := p.rho_lower
      rho_upper := p.rho_upper }

end Alvarez2004
