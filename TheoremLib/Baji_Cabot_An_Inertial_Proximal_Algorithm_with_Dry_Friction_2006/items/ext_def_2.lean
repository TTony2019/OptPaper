import Mathlib.Tactic
import Foundation.SetValued.Resolvent

/-!
# Resolvent of a maximal monotone operator
For a maximal monotone operator $A: H \Rightarrow H$ and $\lambda > 0$, the resolvent
of $A$ is defined by $J_\lambda^A := (I + \lambda A)^{-1}$. The resolvent is
single-valued and nonexpansive on $H$.
-/
open SetValuedOperator
open scoped Pointwise
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
/-- The resolvent (proximal mapping) of a set-valued operator `A` with parameter `λ > 0`:
`J_λ^A := (I + λA)^{-1}`, where `(I + λA)(z) = {z + λ • v | v ∈ A(z)}`. -/
recall SetValuedOperator.resolvent
/-- The resolvent of a maximal monotone operator is single-valued.
(This is a theorem; it follows from monotonicity of the operator.) -/
theorem resolvent_single_valued (A : SetValuedOperator H H) (hA : IsMaximalMonotone A)
    (lam : ℝ) (hlam : lam > 0) :
    SetValuedOperator.IsAtMostSingleValued (J[(lam • A)]) := by
  intro x y₁ hy₁ y₂ hy₂
  rw [mem_resolvent_smul_iff] at hy₁ hy₂
  rcases hy₁ with ⟨a₁, ha₁, hx₁⟩
  rcases hy₂ with ⟨a₂, ha₂, hx₂⟩
  have hy_sub : y₁ - y₂ = lam • (a₂ - a₁) := by
    have hy₁_expr : y₁ = x - lam • a₁ := by
      calc
        y₁ = (y₁ + lam • a₁) - lam • a₁ := (add_sub_cancel_right _ _).symm
        _ = x - lam • a₁ := by rw [hx₁]
    have hy₂_expr : y₂ = x - lam • a₂ := by
      calc
        y₂ = (y₂ + lam • a₂) - lam • a₂ := (add_sub_cancel_right _ _).symm
        _ = x - lam • a₂ := by rw [hx₂]
    rw [hy₁_expr, hy₂_expr]
    calc
      (x - lam • a₁) - (x - lam • a₂) = lam • a₂ - lam • a₁ := by abel
      _ = lam • (a₂ - a₁) := by rw [smul_sub]
  have hinner : inner ℝ (a₁ - a₂) (a₂ - a₁) = -‖a₁ - a₂‖ ^ 2 := by
    rw [show a₂ - a₁ = -(a₁ - a₂) by abel, inner_neg_right, real_inner_self_eq_norm_sq]
  have hmono : 0 ≤ inner ℝ (a₁ - a₂) (y₁ - y₂) := hA.1 a₁ ha₁ a₂ ha₂
  rw [hy_sub, real_inner_smul_right, hinner] at hmono
  have hsq : ‖a₁ - a₂‖ ^ 2 = 0 := by
    nlinarith [hlam, sq_nonneg (‖a₁ - a₂‖)]
  have haeq : a₁ = a₂ := by
    exact sub_eq_zero.mp (norm_eq_zero.mp (by nlinarith [norm_nonneg (a₁ - a₂), hsq]))
  exact sub_eq_zero.mp (by simpa [haeq] using hy_sub)
