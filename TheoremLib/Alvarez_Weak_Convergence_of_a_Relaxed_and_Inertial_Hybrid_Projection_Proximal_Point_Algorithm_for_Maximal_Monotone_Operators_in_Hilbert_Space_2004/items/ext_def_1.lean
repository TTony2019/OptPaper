import Mathlib.Tactic
import Foundation.SetValued.Yosida
import TheoremLib.Alvarez_Weak_Convergence_of_a_Relaxed_and_Inertial_Hybrid_Projection_Proximal_Point_Algorithm_for_Maximal_Monotone_Operators_in_Hilbert_Space_2004.items.def_1

/-!
# Yosida approximation of a maximal monotone operator
-/

open SetValuedOperator
open scoped Pointwise

namespace Alvarez2004

variable {H : Type _} [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- The Yosida approximation `A_λ = λ⁻¹(I - J_λ^A)`, represented as a set-valued
operator because Foundation's resolvent is set-valued. -/
def yosidaApproximation (A : SetValuedOperator H H) (lam : ℝ) : SetValuedOperator H H :=
  fun x : H ↦ {u : H | ∃ y ∈ J[(lam • A)] x, u = lam⁻¹ • (x - y)}

/-- Membership form of the Yosida approximation definition. -/
theorem mem_yosidaApproximation_iff
    (A : SetValuedOperator H H) (lam : ℝ) (x u : H) :
    u ∈ yosidaApproximation A lam x ↔
      ∃ y ∈ J[(lam • A)] x, u = lam⁻¹ • (x - y) := by
  rfl

/-- If `xi = x - J_λ^A x`, then `xi / λ ∈ A (x - xi)`. -/
theorem yosida_resolvent_equiv
    (A : SetValuedOperator H H) {lam : ℝ} (hlam : lam ≠ 0)
    {x y xi : H}
    (hy : y ∈ J[(lam • A)] x)
    (hxi : xi = x - y) :
    lam⁻¹ • xi ∈ A (x - xi) := by
  rw [SetValuedOperator.mem_resolvent_smul_iff] at hy
  dsimp [SetValuedOperator.identityAddScaled] at hy
  rcases hy with ⟨a, ha, hx_eq⟩
  have hxi' : xi = lam • a := by
    rw [hxi, ← hx_eq]
    abel
  have ha_eq : lam⁻¹ • xi = a := by
    rw [hxi']
    calc
      lam⁻¹ • (lam • a) = (lam⁻¹ * lam) • a := by rw [mul_smul]
      _ = a := by
        simp [hlam]
  have hxy : x - xi = y := by
    rw [hxi]
    abel
  rw [hxy]
  rw [ha_eq]
  exact ha

end Alvarez2004
