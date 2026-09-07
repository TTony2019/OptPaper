import Mathlib
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_2
namespace Alvarez2002
/-- The Lyapunov energy `E_λ` from (1), with its special value `E`. -/
noncomputable def dinEnergy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (Φ : H → ℝ) (β ell : ℝ) (_hpos : 0 < ell) (x : ℝ → H) (t : ℝ) : ℝ :=
  ell * Φ (x t) + (1 / 2) * ‖deriv x t + β • gradient Φ (x t)‖ ^ 2
noncomputable def dinStandardEnergy {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (Φ : H → ℝ) (α β : ℝ) (hαβ : 0 < α * β + 1) (x : ℝ → H) : ℝ → ℝ :=
  dinEnergy Φ β (α * β + 1) hαβ x
end Alvarez2002
