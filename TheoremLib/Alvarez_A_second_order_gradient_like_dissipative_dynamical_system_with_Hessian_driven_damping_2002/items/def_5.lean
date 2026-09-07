import Mathlib
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_4
namespace Alvarez2002
/-- The singularly perturbed system `(ε-DIN)`. -/
def IsEpsilonDINTrajectory {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H] (ε : ℝ) (Φ : H → ℝ) (x₀ v₀ : H) (x : ℝ → H) : Prop :=
  0 < ε ∧ x 0 = x₀ ∧ deriv x 0 = v₀ ∧
  ∀ t, t > 0 → ε • deriv (deriv x) t
  + fderiv ℝ (gradient Φ) (x t) (deriv x t) + (gradient Φ) (x t) = 0
end Alvarez2002
