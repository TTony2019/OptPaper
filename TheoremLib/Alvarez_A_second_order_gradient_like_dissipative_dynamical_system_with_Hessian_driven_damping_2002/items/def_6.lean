import Mathlib
import TheoremLib.Alvarez_A_second_order_gradient_like_dissipative_dynamical_system_with_Hessian_driven_damping_2002.items.def_4
namespace Alvarez2002
/-- The continuous Newton equation `(CN)`. -/
def IsContinuousNewtonTrajectory {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [CompleteSpace H]
  (x₀ : H) (x : ℝ → H) (Φ : H → ℝ) : Prop :=
  x 0 = x₀ ∧
  ∀ t, t > 0 → fderiv ℝ (gradient Φ) (x t) (deriv x t) + gradient Φ (x t) = 0
end Alvarez2002
