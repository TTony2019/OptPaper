import Mathlib
import Foundation.SetValued.Yosida

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

open scoped Pointwise

/-- For a perturbed maximal monotone family `A : Λ → H ⇉ H`, the paper's
  `A_λ(., μ) = (1 / λ) (I - J_λ^A(., μ))`.  The right-hand side is
  Foundation's canonical Yosida regularization of the member `A μ`. -/
theorem def_5 {Λ H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (A : Λ → SetValuedOperator H H)
    (hA : ∀ μ, (A μ).IsMaximalMonotone) (lam : ERealFunction.PosReal) (μ : Λ) :
      SetValuedOperator.yosidaRegularization (A μ) (hA μ) (lam : ℝ) lam.2 =
        fun x => (lam : ℝ)⁻¹ •
          (x - SetValuedOperator.resolventMap (A μ) (hA μ) (lam : ℝ) lam.2 x) := rfl

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
