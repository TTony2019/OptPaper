import Mathlib
import Foundation.Operator.Linear
namespace Alvarez2002
open scoped RealInnerProductSpace
/-- Strong monotonicity of a gradient on every bounded ball. -/
def StronglyMonotoneOnBoundedSubsets (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (G : H → H) : Prop := ∀ R : ℝ, 0 < R → ∃ c : ℝ, 0 < c ∧ ∀ x y : H,
  max ‖x‖ ‖y‖ < R → c * ‖x - y‖ ^ 2 ≤ ⟪G x - G y, x - y⟫
end Alvarez2002
