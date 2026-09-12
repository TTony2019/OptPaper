import Mathlib
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.algo_1

namespace Nesterov1983

/-- Exact bibliographic source cited by the paper for its informal first-order
lower-complexity optimality remark. -/
def citedFirstOrderComplexityLowerBoundSource : String :=
  "A. S. Nemirovskii and D. B. Yudin, Complexity of problems and efficiency of optimization methods, Nauka, Moscow, 1979 (Russian)."

/-- The paper attributes its informal first-order lower-complexity optimality
remark to `citedFirstOrderComplexityLowerBoundSource`. -/
theorem firstOrder_complexity_lower_bound_reference :
    citedFirstOrderComplexityLowerBoundSource =
      "A. S. Nemirovskii and D. B. Yudin, Complexity of problems and efficiency of optimization methods, Nauka, Moscow, 1979 (Russian)." := rfl

end Nesterov1983
