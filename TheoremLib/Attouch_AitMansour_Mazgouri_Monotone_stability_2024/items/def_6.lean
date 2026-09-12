import Mathlib
import Foundation.Operator.Distance

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-- The paper's `D_r` (Section 5): the supremal discrepancy on the closed ball
  of radius `r`.  Supplied canonically by Foundation as
  `supDiscrepancyOnBall`. -/
recall supDiscrepancyOnBall

/-- The paper's `D_r` of Section 5, `D_r(A,B) = sup_{‖u‖ ≤ r} ‖A u - B u‖`,
  supplied canonically by Foundation as `supDiscrepancyOnBall`.  This is the
  distance used by Theorem 5.1; it is *not* the ratio distance `d_r` of
  `def_8` (nor the resolvent distance `d_{λ,ρ}` of `def_7`), despite the
  Foundation docstring's "`d_r`-type" wording.

  Two representational deviations inherited from Foundation, which the paper
  user must keep in mind: the value is the real `sSup` of the discrepancy set,
  hence `0` when that set is unbounded or empty, whereas the paper's `sup` may
  be `+∞` (consumers carry an explicit boundedness hypothesis, e.g. `cor_4`'s
  `hbdd`); and the argument `_hr : 0 < r` demanded by the Foundation signature
  is unused by the definition, `r` entering only through the ball. -/
noncomputable abbrev def_6 {H : Type*} [NormedAddCommGroup H] (r : ℝ) (_hr : 0 < r)
    (A B : H → H) : ℝ :=
  supDiscrepancyOnBall r _hr A B

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
