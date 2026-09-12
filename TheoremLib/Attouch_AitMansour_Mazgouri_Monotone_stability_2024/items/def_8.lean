import Mathlib
import Foundation.Operator.Distance

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-- The paper's `d_r` distance, retaining the distinct-points condition
  verbatim.  Supplied canonically by Foundation as `ratioDistanceOnBall`. -/
recall ratioDistanceOnBall

/-- The paper's `d_r` of Section 5,
  `d_r(A,B) = sup_{‖u‖,‖v‖ ≤ r, u ≠ v} ‖A u - B v‖ / ‖u - v‖`, supplied
  canonically by Foundation as `ratioDistanceOnBall` and used by Theorem 5.4.
  The asymmetric-looking `‖A u - B v‖` (A at `u`, B at `v`) is the paper's
  own convention.  It is a different object from `def_6` (`D_r`, the
  *unratioed* supremum of `‖A u - B u‖`) and from `def_7`'s `d_{λ,ρ}`.

  Representational deviations inherited from Foundation: the value is the real
  `sSup` of the ratio set, hence `0` when that set is unbounded or empty,
  whereas the paper's `sup` may be `+∞` (consumers carry explicit boundedness
  or upper-bound hypotheses, e.g. `thm_4`'s `hdist`); and the Foundation
  signature's unused argument `_hr : 0 < r`. -/
noncomputable abbrev def_8 {H : Type*} [NormedAddCommGroup H] (r : ℝ) (_hr : 0 < r)
    (A B : H → H) : ℝ :=
  ratioDistanceOnBall r _hr A B

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
