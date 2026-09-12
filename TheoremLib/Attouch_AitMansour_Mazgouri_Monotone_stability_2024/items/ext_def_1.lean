import Mathlib
import Foundation.Metric.FixedPoint

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-- The point-to-set distance `d(x,C) = inf_{y ∈ C} d(x,y)`, including the
  convention `d(x, ∅) = +∞`. -/
recall Metric.infEDist

/-- The excess `e(C,D) = sup_{x ∈ C} d(x,D)`.  Consequently it is infinite
  when `C` is nonempty and `D` is empty.  Supplied canonically by Foundation. -/
recall excess

/-- The Hausdorff distance `h(C,D) = max {e(C,D), e(D,C)}` in `ℝ≥0∞`, as in
  the paper.  One convention differs: mathlib's `Metric.hausdorffEDist` gives
  `h(∅,∅) = 0`, whereas the paper's Section 2.2 convention makes `h` infinite
  as soon as one of the two sets is empty (`e(∅,D)` is indeed `0`, but
  `e(C,∅) = +∞` for nonempty `C`).  The two agree whenever both sets are
  nonempty. -/
recall Metric.hausdorffEDist

/-- `ε`-approximate fixed points of a *set-valued* map `T : X → Set X`, for
  `ε ≥ 0` (`0 ≤ ε` is part of the membership predicate); Foundation's
  `approximateFixedPoints`.  The paper's `ε-Fix(Γ)` for a single-valued map is
  obtained by reading `T x` as the singleton `{Γ x}`. -/
recall approximateFixedPoints

/-- Exact fixed points: `Fix(T) = {x ∈ X | x ∈ T(x)}`.  Supplied canonically
  by Foundation. -/
recall fixedPoints

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
