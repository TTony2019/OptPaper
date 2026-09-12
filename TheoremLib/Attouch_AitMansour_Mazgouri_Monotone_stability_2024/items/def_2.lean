import Mathlib
import Foundation.Convex.StronglyConvex

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-- The paper's real-valued strong convexity is the readback of Foundation's
  EReal-valued `IsStronglyConvexWith` under the pointwise `EReal` lift; see
  `isStronglyConvexWith_iff_real_jensen`.  The paper-local real forms below are
  kept verbatim because several proofs in the paper module destructure them
  (and `ConvexOn` is Foundation's canonical convexity notion). -/
recall IsStronglyConvexWith

/-- A function f:H→ℝ is convex if f(tx+(1-t)y)≤tf(x)+(1-t)f(y) for all x,y∈H and t∈[0,1]. -/
def IsConvex {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] (f : H → ℝ) : Prop :=
  ∀ x y : H, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f (t • x + (1 - t) • y) ≤ t * f x + (1 - t) * f y

/-- A function f:H→ℝ is δ-strongly convex (δ>0) if
    f(tx+(1-t)y)≤tf(x)+(1-t)f(y)-(δ/2)t(1-t)‖x-y‖² for all x,y∈H and t∈[0,1].

  Deviation: the paper states `δ > 0` as a separate hypothesis, here it is
  bundled into the definition (so the predicate is simply false for `δ ≤ 0`). -/
def IsStronglyConvex {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : H → ℝ) (δ : ℝ) : Prop :=
  0 < δ ∧ ∀ x y : H, ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    f (t • x + (1 - t) • y) ≤ t * f x + (1 - t) * f y -
      (δ / 2) * t * (1 - t) * ‖x - y‖ ^ 2

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
