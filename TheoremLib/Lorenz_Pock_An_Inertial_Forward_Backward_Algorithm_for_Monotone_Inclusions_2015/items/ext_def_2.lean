import Mathlib
import Foundation.SetValued.Resolvent
import Foundation.Analysis.ExtendedRealFunctions
import Foundation.Convex.Subdifferential
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.ext_def_1

namespace LorenzPock

open scoped Pointwise

open ERealFunction

/-! The convex subdifferential (extended-real version) is supplied canonically by Foundation;
recalled here for paper-local use. -/
recall ERealFunction.subdifferential

/-- The variable-metric proximal relation `(Id + P⁻¹ ∂f)⁻¹`, represented using `Pinv`. -/
def proximalMap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (_hf_proper : ERealFunction.IsProper f)
    (_hf_convex : Convex ℝ (ERealFunction.epigraph f))
    (P : PositiveDefiniteMetric H) (Pinv : H →L[ℝ] H)
    (_hPinv : ∀ x, Pinv (P.toContinuousLinearMap x) = x) : SetValuedOperator H H :=
  J[((1 : ℝ) • (fun x ↦ Pinv '' subdifferential f x))]

end LorenzPock
