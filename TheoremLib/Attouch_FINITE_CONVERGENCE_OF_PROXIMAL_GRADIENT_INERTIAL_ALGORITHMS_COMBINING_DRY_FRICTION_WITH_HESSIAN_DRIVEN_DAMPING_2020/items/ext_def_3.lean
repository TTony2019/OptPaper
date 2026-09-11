import TheoremLib.Attouch_FINITE_CONVERGENCE_OF_PROXIMAL_GRADIENT_INERTIAL_ALGORITHMS_COMBINING_DRY_FRICTION_WITH_HESSIAN_DRIVEN_DAMPING_2020.items.ext_def_1
import Foundation.Convex.ProximalOperator
import Foundation.Convex.Subdifferential

open scoped InnerProductSpace

open ERealFunction

/-! The convex subdifferential, the subgradient-form proximal optimality predicate
`IsProximalPoint`, the proximal points `IsProxPoint`, and the single-valued (scaled) proximity
operators are all supplied canonically by Foundation (`Foundation.Convex.Subdifferential` and
`Foundation.Convex.ProximalOperator`); rather than re-encoding them, they are recalled here for
paper-local use. -/
recall ERealFunction.subdifferential
recall IsProximalPoint
recall ERealFunction.proximalObjective
recall ERealFunction.proximalPoints
recall ERealFunction.IsProxPoint
recall ERealFunction.HasUniqueProxPoint
recall ERealFunction.proximityOperator
recall ERealFunction.scaledProximityOperator
