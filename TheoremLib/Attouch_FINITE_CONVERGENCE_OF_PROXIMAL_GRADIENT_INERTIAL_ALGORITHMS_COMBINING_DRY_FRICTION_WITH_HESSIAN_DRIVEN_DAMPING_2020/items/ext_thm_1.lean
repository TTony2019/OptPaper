import Foundation.Differentiation.MoreauGradient
import Foundation.Convex.Subdifferential

open scoped InnerProductSpace

/-! Foundation already supplies the regularity of the Moreau envelope in
`Foundation/Differentiation/MoreauGradient.lean`: the real-valued `γ`-Moreau envelope
`x ↦ ({}^[γ] f x).toReal` is differentiable with gradient the scaled proximal residual
`γ⁻¹ • (x - Prox_{γ f} x)`, that gradient is `γ⁻¹`-Lipschitz, and the (scaled) proximity operator
is firmly nonexpansive with residual in the subdifferential.  Rather than re-derive these facts
from an abstract proximal mapping, they are recalled here for paper-local use. -/
recall ERealFunction.moreauEnvelope_toReal_hasGradientAt_of_mem_gammaZero
recall ERealFunction.gradient_moreauEnvelope_toReal_eq_inv_smul_sub_scaledProximityOperator_of_mem_gammaZero
recall ERealFunction.lipschitzWith_inv_of_gradient_moreauEnvelope_toReal_of_mem_gammaZero
recall ERealFunction.proximityOperator_isProxPoint
recall ERealFunction.eq_proximityOperator_of_isProxPoint
recall ERealFunction.proximityOperator_firmlyNonexpansive_of_mem_gammaZero
recall ERealFunction.scaledProximityOperator_residual_mem
recall ERealFunction.eq_proximityOperator_iff_sub_mem_subdifferential
