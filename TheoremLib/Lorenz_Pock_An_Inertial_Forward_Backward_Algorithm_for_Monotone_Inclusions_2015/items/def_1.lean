import Mathlib
import Foundation.SetValued.Monotone
import Foundation.FixedPoint.Nonexpansive
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.ext_def_1

namespace LorenzPock

/-- Equation (9) of the paper: `B` is co-coercive with respect to the inverse metric
`Linv = L⁻¹`, *on the solution set* `S = (A + B)⁻¹(0)`:

`⟪B x - B y, x - y⟫ ≥ ‖B x - B y‖²_{L⁻¹} = ⟪Linv (B x - B y), B x - B y⟫`
for every `x : H` and every `y ∈ S`.

The paper restricts the second argument to `S`; the theorems below consume exactly this
restricted form (the energy estimate is applied at `(y^k, x^*)` with `x^* ∈ S`). -/
def IsCocoerciveWithInverseMetric {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (B : H → H) (Linv : H →L[ℝ] H) (S : Set H) : Prop :=
  ∀ x : H, ∀ y ∈ S,
    inner ℝ (Linv (B x - B y)) (B x - B y) ≤ inner ℝ (B x - B y) (x - y)

end LorenzPock
