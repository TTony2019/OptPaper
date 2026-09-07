import Foundation.Operator.Linear

namespace Alvarez2000

open scoped InnerProductSpace

/-- A positive quadratic potential induced by a bounded self-adjoint positive operator. -/
structure PositiveQuadraticPotential {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] (A : H →L[ℝ] H) where
  self_adjoint : IsSelfAdjoint A
  positive : ∀ x : H, 0 ≤ ⟪A x, x⟫_ℝ

noncomputable def PositiveQuadraticPotential.potential {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] [CompleteSpace H] {A : H →L[ℝ] H}
    (_ : PositiveQuadraticPotential A) (x : H) : ℝ :=
  (1 / 2 : ℝ) * ⟪A x, x⟫_ℝ

end Alvarez2000
