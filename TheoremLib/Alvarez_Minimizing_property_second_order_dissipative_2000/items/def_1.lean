import Foundation.Differentiation.Gateaux

namespace Alvarez2000

open scoped InnerProductSpace

/-- A classical solution of the scalar-damped system `(E_gamma; u0, v0)`. -/
structure DissipativeSystem {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H]
    (gamma : ℝ) (Phi : H → ℝ) (gradPhi : H → H) (u0 v0 : H) where
  gamma_pos : 0 < gamma
  is_gradient : ∀ x : H, HasGradientAt Phi (gradPhi x) x
  u : ℝ → H
  contDiff : ContDiffOn ℝ 2 u (Set.Ici 0)
  initial_position : u 0 = u0
  initial_velocity : fderiv ℝ u 0 1 = v0
  equation : ∀ t ∈ Set.Ici (0 : ℝ),
    fderiv ℝ (fun s => fderiv ℝ u s 1) t 1 + gamma • fderiv ℝ u t 1 + gradPhi (u t) = 0

end Alvarez2000
