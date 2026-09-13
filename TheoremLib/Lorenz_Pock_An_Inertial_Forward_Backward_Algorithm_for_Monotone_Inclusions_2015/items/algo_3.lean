import Mathlib
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.def_3
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.def_4
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.ext_def_2

namespace LorenzPock

/-- Iterates of the inertial primal--dual forward--backward scheme (21). -/
structure InertialPrimalDualIteration (X Y : Type*) [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y]
    (gradQ : X → X) (gradPStar : Y → Y) (K : X →L[ℝ] Y)
    (subG : SetValuedOperator X X) (subFStar : SetValuedOperator Y Y)
    (α : ℕ → ℝ) (τ σ : ℝ) where
  x : ℕ → X
  ξ : ℕ → X
  dual : ℕ → Y
  dualExtrapolated : ℕ → Y
  ξ_eq : ∀ k, ξ k = x k + α k • (x k - x (k - 1))
  ζ_eq : ∀ k, dualExtrapolated k = dual k + α k • (dual k - dual (k - 1))
  primal_step : ∀ k, ∃ g ∈ subG (x (k + 1)),
    ξ k - τ • (gradQ (ξ k) + K.adjoint (dualExtrapolated k)) - x (k + 1) = τ • g
  dual_step : ∀ k, ∃ f ∈ subFStar (dual (k + 1)),
    dualExtrapolated k - σ • (gradPStar (dualExtrapolated k) - K (2 • x (k + 1) - ξ k)) - dual (k + 1) = σ • f

end LorenzPock
