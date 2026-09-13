import Mathlib
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.def_3
import TheoremLib.Lorenz_Pock_An_Inertial_Forward_Backward_Algorithm_for_Monotone_Inclusions_2015.items.ext_def_2

namespace LorenzPock

open ERealFunction

/-- The preconditioned inertial primal--dual scheme (30). -/
structure PreconditionedInertialPrimalDualIteration (X Y : Type*) [NormedAddCommGroup X]
    [InnerProductSpace ℝ X] [CompleteSpace X] [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y]
    (G : X → EReal) (FStar : Y → EReal) (K : X →L[ℝ] Y) (T : X →L[ℝ] X) (Sigma : Y →L[ℝ] Y)
    (gradQ : X → X) (gradPStar : Y → Y) (α : ℕ → ℝ) where
  x : ℕ → X
  y : ℕ → Y
  ξ : ℕ → X
  ζ : ℕ → Y
  barξ : ℕ → X
  extrapolate_primal : ∀ k, ξ k = x k + α k • (x k - x (k - 1))
  extrapolate_dual : ∀ k, ζ k = y k + α k • (y k - y (k - 1))
  -- `x^{k+1} = (Id + T ∂G)^{-1}(ξ^k - T(∇Q(ξ^k) + K*ζ^k))`, in inclusion form; the
  -- preconditioner `T` acts on the whole gradient expression, as in (30)
  primal_update : ∀ k, ∃ g ∈ subdifferential G (x (k + 1)),
    ξ k - T (gradQ (ξ k) + K.adjoint (ζ k)) = x (k + 1) + T g
  reflected_primal : ∀ k, barξ (k + 1) = 2 • x (k + 1) - ξ k
  dual_update : ∀ k, ∃ f ∈ subdifferential FStar (y (k + 1)),
    ζ k - Sigma (gradPStar (ζ k) - K (barξ (k + 1))) = y (k + 1) + Sigma f

end LorenzPock
