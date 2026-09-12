import Mathlib
import Foundation.Differentiation.ODE

open MeasureTheory

namespace Attouch_AitMansour_Mazgouri_Monotone_stability_2024

/-- A function x:[0,b]→H is absolutely continuous if it is continuous and its
  distributional derivative is Lebesgue integrable on [0,b]. -/
def IsAbsolutelyContinuous {H : Type*} [NormedAddCommGroup H] (x : ℝ → H) (b : ℝ) : Prop :=
  AbsolutelyContinuousOnInterval x 0 b

/-- A function x:[0,+∞)→H and its derivative ẋ are locally absolutely continuous
  if for every T>0 they are absolutely continuous on [0,T].  Supplied canonically
  by Foundation (definitionally `IsAbsolutelyContinuous`-unfolded). -/
recall IsLocallyAbsolutelyContinuous

/-- Definition 2.3: a strong global solution of `S(A,u₀,v₀)`.

The trajectories are represented as total functions on `ℝ`, but every
almost-everywhere condition is restricted to the forward half-line.  The two
derivative clauses ensure that the supplied functions `dx` and `ddx` really
are the first and second derivatives occurring in the paper. -/
def def_3 {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (A : H → H) (γ : ℝ) (u₀ v₀ : H) (x dx ddx : ℝ → H) : Prop :=
  IsLocallyAbsolutelyContinuous x dx ∧
    x 0 = u₀ ∧
    dx 0 = v₀ ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ici 0)), HasDerivAt x (dx t) t) ∧
    (∀ᵐ t ∂(volume.restrict (Set.Ici 0)), HasDerivAt dx (ddx t) t) ∧
    ∀ᵐ t ∂(volume.restrict (Set.Ici 0)), ddx t + γ • dx t + A (x t) = 0

end Attouch_AitMansour_Mazgouri_Monotone_stability_2024
