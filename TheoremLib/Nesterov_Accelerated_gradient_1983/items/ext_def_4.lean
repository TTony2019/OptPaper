import Mathlib
import TheoremLib.Nesterov_Accelerated_gradient_1983.items.ext_def_2

open scoped InnerProductSpace

open ERealFunction

namespace Nesterov1983

/-- A saddle point of the minimax Lagrangian `⟪λ, fbar x⟫`. -/
def IsSaddlePoint {E U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    (F : U → ℝ) (fbar : E → U) (Q : Set E) (lstar : U) (xstar : E) : Prop :=
  lstar ∈ subdifferential (fun y => (F y : EReal)) 0 ∧ xstar ∈ Q ∧
    ∀ l ∈ subdifferential (fun y => (F y : EReal)) 0, ∀ x ∈ Q,
      inner ℝ l (fbar xstar) ≤ inner ℝ lstar (fbar xstar) ∧
        inner ℝ lstar (fbar xstar) ≤ inner ℝ lstar (fbar x)

end Nesterov1983
