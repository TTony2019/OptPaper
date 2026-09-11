import Foundation.SetValued.Basic

namespace BurachikSvaiterRobustnessHPE2001

/-- Pointwise Minkowski sum of two set-valued operators. -/
def setValuedSum {H : Type*} [AddCommMonoid H] (A B : SetValuedOperator H H) :
    SetValuedOperator H H :=
  fun x ↦ {w | ∃ a ∈ A x, ∃ b ∈ B x, w = a + b}

end BurachikSvaiterRobustnessHPE2001
