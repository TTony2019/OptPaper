import Mathlib

namespace Alvarez2000

/-- A function is even when its value is invariant under negation. -/
def IsEvenFunction {H : Type*} [Neg H] (Phi : H → ℝ) : Prop :=
  ∀ x : H, Phi (-x) = Phi x

end Alvarez2000
