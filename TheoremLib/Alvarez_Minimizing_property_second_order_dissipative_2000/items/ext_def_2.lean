import Mathlib

namespace Alvarez2000

/-- The set of minimizers of a bounded-below extended-real function. -/
def argmin {H : Type*} {R : Type*} [ConditionallyCompleteLattice R] (F : H → R)
    (_hBoundedBelow : BddBelow (Set.range F)) : Set H :=
  {x | F x = sInf (Set.range F)}

end Alvarez2000
