import Mathlib
import Foundation.Analysis.ExtendedRealFunctions

namespace AttouchPeypouquetRedont2014

/-- A function whose norm-bounded lower level sets are strongly relatively compact. -/
def IsBoundedlyInfCompact {H : Type*} [NormedAddCommGroup H]
    (f : H → EReal) : Prop :=
  ∀ r R : ℝ, 0 < R → IsCompact (closure {v | f v ≤ (r : EReal) ∧ ‖v‖ ≤ R})

end AttouchPeypouquetRedont2014
