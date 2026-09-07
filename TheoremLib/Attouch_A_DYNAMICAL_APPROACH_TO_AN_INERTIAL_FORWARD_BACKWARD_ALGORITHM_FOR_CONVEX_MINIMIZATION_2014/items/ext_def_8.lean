import Mathlib

namespace AttouchPeypouquetRedont2014

/-- Distance from a point to a set. -/
noncomputable def distanceToSet {H : Type*} [PseudoMetricSpace H] (x : H) (C : Set H) : EReal :=
  sInf (Set.range fun v : C ↦ (dist x v : EReal))

end AttouchPeypouquetRedont2014
