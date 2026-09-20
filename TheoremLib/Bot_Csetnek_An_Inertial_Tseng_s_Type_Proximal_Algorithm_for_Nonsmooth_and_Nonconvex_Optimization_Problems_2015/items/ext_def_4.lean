import Mathlib
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_1

namespace BotCsetnek2015

/-- The argmin set of an extended-real-valued function over the whole Euclidean space. -/
noncomputable def argminSet {m : ℕ} (G : EuclideanSpace m → EReal) :
    Set (EuclideanSpace m) :=
  {p | G p = sInf (Set.range G)}

/-- Membership in `argminSet` gives the minimizer inequality against every competitor. -/
theorem mem_argminSet_iff {m : ℕ} (G : EuclideanSpace m → EReal)
    (p : EuclideanSpace m) :
    p ∈ argminSet G ↔ G p = sInf (Set.range G) := Iff.rfl

end BotCsetnek2015
