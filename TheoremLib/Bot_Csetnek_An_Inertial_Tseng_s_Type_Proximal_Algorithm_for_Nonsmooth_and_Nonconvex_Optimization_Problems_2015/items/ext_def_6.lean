import Mathlib
import Foundation.Analysis.ExtendedRealFunctions
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_1

namespace BotCsetnek2015

/-
Basic semialgebraic sets are an external real-algebraic notion.  Keep the
predicate opaque until the corresponding polynomial-geometry development is
available; a `True` field would incorrectly make every set semialgebraic.
-/
opaque BasicSemialgebraicSet {m : ℕ} (s : Set (EuclideanSpace m × ℝ)) : Prop

/--
An extended-real-valued function is semialgebraic when its real-height epigraph
is a finite union of basic semialgebraic sets.
-/
def IsSemiAlgebraicEReal {m : ℕ} (g : EuclideanSpace m → EReal) : Prop :=
  ∃ pieces : Finset (Set (EuclideanSpace m × ℝ)),
    (∀ s, s ∈ pieces → BasicSemialgebraicSet s) ∧
      ERealFunction.epigraph g = {p | ∃ s, s ∈ pieces ∧ p ∈ s}

end BotCsetnek2015
