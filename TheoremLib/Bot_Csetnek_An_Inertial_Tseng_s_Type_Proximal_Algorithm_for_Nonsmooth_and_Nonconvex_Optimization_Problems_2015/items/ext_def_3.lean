import Mathlib
import Foundation.Analysis.ExtendedRealFunctions
import Foundation.Analysis.Semicontinuity
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_1

namespace BotCsetnek2015

/--
Coercivity for extended-real-valued functions, in the finite-dimensional
equivalent form used in the paper: every real lower level set is bounded.
-/
def CoerciveEReal {m : Nat} (g : EuclideanSpace m -> EReal) : Prop :=
  ∀ c : Real, Bornology.IsBounded (ERealFunction.lowerLevelSet g c)

end BotCsetnek2015
