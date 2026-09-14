import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_4
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.thm_6
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.algo_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.rem_1
import Foundation.SetValued.Monotone

/-!
Remark 3.1 is a bibliographical comparison. Rockafellar's cited result proves
iterate convergence to a zero of a maximal monotone operator under criteria
A'/A and summable errors. In contrast, `inexact_proximal_converges` formalizes
the objective-value rate supplied here by Theorem 3.3.
-/
