import Mathlib
import Foundation.Differentiation.Gateaux
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_1

namespace BotCsetnek2015

/--
A Frechet differentiable function has `L`-Lipschitz continuous gradient when
`L >= 0` and the displayed gradient inequality holds for all points.
-/
noncomputable def HasLipschitzContinuousGradient {m : Nat}
    (h : EuclideanSpace m -> Real) (L : Real) : Prop :=
  0 <= L ∧ Differentiable Real h ∧
    ∀ x y : EuclideanSpace m,
      ‖gradient h x - gradient h y‖ <= L * ‖x - y‖

end BotCsetnek2015
