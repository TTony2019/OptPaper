import Mathlib
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_1

namespace BotCsetnek2015

/-- Strong convexity with parameter `sigma`: `u - sigma/2 * ||.||^2` is convex. -/
def StronglyConvexWith {m : Nat} (sigma : Real) (u : EuclideanSpace m -> Real) : Prop :=
  0 < sigma ∧
    ConvexOn Real Set.univ (fun x : EuclideanSpace m => u x - (sigma / 2) * ‖x‖ ^ 2)

end BotCsetnek2015
