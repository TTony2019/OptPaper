import Mathlib
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_1
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_3
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.algo_1
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.lem_2
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.lem_3
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.thm_1
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_def_6
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_thm_4

open Filter
open scoped Topology BigOperators

namespace BotCsetnek2015

open ERealFunction

/- The bridge is the external semialgebraic-to-KL result cited in the paper. -/
theorem semialgebraic_objective_yields_productKL_HFunction {m : ℕ}
    {P : ProblemData m} (A : AlgorithmData P) (nu mu : ℝ)
    (hsemi : IsSemiAlgebraicEReal P.objective)
    (hbridge : SemialgebraicToProductKL P.objective (A.M2 nu mu)) :
    ERealFunction.IsKLFunction (HFunctionL2 P (A.M2 nu mu)) := by
  simpa [HFunctionL2, objectiveWithQuadratic] using
    (semialgebraic_objective_yields_KL_H
      (g := P.objective) (M2 := A.M2 nu mu) hsemi hbridge)

/-
Corollary 3.1: convergence when the objective is coercive and semialgebraic.
The explicit `hsemi_to_KL` argument records the external semialgebraic-to-KL
theorem, which is not available in the local real-algebraic interface.
-/
theorem corollary_3_1_semialgebraic_convergence {m : ℕ} {P : ProblemData m}
    (A : AlgorithmData P) (nu mu : ℝ)
    (hchosen : chosenAsInLemma33 A nu mu)
    (hcoercive : CoerciveEReal P.objective)
    (hsemi : IsSemiAlgebraicEReal P.objective)
    (hsemi_to_KL : SemialgebraicToProductKL P.objective (A.M2 nu mu)) :
    Summable (fun n : ℕ ↦ ‖A.x n - A.p n‖) ∧
      Summable (fun n : ℕ ↦ ‖A.x (n + 1) - A.x n‖) ∧
      ∃ x : EuclideanSpace m,
        x ∈ limitingCriticalPoints P.objective ∧
          Tendsto A.x atTop (nhds x) ∧ Tendsto A.p atTop (nhds x) := by
  have hH_KL : ERealFunction.IsKLFunction (HFunctionL2 P (A.M2 nu mu)) :=
    semialgebraic_objective_yields_productKL_HFunction A nu mu hsemi hsemi_to_KL
  exact theorem_3_1_convergence A nu mu hchosen hcoercive hH_KL

end BotCsetnek2015
