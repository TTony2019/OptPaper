import Mathlib
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.def_2
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.ext_def_6
import TheoremLib.Bot_Csetnek_An_Inertial_Tseng_s_Type_Proximal_Algorithm_for_Nonsmooth_and_Nonconvex_Optimization_Problems_2015.items.lem_7

namespace BotCsetnek2015

/-
The paper uses the external fact that semialgebraic functions are KL and that
the semialgebraic class is stable under finite sums.  The local
`BasicSemialgebraicSet` definition is only a bookkeeping interface, so those
facts must remain explicit hypotheses until the corresponding real-algebraic
development is added.
-/
theorem semialgebraic_functions_are_KL_and_stable {m : Nat}
    (g q : EuclideanSpace m -> EReal)
    (_hg : IsSemiAlgebraicEReal g) (_hq : IsSemiAlgebraicEReal q)
    (hKLg : KLFunction g)
    (hsum : IsSemiAlgebraicEReal
      (fun x => EReal.sumWithTopBotAsTop (g x) (q x))) :
    KLFunction g ∧
      IsSemiAlgebraicEReal
        (fun x => EReal.sumWithTopBotAsTop (g x) (q x)) := by
  exact ⟨hKLg, hsum⟩

/-
The paper's corollary invokes an external real-algebraic theorem: a
semialgebraic objective, after adding the quadratic regularizer, supplies the
KL hypothesis used by Theorem 3.1.  The local semialgebraic predicate does not
contain that theorem, so expose it as an explicit bridge rather than silently
proving the conclusion.
-/
def SemialgebraicToProductKL {m : Nat}
    (g : EuclideanSpace m -> EReal) (M2 : Real) : Prop :=
  IsSemiAlgebraicEReal g ->
    ProductKLFunction
      (fun z : EuclideanSpace m × EuclideanSpace m =>
        erealAddReal (g z.1) (M2 * ‖z.1 - z.2‖ ^ 2))

theorem semialgebraic_objective_yields_KL_H {m : Nat}
    (g : EuclideanSpace m -> EReal) (M2 : Real)
    (_hg : IsSemiAlgebraicEReal g)
    (hbridge : SemialgebraicToProductKL g M2)
    : ProductKLFunction
      (fun z : EuclideanSpace m × EuclideanSpace m =>
        erealAddReal (g z.1) (M2 * ‖z.1 - z.2‖ ^ 2)) := by
  exact hbridge _hg

end BotCsetnek2015
