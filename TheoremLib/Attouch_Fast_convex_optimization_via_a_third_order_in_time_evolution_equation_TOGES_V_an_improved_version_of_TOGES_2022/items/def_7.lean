import Mathlib
import Foundation.SetValued.Resolvent
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.ext_def_3
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.ext_thm_5

open scoped InnerProductSpace
open scoped Pointwise

open ERealFunction

noncomputable section

/-- The Moreau envelope, defined as the infimum of the proximal objective. -/
def moreauEnvelope {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (lam : ℝ) (x : H) : EReal :=
  sInf (Set.range fun xi : H => f xi + ((1 / (2 * lam) * ‖x - xi‖ ^ 2 : ℝ) : EReal))

/-- A proximal mapping has positive index and realizes the Moreau minimum. -/
def IsProximalMapping {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (lam : ℝ) (prox : H → H)
    (hProper : ERealFunction.IsProper f) (hConvex : Convex ℝ (ERealFunction.epigraph f)) : Prop :=
  0 < lam ∧ ∀ x : H,
    f (prox x) + ((1 / (2 * lam) * ‖x - prox x‖ ^ 2 : ℝ) : EReal) = moreauEnvelope f lam x ∧
      (lam • subdifferential f).resolvent x = {prox x}
