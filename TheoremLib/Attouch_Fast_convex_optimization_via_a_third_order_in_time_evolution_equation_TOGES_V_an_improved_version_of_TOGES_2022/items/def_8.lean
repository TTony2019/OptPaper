import Mathlib
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.def_1
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.def_7
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.ext_thm_5

/-- The Moreau-regularized TOGES-VR evolution equation. -/
def IsTOGESVR {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (lam : ℝ) (prox : H → H) (u : ℝ → H)
    (alpha t0 : ℝ) (hProper : ERealFunction.IsProper f)
    (hConvex : Convex ℝ (ERealFunction.epigraph f)) : Prop :=
  0 < lam ∧ IsProximalMapping f lam prox hProper hConvex ∧
  (∀ x : H, gradient (fun y => (moreauEnvelope f lam y).toReal) x =
    (1 / lam) • (x - prox x)) ∧
  ∀ t : ℝ, t0 ≤ t → t ≠ 0 →
    deriv (deriv (deriv u)) t + ((alpha + 7) / t) • deriv (deriv u) t +
      (5 * (alpha + 1) / t ^ 2) • deriv u t +
      gradient (fun y => (moreauEnvelope f lam y).toReal)
        (u t + (t / 4) • deriv u t) = 0
