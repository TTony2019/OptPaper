import Mathlib
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.def_1
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.def_7
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.ext_thm_5

/-- The Moreau-regularized TOGES-VR evolution equation. -/
def IsTOGESVR {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → EReal) (lam : ℝ) (prox : H → H) (u uDot uDdot : ℝ → H) (gradEnvelope : H → H)
    (alpha t0 : ℝ) (hProper : ERealFunction.IsProper f)
    (hConvex : Convex ℝ (ERealFunction.epigraph f)) : Prop :=
  0 < lam ∧ IsProximalMapping f lam prox hProper hConvex ∧
  (∀ x : H, gradEnvelope x = (1 / lam) • (x - prox x)) ∧
  ∀ t : ℝ, t0 ≤ t → t ≠ 0 →
    uDdot t + ((alpha + 7) / t) • uDdot t + (5 * (alpha + 1) / t ^ 2) • uDot t +
      gradEnvelope (u t + (t / 4) • uDot t) = 0
