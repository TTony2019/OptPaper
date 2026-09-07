import Mathlib
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.def_1

/-- The Hessian-driven TOGES-VH evolution equation. -/
def IsTOGESVH {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u uDot uDdot : ℝ → H) (grad : H → H) (hess : H → H → H) (alpha beta : ℝ) : Prop :=
  ∀ t : ℝ, t ≠ 0 →
    uDdot t + ((alpha + 7) / t) • uDdot t + (5 * (alpha + 1) / t ^ 2) • uDot t +
      beta • hess (u t + (t / 4) • uDot t) ((5 / 4 : ℝ) • uDot t + (t / 4) • uDdot t) +
      grad (u t + (t / 4) • uDot t) = 0
