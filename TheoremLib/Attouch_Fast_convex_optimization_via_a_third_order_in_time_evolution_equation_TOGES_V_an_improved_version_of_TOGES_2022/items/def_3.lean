import Mathlib
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.def_1

/-- The second-derivative-driven TOGES-VH evolution equation. -/
def IsTOGESVH {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [InnerProductSpace ℝ H] [CompleteSpace H]
  (u : ℝ → H) (alpha beta : ℝ) (f : H → ℝ) (t0 : ℝ) : Prop :=
  ∀ t : ℝ, t ≥ t0 →
    deriv (deriv (deriv u)) t + ((alpha + 7) / t) • deriv (deriv u) t +
    (5 * (alpha + 1) / t ^ 2) • (deriv u) t +
    beta • fderiv ℝ (gradient f) (u t + (t / 4) • (deriv u) t) ((5 / 4 : ℝ) • (deriv u) t
      + (t / 4) • deriv (deriv u) t) + gradient f (u t + (t / 4) • (deriv u) t) = 0
