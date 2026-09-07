import Mathlib
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.def_5

noncomputable section

/-- The Lyapunov energy used for the strongly convex evolution. -/
def stronglyConvexLyapunov {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (u uDot uDdot : ℝ → H) (xStar : H) (mu t : ℝ)
    (_hxStar : ∀ x : H, f xStar ≤ f x ∧ (f x = f xStar → x = xStar)) : ℝ :=
  f (u t + (Real.sqrt mu)⁻¹ • uDot t) - sInf (Set.range f) +
    (1 / 2 : ℝ) * ‖Real.sqrt mu • (u t + (Real.sqrt mu)⁻¹ • uDot t - xStar) +
      uDot t + (Real.sqrt mu)⁻¹ • uDdot t‖ ^ 2

def initialObjectiveGap {H : Type*} (f : H → ℝ) (u : ℝ → H) (_xStar : H) (t0 : ℝ) : ℝ :=
  f (u t0) - sInf (Set.range f)

def stronglyConvexEnergyConstant {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (f : H → ℝ) (u uDot uDdot : ℝ → H) (xStar : H) (mu t0 : ℝ)
    (hxStar : ∀ x : H, f xStar ≤ f x ∧ (f x = f xStar → x = xStar)) : ℝ :=
  stronglyConvexLyapunov f u uDot uDdot xStar mu t0 hxStar * Real.exp (Real.sqrt mu * t0)
