import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_1
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.def_1

/-- The proximal objective `φ_k`. -/
noncomputable def proximalObjective {H : Type*} [NormedAddCommGroup H] (f : H → ℝ)
    (lam : ℝ) (y : H) (z : H) : ℝ := f z + ‖z - y‖ ^ 2 / (2 * lam)

/-- A point realizes the minimum value of a proximal objective. -/
def IsProximalMinimizer {H : Type*} [NormedAddCommGroup H] (f : H → ℝ)
    (lam : ℝ) (y p : H) : Prop := p ∈ proximalPoints f lam y
