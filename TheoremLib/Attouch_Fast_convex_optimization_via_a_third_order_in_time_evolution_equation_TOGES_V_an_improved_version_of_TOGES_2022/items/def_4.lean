import Mathlib
import TheoremLib.Attouch_Fast_convex_optimization_via_a_third_order_in_time_evolution_equation_TOGES_V_an_improved_version_of_TOGES_2022.items.def_3

noncomputable section

/-- The auxiliary trajectory v in the Lyapunov construction. -/
def togesVAuxiliary {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u uDot : ℝ → H) (t : ℝ) : H := u t + (t / 4) • uDot t

/-- The coefficient delta in the Lyapunov construction. -/
def togesVDelta (beta t : ℝ) : ℝ := t ^ 2 * (1 - 2 * beta / t)

/-- The vector w in the Lyapunov construction. -/
def togesVLyapunovVector {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u uDot uDdot : ℝ → H) (grad : H → H) (z : H) (alpha beta t : ℝ) : H :=
  t ^ 2 • (uDdot t + beta • grad (togesVAuxiliary u uDot t)) +
    ((alpha + 5) * t) • uDot t + (4 * alpha) • (u t - z)

/-- The Lyapunov function E of equations (8)--(12). -/
def togesVLyapunov {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (f : H → ℝ) (u uDot uDdot : ℝ → H) (grad : H → H) (z : H) (alpha beta t : ℝ) : ℝ :=
  4 * t * togesVDelta beta t * (f (togesVAuxiliary u uDot t) - sInf (Set.range f)) +
    (1 / 2 : ℝ) * ‖togesVLyapunovVector u uDot uDdot grad z alpha beta t‖ ^ 2
