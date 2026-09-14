import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_2

open scoped InnerProductSpace

open ERealFunction

/-- Strong convexity with modulus `m`, in the subgradient form used in the paper. -/
def IsStronglyConvexWith {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (g : H → ℝ) (m : ℝ) : Prop :=
  ConvexOn ℝ Set.univ g ∧ 0 < m ∧ ∀ x z w, w ∈ subdifferential (fun y => (g y : EReal)) x →
    g z ≥ g x + inner ℝ w (z - x) + (m / 2) * ‖z - x‖ ^ 2
