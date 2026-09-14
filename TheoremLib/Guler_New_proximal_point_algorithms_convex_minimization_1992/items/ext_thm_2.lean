import Mathlib.Tactic
import TheoremLib.Guler_New_proximal_point_algorithms_convex_minimization_1992.items.ext_def_5

open scoped InnerProductSpace

open ERealFunction

/-- The subgradient inequality for a strongly convex function. -/
theorem stronglyConvex_subgradient_inequality {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (g : H → ℝ) {m : ℝ} (hg : IsStronglyConvexWith g m)
    {x z w : H} (hw : w ∈ subdifferential (fun y => (g y : EReal)) x) :
    g z ≥ g x + inner ℝ w (z - x) + (m / 2) * ‖z - x‖ ^ 2 := by
  rcases hg with ⟨hconvex, hm_pos, hsubgrad⟩
  exact hsubgrad x z w hw
