import Mathlib
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.ext_def_4

/-!
# Interior characterization via support function
Let $C \subset H$ be a convex set. Then $0 \in \operatorname{int}(C)$ if
and only if there exists $\alpha > 0$ such that $\sigma_C(x) \geqslant \alpha |x|$
for all $x \in H$.
Cited from: classical result in convex analysis
(see e.g. R.T. Rockafellar, Convex Analysis, Princeton University Press, 1970).
-/
open Set
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
/-- For a convex set `C`, `0 ∈ int(C)` iff there exists `α > 0` such that
`σ_C(x) ≥ α ‖x‖` for all `x`. -/
theorem interior_zero_iff_supportFunction (C : Set H) (hC : Convex ℝ C) :
    (0 ∈ interior C) ↔
      ∃ (α : ℝ), α > 0 ∧ ∀ x, supportFunction C x ≥ ((α * ‖x‖ : ℝ) : EReal) := by
  sorry
