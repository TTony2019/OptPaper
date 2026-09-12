import Mathlib
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.def_1

/-!
# Excess of a set over another
Given subsets $A, B \subset H$, the excess of $A$ over $B$ is
$e(A, B) = \sup_{x \in A} d(x, B)$.
-/
open Set
variable {H : Type _} [NormedAddCommGroup H]
/-- The excess of set `A` over set `B`: `e(A, B) = sup_{x ∈ A} d(x, B)`. -/
noncomputable def excess (A B : Set H) : ℝ := ⨆ x ∈ A, Metric.infDist x B
