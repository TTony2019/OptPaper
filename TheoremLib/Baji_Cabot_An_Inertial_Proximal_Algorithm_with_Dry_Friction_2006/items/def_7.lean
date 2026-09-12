import Mathlib
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.ext_def_3

/-!
# Smooth convex set at a point
A convex set $C \subset H$ is said to be smooth at a point $\overline{x} \in C$
if $N_C(\overline{x})$ is reduced to a half-line.
-/
open Set
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
/-- A convex set `C` is smooth at `xbar ∈ C` if the normal cone `N_C(xbar)`
is a half-line (i.e., of the form `{t • u | t ≥ 0}` for some nonzero `u`). -/
def IsSmoothAt (C : Set H) (xbar : H) : Prop :=
  xbar ∈ C ∧ ∃ (u : H), u ≠ 0 ∧ normalCone C xbar = {v | ∃ (t : ℝ), t ≥ 0 ∧ v = t • u}
