import Mathlib
import TheoremLib.Baji_Cabot_An_Inertial_Proximal_Algorithm_with_Dry_Friction_2006.items.def_7

/-!
# Smooth convex set
A convex set $C \subset H$ is said to be smooth if it is smooth
at every point of its boundary.
-/
open Set
variable {H : Type _} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
/-- A convex set `C` is smooth if it is smooth at every point of its boundary. -/
def IsSmooth (C : Set H) : Prop :=
  Convex ℝ C ∧ ∀ x ∈ frontier C, IsSmoothAt C x
